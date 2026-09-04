;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.predall-test
  "The predAll / predExists / predInstance / predSpecified matrix (docs/predall.md,
  resources/kb/CxCore.txt).

  The *Instance* relations (predAllInstance / predInstanceAll) are rule generators that do
  REAL inference: every member of the quantified collection is concluded to bear the
  predicate to the fixed filler, and the conclusion retracts and belief-follows like any
  derived fact.

  The *Exists* relations (predAllExists / predExistsAll / predExistsInstance /
  predInstanceExists) are inferentially INERT: each declaration is a stored, queryable
  record beside a sanctioned per-cell full-arg placeholder functor an author may use for
  the unnamed filler.  The engine derives nothing — no skolem witness, no defn, no rule
  (Pace, \"skolems suck\").

  The *Specified* relations (predAllSpecified / predSpecifiedAll) are an integrity AUDIT
  that reports the instances with no *determinate* filler.  Indeterminate = a member of the
  extensible `indeterminate_term` category (skolem is its built-in first member), so an
  author-asserted *Exists* placeholder passes and a skolemised witness does not — the
  exact antagonist of the *Exists* class.  The same category drives the UNA identity
  exemption: the unique-name assumption is suspended for an unpinned indeterminate term.

  The tracer is predAllInstance on Pace's `sign` / `-212` example.  The generator's
  stamped rule (defeasible, direction `:both` — `set/defaultRule`'s default) fires on a
  believed membership, and its backward arm closes the keystone: bare-literal membership
  derives (the evaluative defnSufficient provers, #59) and is discharged inside a
  query/prove proof (`pred-all-instance-keystone-proves-from-the-bare-literal`).  `ask`
  answers the same goal false by contract — the registry expands no rule."
  (:require [clojure.test :refer [is use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.predall :as predall]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (core-context/load-into))))

(defn- believes?
  "Is `sentence` a believed, stored sentex in `ctx`?  Read through `sentexes-matching`,
  which is belief-sensitive, rather than through `ask`."
  [kb sentence ctx]
  (boolean (seq (v/sentexes-matching kb sentence ctx))))

;; ==== the -212 subtlety, isolated ==========================================
;; Pace named -212 the keystone: (sign -212 "negative") should be provable from the BARE
;; literal, with membership DERIVED, not hand-asserted.  Both halves hold: membership
;; derives via the evaluative defnSufficient prover (#59), and the stamped defaultRule's
;; backward arm discharges that antecedent inside a query/prove proof — see
;; pred-all-instance-keystone-proves-from-the-bare-literal.  The one instrument caveat:
;; `ask` expands no rule by contract, so the ask-mode answer is false by design, not gap.

(tu/deftest-kb minus-212-membership-is-derived
  ;; #59 closed the membership half of the keystone: bare-literal membership now derives,
  ;; no hand-assert needed.
  (is (v/ask? kb '(negative_integer -212) 'CxUniverse)
      "negative_integer membership of a bare literal derives via defnSufficient (#59)")
  (is (v/ask? kb '(integer -212) 'CxUniverse)
      "and integer membership too — now query-time evaluatable"))

;; ==== Instance class: real inference =======================================

(tu/deftest-kb pred-all-instance-mechanism-fires-on-a-believed-membership
  ;; the generator's stamped defaultRule (bidirectional), on Pace's sign/-212 predicates:
  ;; once (negative_integer -212) is believed — here asserted directly, exercising the
  ;; forward arm on its own; the keystone test below covers the backward, query-time
  ;; path — the rule concludes (sign -212 "negative") and binds the fixed position.
  (v/assert kb '(binary_predicate sign) 'CxUniverse)
  (v/assert kb '(predAllInstance sign negative_integer "negative") 'CxUniverse)
  (v/assert kb '(negative_integer -212) 'CxUniverse)
  (is (v/ask? kb '(sign -212 "negative") 'CxUniverse)
      "every negative_integer is signed \"negative\", so -212 is")
  (is (= #{"negative"} (into #{} (map '?x) (v/ask kb '(sign -212 ?x) 'CxUniverse)))
      "and querying the fixed position binds it to the filler"))

(tu/deftest-kb pred-all-instance-keystone-proves-from-the-bare-literal
  ;; THE KEYSTONE, closed: with no hand-asserted membership, the stamped rule's backward
  ;; arm discharges (negative_integer -212) through the evaluative defnSufficient prover
  ;; at query time, so the acceptance criterion holds from the bare literal.  Under `ask`
  ;; the same goal answers false BY CONTRACT — level 6 is the registry and expands no
  ;; rule (docs/levels.md) — so the pair below pins both the capability and the
  ;; instrument distinction that once hid it.
  (v/assert kb '(binary_predicate sign) 'CxUniverse)
  (v/assert kb '(predAllInstance sign negative_integer "negative") 'CxUniverse)
  (is (v/query? kb '(sign -212 "negative") 'CxUniverse {:max-depth 5})
      "provable from the bare literal — membership derives inside the proof")
  (is (= [{'?x "negative"}] (vec (v/query kb '(sign -212 ?x) 'CxUniverse {:max-depth 5})))
      "and querying the fixed position binds it")
  (is (not (v/query? kb '(sign -212 "positive") 'CxUniverse {:max-depth 5}))
      "negative control: the wrong filler is not provable")
  (is (not (v/ask? kb '(sign -212 "negative") 'CxUniverse))
      "ask answers false by contract — the registry expands no rule; use query/prove"))

(tu/deftest-kb pred-all-instance-on-a-kind-without-a-defn
  ;; Pace: also cover a kind whose membership is asserted directly, not derived through a
  ;; defnNecessary/defnSufficient expansion.  A gensym'd type has no defn at all.
  (tu/with-terms [color widget Blueish W1]
    (v/assert kb (list 'binary_predicate color) 'CxUniverse)
    (v/assert kb (list 'unary_predicate widget) 'CxUniverse)
    (v/assert kb (list 'predAllInstance color widget Blueish) 'CxUniverse)
    (is (not (believes? kb (list color W1 Blueish) 'CxUniverse))
        "with no member yet, nothing is concluded")
    (v/assert kb (list widget W1) 'CxUniverse)
    (is (believes? kb (list color W1 Blueish) 'CxUniverse)
        "a directly-asserted member fires the stamped rule")))

(tu/deftest-kb pred-all-instance-retracts-and-belief-follows
  (tu/with-terms [color widget Blueish W1]
    (v/assert kb (list 'binary_predicate color) 'CxUniverse)
    (v/assert kb (list 'unary_predicate widget) 'CxUniverse)
    (let [dh (v/assert kb (list 'predAllInstance color widget Blueish) 'CxUniverse)]
      (v/assert kb (list widget W1) 'CxUniverse)
      (is (believes? kb (list color W1 Blueish) 'CxUniverse))
      (v/retract! kb dh)
      (is (not (believes? kb (list color W1 Blueish) 'CxUniverse))
          "retracting the declaration withdraws the stamped rule and its conclusion"))))

(tu/deftest-kb pred-instance-all-is-the-argument-swapped-twin
  ;; the fixed filler bears ?pred to every member of the collection, at position 2
  (tu/with-terms [enjoys Alice hobby Chess Sudoku]
    (v/assert kb (list 'binary_predicate enjoys) 'CxUniverse)
    (v/assert kb (list 'unary_predicate hobby) 'CxUniverse)
    (v/assert kb (list 'predInstanceAll enjoys Alice hobby) 'CxUniverse)
    (v/assert kb (list hobby Chess) 'CxUniverse)
    (v/assert kb (list hobby Sudoku) 'CxUniverse)
    (is (= #{Chess Sudoku} (into #{} (map '?y) (v/ask kb (list enjoys Alice '?y) 'CxUniverse)))
        "Alice enjoys every hobby")))

;; ==== Exists class: pure record, inferentially inert =======================
;; Pace's ruling (2026-09-03): everything with "exist" in the name is inferentially
;; inert — a stored, queryable record plus a sanctioned per-cell placeholder functor
;; for authors, and the engine derives NOTHING.  This supersedes the earlier generator
;; design that materialized (?pred ?x P) over the members; inertness is also what makes
;; the two pure-existential cross-cells expressible (nothing to stamp, so no range
;; restriction to fail and no variable-functor rule to pollute the planner with).

(tu/deftest-kb an-exists-declaration-is-a-record-and-derives-nothing
  (tu/with-terms [owns person dog Alice]
    (v/assert kb (list 'binary_predicate owns) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate dog) 'CxUniverse)
    (v/assert kb (list 'predAllExists owns person dog) 'CxUniverse)
    (v/assert kb (list person Alice) 'CxUniverse)
    (is (v/ask? kb (list 'predAllExists owns person dog) 'CxUniverse)
        "the declaration is stored and queryable like any fact")
    (is (empty? (into #{} (map '?y) (v/ask kb (list owns Alice '?y) 'CxUniverse)))
        "and no filler is concluded for any member — inferentially inert")
    (is (empty? (into #{} (map '?y) (v/ask kb (list dog '?y) 'CxUniverse)))
        "no placeholder membership is materialized either")))

(tu/deftest-kb all-four-exists-cells-are-inert-records
  ;; the straight cells and the pure-existential cross-cells are uniform under inertness:
  ;; four declarations stored, zero facts derived
  (tu/with-terms [rel person dog Alice Rome]
    (v/assert kb (list 'binary_predicate rel) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate dog) 'CxUniverse)
    (v/assert kb (list 'predAllExists rel person dog) 'CxUniverse)
    (v/assert kb (list 'predExistsAll rel dog person) 'CxUniverse)
    (v/assert kb (list 'predExistsInstance rel person Rome) 'CxUniverse)
    (v/assert kb (list 'predInstanceExists rel Rome dog) 'CxUniverse)
    (v/assert kb (list person Alice) 'CxUniverse)
    (is (v/ask? kb (list 'predExistsInstance rel person Rome) 'CxUniverse)
        "a pure-existential cross-cell is storable and queryable")
    (is (v/ask? kb (list 'predInstanceExists rel Rome dog) 'CxUniverse)
        "and its argument-swapped twin")
    (is (empty? (into [] (v/ask kb (list rel '?x '?y) 'CxUniverse)))
        "none of the four declarations concludes a single fact of the subject predicate")))

(tu/deftest-kb a-placeholder-is-sanctioned-vocabulary-the-author-asserts
  ;; the per-cell full-arg functor is the author's term for the unnamed filler: usable in
  ;; hand-asserted sentences, structural (unreifiable), and distinct per cell — the
  ;; predAllExists and predExistsAll placeholders over the same (rel, dog) are two terms,
  ;; not one shared filler (Pace, "eventually it will matter that they're distinct")
  (tu/with-terms [rel person dog Alice]
    (v/assert kb (list 'binary_predicate rel) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate dog) 'CxUniverse)
    (v/assert kb (list 'predAllExists rel person dog) 'CxUniverse)
    (v/assert kb (list 'predExistsAll rel dog person) 'CxUniverse)
    (v/assert kb (list person Alice) 'CxUniverse)
    (let [p1 (list 'PredAllExistsFn rel person dog)
          p2 (list 'PredExistsAllFn rel dog person)]
      (v/assert kb (list dog p1) 'CxUniverse)
      (v/assert kb (list dog p2) 'CxUniverse)
      (v/assert kb (list rel Alice p1) 'CxUniverse)
      (is (v/ask? kb (list rel Alice p1) 'CxUniverse)
          "an author-asserted sentence naming the placeholder is believed like any fact")
      (let [fillers (into #{} (map '?y) (v/ask kb (list rel Alice '?y) 'CxUniverse))]
        (is (= 1 (count fillers)) "and answers as a filler")
        (is (not (v/reified-term? (first fillers)))
            "staying a structural NAT — unreifiable, readable inside the sentence"))
      (is (= 2 (count (into #{} (map '?y) (v/ask kb (list dog '?y) 'CxUniverse))))
          "the two cells' placeholders are two distinct dog members, not one shared term"))))

;; The aspirational existential-inference test (Pace, 2026-08-29 — KEEP, do NOT delete).
;; Under pure-record inert semantics nothing at all is derivable from the declaration,
;; so no existential filler for `(parts Lain ?x)` is provable.  That is the expected
;; outcome and it is pinned here as a standing marker for future existential-inference
;; work rather than as a passing feature.
;;
;; Cyc taught us that skolems suck, so we're not prioritizing this line of inference
(tu/deftest-kb exists-inference-from-a-predAllExists-is-not-yet-supported
  (tu/with-terms [parts construct llm Lain]
    (v/assert kb (list 'binary_predicate parts) 'CxUniverse)
    (v/assert kb (list 'unary_predicate construct) 'CxUniverse)
    (v/assert kb (list 'unary_predicate llm) 'CxUniverse)
    (v/assert kb (list 'predAllExists parts construct llm) 'CxUniverse)
    (is (not (v/ask? kb (list 'thereExists '?x
                              (list 'and (list llm '?x) (list parts Lain '?x)))
                     'CxUniverse))
        "no existential llm part of Lain is derivable from the inert record — pending")))

;; ==== Specified class: an integrity audit ==================================

(tu/deftest-kb pred-all-specified-reports-instances-with-no-determinate-filler
  ;; binary form: the required filler type is DERIVED from hasPet's own slot-2 contract
  ;; ((arg hasPet 2 pet)), never restated in the declaration.
  (tu/with-terms [hasPet person pet Alice Bob Carol Rex]
    (v/assert kb (list 'binary_predicate hasPet) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate pet) 'CxUniverse)
    (v/assert kb (list 'arg hasPet 2 pet) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified hasPet person) 'CxUniverse)
    (v/assert kb (list person Alice) 'CxUniverse)   ; a determinate filler
    (v/assert kb (list person Bob) 'CxUniverse)     ; no filler at all
    (v/assert kb (list person Carol) 'CxUniverse)   ; a filler of unknown type
    (v/assert kb (list hasPet Alice Rex) 'CxUniverse)
    (v/assert kb (list pet Rex) 'CxUniverse)
    (tu/with-terms [NotAPet]
      (v/assert kb (list hasPet Carol NotAPet) 'CxUniverse))
    (let [vs (:violations (predall/specified-violations kb hasPet person 'CxUniverse))]
      (is (not (contains? vs Alice)) "Alice has a determinate pet")
      (is (contains? vs Bob) "Bob has no filler at all")
      ;; Carol PASSES, and the pass is the design: the audit's membership question is
      ;; answered by the KB's own reading, and with (arg hasPet 2 pet) visible,
      ;; argument-type inference types her stored filler off that very declaration.
      ;; An audit stricter than the contract it derives from would be the second type
      ;; system the binary form exists to remove; the conformance bite lives at the
      ;; assert-time checker (which refuses a filler it can convict) and on the
      ;; kind-position arms tested below.
      (is (not (contains? vs Carol))
          "a stored filler is typed by the slot contract itself — no second type system"))))

(tu/deftest-kb a-ternary-pred-all-specified-is-refused
  ;; the old three-place spelling is gone, not tolerated: predAllSpecified is a
  ;; binary_predicate and the arity classifications are pairwise disjoint, so the
  ;; ternary form fails WFF at assert instead of quietly storing a second type system.
  (tu/with-terms [hasPet person pet]
    (v/assert kb (list 'binary_predicate hasPet) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate pet) 'CxUniverse)
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list 'predAllSpecified hasPet person pet) 'CxUniverse))
        "the retired ternary spelling is refused at assert")))

(tu/deftest-kb a-declaration-without-slot-typing-is-a-reported-gap
  ;; missing slot typing is an explicit declaration-contract diagnostic, never a silent
  ;; unconstrained audit: an untyped pred's declaration reports {:gap …}, and the sweep
  ;; carries the gap where a clean sweep would omit the declaration.
  (tu/with-terms [likes person Alice Bob]
    (v/assert kb (list 'binary_predicate likes) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified likes person) 'CxUniverse)
    (v/assert kb (list person Alice) 'CxUniverse)
    (v/assert kb (list likes Alice Bob) 'CxUniverse)
    (let [r (predall/specified-violations kb likes person 'CxUniverse)]
      (is (= :missing-slot-typing (:gap r)) "the gap is named, not absorbed")
      (is (= 2 (:position r)) "and carries the audited position")
      (is (nil? (:violations r)) "no violation set pretends the audit ran"))
    (is (= {:gap :missing-slot-typing :pred likes :position 2}
           (get (predall/all-specified-violations kb 'CxUniverse)
                ['predAllSpecified likes person]))
        "the sweep reports the gap — it can never pass as a clean declaration")))

(tu/deftest-kb a-genlarg-typed-slot-audits-the-subtype-arm
  ;; the derived contract has two arms: (arg p 2 t) asks membership, (genlArg p 2 t)
  ;; asks subtypehood — the same split the assert-time checker runs.  A filler that is
  ;; itself the constraint type passes reflexively (no genl self-edge is stored).
  (tu/with-terms [governs meta_kind kind_a lone_individual]
    (v/assert kb (list 'binary_predicate governs) 'CxUniverse)
    (v/assert kb (list 'unary_predicate meta_kind) 'CxUniverse)
    (v/assert kb (list 'unary_predicate kind_a) 'CxUniverse)
    (v/assert kb (list 'genlArg governs 2 'thing) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified governs meta_kind) 'CxUniverse)
    (tu/with-terms [M1 M2 M3]
      (v/assert kb (list meta_kind M1) 'CxUniverse)
      (v/assert kb (list meta_kind M2) 'CxUniverse)
      (v/assert kb (list meta_kind M3) 'CxUniverse)
      (v/assert kb (list 'genl kind_a 'thing) 'CxUniverse)
      (v/assert kb (list governs M1 kind_a) 'CxUniverse)      ; a kind under thing — passes
      (v/assert kb (list governs M2 'thing) 'CxUniverse)      ; the type itself — reflexive pass
      (v/assert kb (list governs M3 lone_individual) 'CxUniverse) ; no genl path to thing
      (let [vs (:violations (predall/specified-violations kb governs meta_kind 'CxUniverse))]
        (is (not (contains? vs M1)) "a filler with a genl path to the constraint type passes")
        (is (not (contains? vs M2)) "the constraint type itself passes reflexively")
        (is (contains? vs M3) "a filler with no visible path into the hierarchy violates")))))

(tu/deftest-kb multiple-slot-constraints-compose-conjunctively
  ;; two visible slot-2 constraints must BOTH be satisfied.  The division of labour the
  ;; comment in `satisfies-typing?` describes shows up concretely here: a filler with
  ;; visible evidence reaching the WRONG constraint is refused at assert by the checker
  ;; (composition enforced at the entry point — there is no storable
  ;; passes-one-fails-the-other case), so what the audit's conjunction meets on stored
  ;; facts is the checker's open-world excuse: a filler with NO visible evidence stores
  ;; fine and violates both derived constraints, and one under both passes.
  (tu/with-terms [governs meta_kind vehicle_kind insured_kind car_kind mystery_kind M1 M2]
    (v/assert kb (list 'binary_predicate governs) 'CxUniverse)
    (v/assert kb (list 'unary_predicate meta_kind) 'CxUniverse)
    (v/assert kb (list 'unary_predicate vehicle_kind) 'CxUniverse)
    (v/assert kb (list 'unary_predicate insured_kind) 'CxUniverse)
    (v/assert kb (list 'genl vehicle_kind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl insured_kind 'thing) 'CxUniverse)
    (v/assert kb (list 'genlArg governs 2 vehicle_kind) 'CxUniverse)
    (v/assert kb (list 'genlArg governs 2 insured_kind) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified governs meta_kind) 'CxUniverse)
    (v/assert kb (list meta_kind M1) 'CxUniverse)
    (v/assert kb (list meta_kind M2) 'CxUniverse)
    (v/assert kb (list 'genl car_kind vehicle_kind) 'CxUniverse)
    (v/assert kb (list 'genl car_kind insured_kind) 'CxUniverse)  ; under both
    (v/assert kb (list governs M1 car_kind) 'CxUniverse)
    (v/assert kb (list governs M2 mystery_kind) 'CxUniverse)      ; no visible evidence
    ;; the partially-conforming case is unstorable, which is itself worth pinning:
    (tu/with-terms [boat_kind M3]
      (v/assert kb (list meta_kind M3) 'CxUniverse)
      (v/assert kb (list 'genl boat_kind vehicle_kind) 'CxUniverse)
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list governs M3 boat_kind) 'CxUniverse))
          "a filler visibly under one constraint and not the other is refused at assert"))
    (let [vs (:violations (predall/specified-violations kb governs meta_kind 'CxUniverse))]
      (is (not (contains? vs M1)) "car_kind satisfies both subtype constraints")
      (is (contains? vs M2)
          "an evidence-free filler the checker excused fails the audit's conjunction"))))

(tu/deftest-kb argn-bridges-project-arg-in-both-directions
  ;; the binary projections: (arg1 p t) concludes (arg p 1 t) and conversely, so either
  ;; spelling is assertable and both are believed — which is what lets a positional
  ;; constraint stand in a binary declaration's subject position.
  (tu/with-terms [rel kind_a kind_b]
    (v/assert kb (list 'binary_predicate rel) 'CxUniverse)
    (v/assert kb (list 'unary_predicate kind_a) 'CxUniverse)
    (v/assert kb (list 'unary_predicate kind_b) 'CxUniverse)
    (v/assert kb (list 'arg1 rel kind_a) 'CxUniverse)
    (is (v/ask? kb (list 'arg rel 1 kind_a) 'CxUniverse)
        "the binary spelling concludes the ternary one")
    (v/assert kb (list 'arg rel 2 kind_b) 'CxUniverse)
    (is (v/ask? kb (list 'arg2 rel kind_b) 'CxUniverse)
        "and the ternary spelling concludes the binary one")))

(tu/deftest-kb pred-all-specified-treats-a-skolem-filler-as-indeterminate
  ;; the crux: a filler minted by head-existential skolemization is INDETERMINATE, so the
  ;; instance it fills still violates the requirement — Specified is the antagonist of the
  ;; existential
  (tu/with-terms [hasPet person pet Alice]
    (v/assert kb (list 'binary_predicate hasPet) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate pet) 'CxUniverse)
    ;; skolemize a pet witness for every person, so Alice HAS a filler — an indeterminate
    ;; one
    (v/assert kb (list 'implies (list person '?x)
                       (list 'exists '?y (list 'and (list hasPet '?x '?y) (list pet '?y))))
              'CxUniverse)
    (v/assert kb (list 'arg hasPet 2 pet) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified hasPet person) 'CxUniverse)
    (v/assert kb (list person Alice) 'CxUniverse)
    (let [filler (get (first (v/ask kb (list hasPet Alice '?y) 'CxUniverse)) '?y)]
      (is (some? filler) "Alice does have a skolem filler")
      (is (predall/indeterminate-term? kb filler 'CxUniverse)
          "which is an indeterminate (skolem) term"))
    (is (contains? (:violations (predall/specified-violations kb hasPet person 'CxUniverse))
                   Alice)
        "so Alice still violates predAllSpecified — a skolem filler is not determinate")))

(tu/deftest-kb pred-all-specified-honours-an-extensible-indeterminate-kind
  ;; the category is extensible, not hard-wired to skolems: a filler that is a member of a
  ;; NEW kind declared (genl NewKind indeterminate_term) is indeterminate too, so it does
  ;; not satisfy the requirement — the audit reads the category, not the SkolemFn shape.
  (tu/with-terms [hasPet person pet Alice Fuzzy vague_kind]
    (v/assert kb (list 'binary_predicate hasPet) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate pet) 'CxUniverse)
    (v/assert kb (list 'genl vague_kind 'indeterminate_term) 'CxUniverse)  ; a future indeterminate kind
    (v/assert kb (list 'arg hasPet 2 pet) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified hasPet person) 'CxUniverse)
    (v/assert kb (list person Alice) 'CxUniverse)
    (v/assert kb (list hasPet Alice Fuzzy) 'CxUniverse)
    (v/assert kb (list pet Fuzzy) 'CxUniverse)     ; Fuzzy satisfies the derived slot type
    (v/assert kb (list vague_kind Fuzzy) 'CxUniverse)   ; but it is an indeterminate_term member
    (is (predall/indeterminate-term? kb Fuzzy 'CxUniverse)
        "a member of a (genl _ indeterminate_term) kind is indeterminate")
    (is (contains? (:violations (predall/specified-violations kb hasPet person 'CxUniverse))
                   Alice)
        "so Alice's only filler is indeterminate and she violates the requirement")))

(tu/deftest-kb an-exists-placeholder-satisfies-the-specified-requirement
  ;; the antagonism from the other side: the *Exists* placeholder is DETERMINATE — an
  ;; author who asserts it as a filler passes the predAllSpecified audit, where a skolem
  ;; witness (an indeterminate_term) would not.  Under pure-record semantics the
  ;; assertion is the author's, so the test makes it by hand.
  (tu/with-terms [owns person dog Alice]
    (v/assert kb (list 'binary_predicate owns) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate dog) 'CxUniverse)
    (v/assert kb (list 'predAllExists owns person dog) 'CxUniverse)
    (v/assert kb (list 'arg owns 2 dog) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified owns person) 'CxUniverse)
    (v/assert kb (list person Alice) 'CxUniverse)
    (let [p (list 'PredAllExistsFn owns person dog)]
      (v/assert kb (list dog p) 'CxUniverse)
      (v/assert kb (list owns Alice p) 'CxUniverse))
    (is (empty? (:violations (predall/specified-violations kb owns person 'CxUniverse)))
        "the author-asserted placeholder is a determinate filler, so nothing violates")))

(tu/deftest-kb pred-specified-all-audits-the-first-position
  ;; the argument-swapped twin: the filler sits at ?pred's first position
  (tu/with-terms [managedBy report manager Carol Dan Boss]
    (v/assert kb (list 'binary_predicate managedBy) 'CxUniverse)
    (v/assert kb (list 'unary_predicate report) 'CxUniverse)
    (v/assert kb (list 'unary_predicate manager) 'CxUniverse)
    ;; binary twin: (predSpecifiedAll ?pred ?indep) — quantified over ?indep at ?pred's
    ;; second position, filler audited at position 1 under the slot-1 derived contract
    (v/assert kb (list 'arg managedBy 1 manager) 'CxUniverse)
    (v/assert kb (list 'predSpecifiedAll managedBy report) 'CxUniverse)
    (v/assert kb (list report Carol) 'CxUniverse)
    (v/assert kb (list report Dan) 'CxUniverse)
    (v/assert kb (list managedBy Boss Carol) 'CxUniverse)  ; Boss manages Carol
    (v/assert kb (list manager Boss) 'CxUniverse)
    (let [vs (:violations
              (predall/specified-violations kb managedBy report 'CxUniverse :first))]
      (is (not (contains? vs Carol)) "Carol has a determinate manager")
      (is (contains? vs Dan) "Dan has none"))))

(tu/deftest-kb all-specified-violations-sweeps-every-declaration
  (tu/with-terms [hasPet person pet Bob]
    (v/assert kb (list 'binary_predicate hasPet) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate pet) 'CxUniverse)
    (v/assert kb (list 'arg hasPet 2 pet) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified hasPet person) 'CxUniverse)
    (v/assert kb (list person Bob) 'CxUniverse)
    (let [report (predall/all-specified-violations kb 'CxUniverse)]
      (is (contains? report ['predAllSpecified hasPet person])
          "the sweep names the violated declaration")
      (is (contains? (:violations (get report ['predAllSpecified hasPet person])) Bob)
          "and carries its violating instances"))))

;; ==== the acceptance fixture: Pace's KE packet, normalized ================
;; The declarations from the 2026-09-04 predAllSpecified KE packet that survived the
;; thread's rulings, normalized to the binary (pred, collection) form.  Parked lines are
;; deliberately absent: the at_least_* collections (await the arity vocabulary lane), the
;; all-functions fcp audit (known unreifiable noise), and the arityMin family (its own
;; vocabulary-only PR).  What is pinned here is that each surviving declaration is
;; assertable against the shipped core vocabulary and audits — deriving a real slot
;; contract, not a gap.

(tu/deftest-kb the-ke-packet-declarations-assert-and-audit-over-core
  (doseq [[pred indep] [['arg1    'predicate]        ; every relation types argument 1
                        ['result  'function]         ; every function types its result
                        ['comment 'thing]            ; everything is documented
                        ['genl    'unary_predicate]] ; every type has a place in the hierarchy
          :let [_ (v/assert kb (list 'predAllSpecified pred indep) 'CxUniverse)
                r (predall/specified-violations kb pred indep 'CxUniverse)]]
    (is (nil? (:gap r))
        (str "(predAllSpecified " pred " " indep ") derives a slot contract — "
             pred "'s filler typing is visible to the audit"))
    (is (set? (:violations r))
        (str "and the audit over " indep " runs to a violation set")))
  ;; genl's slot 2 carries no arg/genlArg declaration on purpose (the root would fail
  ;; it); its contract arrives through the type_relation_predicate arm, which is the
  ;; specific reading this fixture exists to pin.
  (is (v/ask? kb '(type_relation_predicate genl) 'CxUniverse)
      "the arm the genl declaration audits through is a believed membership"))

;; ==== the IndeterminateTerm identity exemption + the UNA matrix ============
;; The unique-name assumption applies to DETERMINATE terms (distinct names are provably
;; different, a term is never different from itself) but is SUSPENDED for an unpinned
;; indeterminate_term: neither equals nor different is provable of it against a determinate
;; term until a merge pins it.  Built data-driven over the grid rather than N hand-written
;; cases (Pace, "DRY it").
;;
;; FLAGGED for a future ruling: (1) the design notes also want a non-evaluatable
;; *unreifiable* NAT (MotherFn JFK) treated as indeterminate; that rests on the
;; NAT-determinacy question explicitly PUNTED ("for now only skolem is a
;; member; flag the NAT call"), so the category here is skolem + whatever is declared
;; (genl _ indeterminate_term), and the generic-NAT cell is left to that ruling.  (2)
;; rewriteOf-pinning restores UNA for a skolem (below), but for an explicitly-declared
;; indeterminate kind the equality merge MIGRATES the kind membership onto the winner, so
;; the winner inherits the indeterminacy — pin-restoration for that row needs a
;; merge-surviving pin signal (a Pace design call).

(defn- a-skolem
  "Skolemize a witness through a head-existential rule and return the minted skolem
  constant — the built-in first member of indeterminate_term."
  [kb]
  (tu/with-terms [wk pk hasP T1]
    (v/assert kb (list 'binary_predicate hasP) 'CxUniverse)
    (v/assert kb (list 'unary_predicate wk) 'CxUniverse)
    (v/assert kb (list 'unary_predicate pk) 'CxUniverse)
    (v/assert kb (list 'implies (list wk '?x)
                       (list 'exists '?y (list 'and (list hasP '?x '?y) (list pk '?y))))
              'CxUniverse)
    (v/assert kb (list wk T1) 'CxUniverse)
    (get (first (v/ask kb (list hasP T1 '?y) 'CxUniverse)) '?y)))

(tu/deftest-kb una-applies-to-distinct-determinate-terms
  ;; every atomic determinate term-type pair is provably different; none is different from
  ;; itself — the UNA baseline the exemption is carved out of.
  (tu/with-terms [Alice Bob]
    (doseq [[a b] [[Alice Bob]     ; symbol × symbol (individuals)
                   [1 2]           ; number × number
                   ["x" "y"]       ; string × string
                   [1 "x"]         ; number × string (cross-kind)
                   [Alice 1]]]     ; symbol × number
      (is (v/ask? kb (list 'different a b) 'CxUniverse)
          (str "UNA: " (pr-str a) " and " (pr-str b) " are provably different"))
      (is (not (v/ask? kb (list 'different a a) 'CxUniverse))
          (str "reflexive: " (pr-str a) " is not different from itself")))))

(tu/deftest-kb una-is-suspended-for-unpinned-indeterminate-terms
  ;; all three ways into the category — the built-in skolem, a declared kind, and a
  ;; DIRECT membership — are exempt.  The direct case is the regression pin: the prover's
  ;; cheap gate once required a declared subkind to exist before it would look, so a
  ;; direct member's exemption appeared and disappeared with an unrelated (genl _
  ;; indeterminate_term) declaration, and the audit and the prover disagreed about the
  ;; same term.  Tested in ITS OWN kb-shape (no subkind declared) below.
  (tu/with-terms [Other Foggy vague_kind]
    (v/assert kb (list 'genl vague_kind 'indeterminate_term) 'CxUniverse)
    (v/assert kb (list vague_kind Foggy) 'CxUniverse)
    (doseq [[label t] [["skolem (built-in member)" (a-skolem kb)]
                       ["declared (genl _ indeterminate_term) kind" Foggy]]]
      (is (predall/indeterminate-term? kb t 'CxUniverse)
          (str label " is an indeterminate term"))
      (is (not (v/ask? kb (list 'different t Other) 'CxUniverse))
          (str label ": UNA suspended — not provably different from a determinate term")))))

(tu/deftest-kb a-direct-indeterminate-member-is-exempt-with-no-subkind-declared
  ;; the regression shape: NO (genl _ indeterminate_term) declaration anywhere, only a
  ;; direct membership.  The audit and the prover must agree.
  (tu/with-terms [Other Hazy]
    (v/assert kb (list 'indeterminate_term Hazy) 'CxUniverse)
    (is (predall/indeterminate-term? kb Hazy 'CxUniverse)
        "the audit sees the direct membership")
    (is (not (v/ask? kb (list 'different Hazy Other) 'CxUniverse))
        "and so does the different prover — no subkind declaration required")))

(tu/deftest-kb a-rewriteOf-pins-a-skolem-and-restores-una
  ;; a merge that gives the skolem a determinate identity lifts the exemption for it.
  (tu/with-terms [Real Other]
    (let [sk (a-skolem kb)]
      (is (not (v/ask? kb (list 'different sk Other) 'CxUniverse)) "unpinned: exempt")
      (v/assert kb (list 'rewriteOf Real sk) 'CxUniverse)          ; pin sk -> Real
      (is (v/ask? kb (list 'different sk Other) 'CxUniverse)
          (str "once pinned by rewriteOf, the SKOLEM itself obeys the UNA — its"
               " representative has moved off it, which is the exemption's lifting"
               " condition"))
      (is (v/ask? kb (list 'different Real Other) 'CxUniverse)
          "control: the determinate pin target was never exempt"))))

(tu/deftest-kb negative-zero-permutations-are-canonicalized
  ;; Pace's Cyc-canonicalizer check: -0.0 must not be a distinct term from 0.0 (the
  ;; Allegro bug).  Honest scope note: (= 0.0 -0.0) is true in Clojure, so the -0.0 rows
  ;; are settled by =-level canonicalization before the equality closure is ever
  ;; consulted — this pins the reader-and-equality layer, not a closure read.  (An
  ;; integer -0 literal reads as 0 and is pure reflexivity, so it is not a row.)
  (doseq [[a b una?] [[0.0 -0.0 false]   ; same magnitude+kind: NOT different (no -0.0 bug)
                      [0   0.0  true]    ; integer 0 vs float 0.0: distinct EDN kinds
                      [0.0  1.0 true]]]  ; ordinary distinct floats
    (is (= una? (v/ask? kb (list 'different a b) 'CxUniverse))
        (str "(different " (pr-str a) " " (pr-str b) ") is " una?)))
  (is (v/ask? kb '(different 0.0 1.0 2.0) 'CxUniverse)
      "variable-arity control: three genuinely distinct floats are pairwise different")
  (is (not (v/ask? kb '(different 0.0 -0.0 1.0) 'CxUniverse))
      (str "-0.0 collapses onto 0.0, so this tuple carries a repeat and is NOT pairwise"
           " different — the canonicalization visible through the variable-arity read")))

(tu/deftest-kb a-rule-concluding-indeterminacy-from-a-different-antecedent-is-refused
  ;; `different` is negation as failure over TWO things now: the equality closure, and the
  ;; `indeterminate_term` category the exemption reads.  A rule that concludes the second
  ;; from a `different` antecedent is a cycle through negation — it withdraws the
  ;; antecedent that derived it — so the stratification check refuses it, exactly as it
  ;; already refuses one concluding an equality.  Stored, the pair settles to a belief that
  ;; contradicts its own support: `(indeterminate_term Aa)` believed off a `(different Aa
  ;; Bb)` that the belief then makes false.
  (tu/with-terms [pRel]
    (v/assert kb (list 'binary_predicate pRel) 'CxUniverse)
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list 'implies (list 'and (list pRel '?x '?y)
                                                   (list 'different '?x '?y))
                                    (list 'indeterminate_term '?x))
                           'CxUniverse))
        "concluding indeterminacy from a difference is not stratified")
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb (list 'implies (list 'and (list pRel '?x '?y)
                                                   (list 'different '?x '?y))
                                    (list 'genl '?x 'indeterminate_term))
                           'CxUniverse))
        "and neither is minting a subkind of it — the genl edge withdraws the same way")))

(tu/deftest-kb the-audit-and-the-prover-cannot-disagree-about-a-term
  ;; ONE implementation, called from both sides.  Two copies split on a membership no fact
  ;; states: `(arg pointsAt 2 vague_kind)` makes `(vague_kind Hazy)`
  ;; answerable by argument-type inference, which `ask` runs and a stored-sentex read does
  ;; not.  Either answer is defensible; disagreeing is not, because the audit would call a
  ;; filler indeterminate while `different` treated it as a determinate name.
  (tu/with-terms [pointsAt Src Hazy Other vague_kind]
    (v/assert kb (list 'genl vague_kind 'indeterminate_term) 'CxUniverse)
    (v/assert kb (list 'binary_predicate pointsAt) 'CxUniverse)
    (v/assert kb (list 'arg pointsAt 2 vague_kind) 'CxUniverse)
    (v/assert kb (list pointsAt Src Hazy) 'CxUniverse)
    (is (v/ask? kb (list vague_kind Hazy) 'CxUniverse)
        "the membership is answerable by argument-type inference")
    (let [audit-says     (predall/indeterminate-term? kb Hazy 'CxUniverse)
          una-suspended? (not (v/ask? kb (list 'different Hazy Other) 'CxUniverse))]
      (is (= audit-says una-suspended?)
          "the audit and the different prover give one answer, whichever it is")
      (is (false? audit-says)
          (str "and the answer is that the category is what the KB HOLDS — a stored"
               " membership or a genl edge into it — not what a prover can infer"
               " on demand at query time")))))

(tu/deftest-kb the-audit-runs-through-the-public-api
  ;; the declarations in CxCore send an author to `vaelii.core`, so the audit answers there
  ;; without a caller requiring anything under `vaelii.impl`.  `predall` sits ABOVE core and
  ;; the delegation runs back down through `wiring`, which is the arrangement being pinned:
  ;; a broken resolve there fails at call time rather than at load.
  (tu/with-terms [hasPet person pet Alice Bob Rex]
    (v/assert kb (list 'binary_predicate hasPet) 'CxUniverse)
    (v/assert kb (list 'unary_predicate person) 'CxUniverse)
    (v/assert kb (list 'unary_predicate pet) 'CxUniverse)
    (v/assert kb (list 'arg hasPet 2 pet) 'CxUniverse)
    (v/assert kb (list 'predAllSpecified hasPet person) 'CxUniverse)
    (v/assert kb (list person Alice) 'CxUniverse)
    (v/assert kb (list person Bob) 'CxUniverse)
    (v/assert kb (list pet Rex) 'CxUniverse)
    (v/assert kb (list hasPet Alice Rex) 'CxUniverse)
    (is (= {:violations #{Bob}} (v/specified-violations kb hasPet person 'CxUniverse))
        "Alice has a determinate pet; Bob has no filler at all")
    (is (= {:violations #{Bob}}
           (v/specified-violations kb hasPet person 'CxUniverse :second))
        "and :second is the default argument position, stated or not")
    (let [report (v/all-specified-violations kb 'CxUniverse)]
      (is (= {['predAllSpecified hasPet person] {:violations #{Bob}}} report)
          "the sweep reports the one declaration that does not hold, keyed by it"))
    (v/assert kb (list hasPet Bob Rex) 'CxUniverse)
    (is (= {} (v/all-specified-violations kb 'CxUniverse))
        "and a requirement that holds is omitted, so a clean sweep is an empty map")))

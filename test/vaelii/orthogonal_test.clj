;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.orthogonal-test
  "`(orthogonal A B)`: the two types may overlap — something could be an instance of both —
  and neither is a subtype of the other.  It does not say that anything is an instance of
  both, and claims nothing about things that are instances of neither.  The declared spelling of the `:orthogonal` subsumption status."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.clashes :as clashes]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded tu/load-starter!))
(use-fixtures :each (tu/neutral))

;; `true?` around each read, so a failure prints the answer rather than the KB.

;; ---- the declaration ------------------------------------------------------

(tu/deftest-kb orthogonal-is-a-declared-term-of-the-grammar
  (is (some? (v/interpreted 'orthogonal))
      "CxCore declares orthogonal, and the vocabulary roster answers for it")
  (is (true? (v/ask? kb '(binary_predicate orthogonal))))
  (is (true? (v/ask? kb '(symmetric orthogonal))))
  (is (true? (v/ask? kb '(type_relation_predicate orthogonal)))))

(tu/deftest-kb its-length-is-checked-by-its-own-arm-not-a-stated-class
  ;; `symmetric` and `type_relation_predicate` are each `genl binary_predicate`, so the
  ;; class is answered without stating it, and the well-formedness arm, which reads the
  ;; sentence alone, refuses any other length.
  (is (empty? (v/sentexes-matching kb '(binary_predicate orthogonal) '?ctx))
      "no (binary_predicate orthogonal) is stated")
  (is (true? (v/ask? kb '(binary_predicate orthogonal))))
  (is (= 2 (:arity (v/describe kb 'orthogonal))))
  (tu/with-terms [alphaKind betaKind gammaKind]
    (doseq [t ['alphaKind 'betaKind 'gammaKind]]
      (v/assert kb (list 'genl t 'thing) 'CxUniverse))
    (doseq [s [(list 'orthogonal 'alphaKind 'betaKind 'gammaKind) (list 'orthogonal 'alphaKind)]]
      (is (= :not-well-formed
             (try (v/assert kb s 'CxUniverse) :ok
                  (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))
          (str (pr-str s) " is refused")))))

(tu/deftest-kb orthogonal-is-symmetric
  (tu/with-terms [spatialKind temporalKind]
    (v/assert kb (list 'genl 'spatialKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'temporalKind 'thing) 'CxUniverse)
    (v/assert kb (list 'orthogonal 'temporalKind 'spatialKind) 'CxUniverse)
    (is (true? (v/ask? kb (list 'orthogonal 'spatialKind 'temporalKind) 'CxUniverse))
        "either spelling answers the one stored declaration")
    (is (true? (v/ask? kb (list 'orthogonal 'temporalKind 'spatialKind) 'CxUniverse)))))

;; ---- the subsumption status -------------------------------------------------

(tu/deftest-kb a-declared-pair-is-orthogonal-without-a-shared-instance
  (tu/with-terms [spatialKind temporalKind]
    (v/assert kb (list 'genl 'spatialKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'temporalKind 'thing) 'CxUniverse)
    (is (= :unknown (v/subsumption-status kb 'spatialKind 'temporalKind))
        "no relation and no shared instance yet")
    (v/assert kb (list 'orthogonal 'temporalKind 'spatialKind) 'CxUniverse)
    (is (= #{:orthogonal} (v/subsumption-statuses kb 'spatialKind 'temporalKind))
        "the declaration is the witness, whichever order it was written in")
    (is (= :orthogonal (v/subsumption-status kb 'temporalKind 'spatialKind)))))

(tu/deftest-kb a-declaration-a-narrower-context-holds-is-read-from-that-vantage
  (tu/with-terms [spatialKind temporalKind]
    (let [cx (tu/tmp-ctx)]
      (v/assert kb (list 'genlCx cx 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genl 'spatialKind 'thing) 'CxUniverse)
      (v/assert kb (list 'genl 'temporalKind 'thing) 'CxUniverse)
      (v/assert kb (list 'orthogonal 'spatialKind 'temporalKind) cx)
      (is (= :unknown (v/subsumption-status kb 'spatialKind 'temporalKind))
          "CxUniverse does not see a declaration stated below it")
      (is (= :orthogonal (v/subsumption-status kb 'spatialKind 'temporalKind cx))))))

(tu/deftest-kb a-declared-pair-that-is-also-genl-related-is-inconsistent
  (tu/with-terms [alphaKind betaKind]
    (v/assert kb (list 'genl 'alphaKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'betaKind 'alphaKind) 'CxUniverse)
    (v/assert kb (list 'orthogonal 'alphaKind 'betaKind) 'CxUniverse {:strength :monotonic})
    (is (= #{:spec :orthogonal} (v/subsumption-statuses kb 'alphaKind 'betaKind)))
    (is (= :inconsistent (v/subsumption-status kb 'alphaKind 'betaKind)))))

(tu/deftest-kb a-declared-pair-under-a-separated-pair-is-inconsistent
  ;; overlap propagates upward: two subtypes that could share an instance put it in both
  ;; separated supertypes, so the declaration does not exempt the pair it names
  (tu/with-terms [upperA upperB subA subB]
    (v/assert kb (list 'genl 'upperA 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'upperB 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'subA 'upperA) 'CxUniverse)
    (v/assert kb (list 'genl 'subB 'upperB) 'CxUniverse)
    (v/assert kb (list 'disjoint 'upperA 'upperB) 'CxUniverse)
    (v/assert kb (list 'orthogonal 'subA 'subB) 'CxUniverse)
    (is (= #{:disjoint :orthogonal} (v/subsumption-statuses kb 'subA 'subB)))
    (is (= :inconsistent (v/subsumption-status kb 'subB 'subA)))))

(tu/deftest-kb the-separation-and-the-declaration-are-read-from-one-vantage
  (tu/with-terms [alphakind betakind]
    (let [cx (tu/tmp-ctx)]
      (v/assert kb (list 'genlCx cx 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genl alphakind 'thing) 'CxUniverse)
      (v/assert kb (list 'genl betakind 'thing) 'CxUniverse)
      (v/assert kb (list 'disjoint alphakind betakind) 'CxUniverse)
      (v/assert kb (list 'orthogonal alphakind betakind) cx)
      (is (= #{:disjoint} (v/subsumption-statuses kb alphakind betakind))
          "CxUniverse reads the disjoint and not the declaration below it")
      (is (= #{:orthogonal} (v/subsumption-statuses kb alphakind betakind cx))))))

(tu/deftest-kb the-audit-counts-a-declared-pair-as-known
  (tu/with-terms [spatialKind temporalKind]
    (v/assert kb (list 'genl 'spatialKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'temporalKind 'thing) 'CxUniverse)
    (let [row (fn [] (first (filter #(= #{'spatialKind 'temporalKind} (hash-set (:a %) (:b %)))
                                    (:pairs-data (v/disjointness-audit kb)))))
          before (row)]
      (is (= :unknown (:status before)))
      (v/assert kb (list 'orthogonal 'spatialKind 'temporalKind) 'CxUniverse)
      (is (= :orthogonal (:status (row)))
          "a declared pair leaves the audit's unknown candidates"))))

;; ---- the clash: a possible overlap stated over a subsumed pair -----------------
;;
;; A `disjoint` over two `genl`-related types is a one-member hard clash of the
;; declaration (docs/nmtms.md, "Declarations over related types"), stored and reported by
;; `conflicts` rather than refused.  An `orthogonal` over two `genl`-related types, over
;; one type twice, or over two subtypes of a pair still separated is the same family's
;; clash, of the `orthogonal` declaration.

(defn- clashes
  "The member sentence sets of the `:orthogonal` clashes `conflicts` lists."
  [kb]
  (into #{} (comp (filter #(= :orthogonal (:kind %)))
                  (map (fn [r] (into #{} (map :sentence) (:sides r)))))
        (v/conflicts kb)))

(tu/deftest-kb a-consistent-declaration-is-no-clash
  (tu/with-terms [spatialKind temporalKind]
    (v/assert kb (list 'genl 'spatialKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'temporalKind 'thing) 'CxUniverse)
    (v/assert kb (list 'orthogonal 'spatialKind 'temporalKind) 'CxUniverse {:strength :monotonic})
    (is (= #{} (clashes kb)))))

(tu/deftest-kb an-orthogonal-over-a-genl-related-pair-is-a-clash-in-either-order
  (tu/with-terms [alphaKind betaKind]
    (v/assert kb (list 'genl 'alphaKind 'thing) 'CxUniverse)
    (let [orth (list 'orthogonal 'alphaKind 'betaKind)]
      (testing "the edge first"
        (let [e (v/assert kb (list 'genl 'betaKind 'alphaKind) 'CxUniverse)
              o (v/assert kb orth 'CxUniverse {:strength :monotonic})]
          (is (= #{#{orth}} (clashes kb)))
          (v/retract! kb o)
          (v/retract! kb e)))
      (testing "the orthogonal first"
        (v/assert kb (list 'genl 'betaKind 'thing) 'CxUniverse)
        (let [o (v/assert kb orth 'CxUniverse {:strength :monotonic})]
          (is (= #{} (clashes kb)))
          (let [e (v/assert kb (list 'genl 'alphaKind 'betaKind) 'CxUniverse)]
            (is (= #{#{orth}} (clashes kb)) "the later edge convicts the stored declaration")
            (v/retract! kb e))
          (is (= #{} (clashes kb)))
          (v/retract! kb o))))))

(tu/deftest-kb an-orthogonal-under-a-separated-pair-is-a-clash-in-either-order
  ;; The exemption is read against the separated pair of supertypes, so (orthogonal subA
  ;; subB) does not lift (disjoint upperA upperB): an instance of both subtypes would be an
  ;; instance of both separated supertypes.  The report names the separation it was
  ;; convicted through.
  (tu/with-terms [upperA upperB subA subB]
    (v/assert kb (list 'genl 'upperA 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'upperB 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'subA 'upperA) 'CxUniverse)
    (v/assert kb (list 'genl 'subB 'upperB) 'CxUniverse)
    (let [orth (list 'orthogonal 'subA 'subB)
          dj   (list 'disjoint 'upperA 'upperB)]
      (testing "the separation first"
        (let [d (v/assert kb dj 'CxUniverse)
              o (v/assert kb orth 'CxUniverse)]
          (is (= #{#{orth}} (clashes kb)))
          (is (= [dj] (map :sentence (:grounds (first (filter #(= :orthogonal (:kind %))
                                                              (v/conflicts kb)))))))
          (v/retract! kb o)
          (v/retract! kb d)))
      (is (= #{} (clashes kb)))
      (testing "the orthogonal first"
        (let [o (v/assert kb orth 'CxUniverse)]
          (is (= #{} (clashes kb)))
          (let [d (v/assert kb dj 'CxUniverse)]
            (is (= #{#{orth}} (clashes kb)) "the later separation convicts the declaration")
            (v/retract! kb d))
          (is (= #{} (clashes kb)) "the separation leaving takes the clash")
          (v/retract! kb o))))))

(tu/deftest-kb an-orthogonal-under-two-partition-parts-is-a-clash
  (tu/with-terms [wholeKind alphaKind betaKind subA subB]
    (v/assert kb (list 'genl 'wholeKind 'thing) 'CxUniverse)
    (v/assert kb (list 'partition 'wholeKind 'alphaKind 'betaKind) 'CxUniverse)
    (v/assert kb (list 'genl 'subA 'alphaKind) 'CxUniverse)
    (v/assert kb (list 'genl 'subB 'betaKind) 'CxUniverse)
    (v/assert kb (list 'orthogonal 'subA 'subB) 'CxUniverse)
    (is (= #{#{(list 'orthogonal 'subA 'subB)}} (clashes kb)))))

(tu/deftest-kb orthogonal-is-on-the-forced-monotonic-roster
  (is (true? (v/has-prop? kb :forced-monotonic 'orthogonal)))
  (is (= :unforced-definitional-declaration
         (get checks/uncleared-forcing ['forced_monotonic_predicate 'orthogonal]))
      "held on every KB, as disjoint is, and its declaration is not retracted"))

(tu/deftest-kb a-default-declaration-the-taxonomy-contradicts-is-a-hard-clash
  ;; `orthogonal` is forced monotonic, so a declaration written at `:default` is held
  ;; `:monotonic`: its one-member nogood is a hard clash `conflicts` lists, every member
  ;; stays believed, and the pair reads both statuses.
  (tu/with-terms [alphaKind betaKind]
    (v/assert kb (list 'genl 'alphaKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'betaKind 'alphaKind) 'CxUniverse)
    (let [o (v/assert kb (list 'orthogonal 'alphaKind 'betaKind) 'CxUniverse {:strength :default})]
      (is (= :monotonic (v/defeat-class kb o)))
      (is (= #{#{(list 'orthogonal 'alphaKind 'betaKind)}} (clashes kb)))
      (is (true? (v/ask? kb (list 'orthogonal 'alphaKind 'betaKind) 'CxUniverse)))
      (is (= :inconsistent (v/subsumption-status kb 'alphaKind 'betaKind))))))

(tu/deftest-kb the-clash-is-read-where-the-separation-is-seen
  (tu/with-terms [upperA upperB subA subB]
    (let [cx (tu/tmp-ctx)]
      (v/assert kb (list 'genlCx cx 'CxUniverse) 'CxUniverse)
      (doseq [[s t] [['upperA 'thing] ['upperB 'thing] ['subA 'upperA] ['subB 'upperB]]]
        (v/assert kb (list 'genl s t) 'CxUniverse))
      (v/assert kb (list 'orthogonal 'subA 'subB) 'CxUniverse)
      (v/assert kb (list 'disjoint 'upperA 'upperB) cx)
      (is (= #{#{(list 'orthogonal 'subA 'subB)}} (clashes kb)))
      (is (= [#{cx}] (keep #(when (= :orthogonal (:kind %)) (clashes/report-vantages %))
                           (v/conflicts kb)))
          "read where the disjoint is seen, and not above it"))))

(tu/deftest-kb a-type-is-not-orthogonal-to-itself
  (tu/with-terms [alphaKind]
    (v/assert kb (list 'genl 'alphaKind 'thing) 'CxUniverse)
    (v/assert kb (list 'orthogonal 'alphaKind 'alphaKind) 'CxUniverse {:strength :monotonic})
    (is (= #{#{(list 'orthogonal 'alphaKind 'alphaKind)}} (clashes kb))
        "a type subsumes itself")))

;; ---- the exemption: every form of disjointness spares a stated pair ------------
;;
;; Each form of disjointness is one claim — an explicit `disjoint`, a `partition` or
;; `separating` roster (a partition keeps its coverage half), a `disjoint_metatype` and a
;; `sibling_disjoint` parent — and an `orthogonal` over the separated pair exempts it from
;; every one, wherever the declaration is seen.

(defn- exempted?
  "The pair `a` `b` reads apart at CxUniverse, `orthogonal`, with no orthogonal clash."
  [kb a b]
  (and (not (v/disjoint? kb a b 'CxUniverse))
       (= :orthogonal (v/subsumption-status kb a b))
       (empty? (clashes kb))))

(tu/deftest-kb an-orthogonal-pair-is-exempt-from-an-explicit-disjoint-in-every-order
  (tu/with-terms [alphaKind betaKind]
    (v/assert kb (list 'genl 'alphaKind 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'betaKind 'thing) 'CxUniverse)
    (doseq [[o-args d-args] [[['alphaKind 'betaKind] ['alphaKind 'betaKind]]
                             [['betaKind 'alphaKind] ['alphaKind 'betaKind]]]
            orth-first [true false]]
      (let [orth (cons 'orthogonal o-args)
            dj   (cons 'disjoint d-args)
            [h1 h2] (if orth-first
                      [(v/assert kb orth 'CxUniverse) (v/assert kb dj 'CxUniverse)]
                      [(v/assert kb dj 'CxUniverse) (v/assert kb orth 'CxUniverse)])]
        (is (true? (exempted? kb 'alphaKind 'betaKind))
            (str (pr-str orth) " and " (pr-str dj) (if orth-first ", orthogonal first" ", disjoint first")))
        (is (true? (v/in? kb (v/handle-of kb dj 'CxUniverse)))
            "the disjoint stays stored and believed")
        (is (false? (v/ask? kb dj 'CxUniverse))
            "and the disjointness prover answers the pair apart")
        (v/retract! kb h2)
        (v/retract! kb h1)))))

(tu/deftest-kb an-exempted-pair-lifts-the-separation-below-it
  (tu/with-terms [upperA upperB subA subB]
    (doseq [[s t] [['upperA 'thing] ['upperB 'thing] ['subA 'upperA] ['subB 'upperB]]]
      (v/assert kb (list 'genl s t) 'CxUniverse))
    (v/assert kb (list 'disjoint 'upperA 'upperB) 'CxUniverse)
    (is (true? (v/disjoint? kb 'subA 'subB 'CxUniverse)))
    (v/assert kb (list 'orthogonal 'upperA 'upperB) 'CxUniverse)
    (is (false? (v/disjoint? kb 'subA 'subB 'CxUniverse))
        "the exemption is read against the separated pair, so it reaches what it separated")))

(tu/deftest-kb an-orthogonal-pair-is-exempt-from-a-partition-which-keeps-its-cover
  (tu/with-terms [wholeKind alphaKind betaKind]
    (v/assert kb (list 'genl 'wholeKind 'thing) 'CxUniverse)
    (v/assert kb (list 'partition 'wholeKind 'alphaKind 'betaKind) 'CxUniverse)
    (is (true? (v/disjoint? kb 'alphaKind 'betaKind 'CxUniverse)))
    (v/assert kb (list 'orthogonal 'alphaKind 'betaKind) 'CxUniverse)
    (is (true? (exempted? kb 'alphaKind 'betaKind)))
    (is (true? (v/genl? kb 'alphaKind 'wholeKind)) "the cover's part edges stand")))

(tu/deftest-kb an-orthogonal-pair-is-exempt-from-a-separating-roster
  (tu/with-terms [wholeKind alphaKind betaKind gammaKind]
    (v/assert kb (list 'genl 'wholeKind 'thing) 'CxUniverse)
    (v/assert kb (list 'separating 'wholeKind 'alphaKind 'betaKind 'gammaKind) 'CxUniverse)
    (v/assert kb (list 'orthogonal 'alphaKind 'betaKind) 'CxUniverse)
    (is (true? (exempted? kb 'alphaKind 'betaKind)))
    (is (true? (v/disjoint? kb 'alphaKind 'gammaKind 'CxUniverse))
        "only the stated pair is spared")))

(tu/deftest-kb an-orthogonal-pair-is-exempt-from-sibling-disjointness
  (tu/with-terms [parentKind alphaKind betaKind gammaKind]
    (v/assert kb (list 'genl 'parentKind 'thing) 'CxUniverse)
    (v/assert kb (list 'sibling_disjoint 'parentKind) 'CxUniverse)
    (doseq [t ['alphaKind 'betaKind 'gammaKind]]
      (v/assert kb (list 'genl t 'parentKind) 'CxUniverse))
    (is (true? (v/disjoint? kb 'alphaKind 'betaKind 'CxUniverse)))
    (v/assert kb (list 'orthogonal 'alphaKind 'betaKind) 'CxUniverse)
    (is (true? (exempted? kb 'alphaKind 'betaKind)))
    (is (true? (v/disjoint? kb 'alphaKind 'gammaKind 'CxUniverse))
        "only the stated pair is spared")))

(tu/deftest-kb an-orthogonal-pair-is-exempt-from-a-disjoint-metatype
  (tu/with-terms [kind_type alphaKind betaKind gammaKind]
    (doseq [t ['alphaKind 'betaKind 'gammaKind]]
      (v/assert kb (list 'genl t 'thing) 'CxUniverse)
      (v/assert kb (list 'kind_type t) 'CxUniverse))
    (v/assert kb (list 'disjoint_metatype 'kind_type) 'CxUniverse)
    (is (true? (v/disjoint? kb 'alphaKind 'betaKind 'CxUniverse)))
    (v/assert kb (list 'orthogonal 'alphaKind 'betaKind) 'CxUniverse)
    (is (true? (exempted? kb 'alphaKind 'betaKind)))
    (is (true? (v/disjoint? kb 'betaKind 'gammaKind 'CxUniverse))
        "only the stated pair is spared")))

(tu/deftest-kb the-exemption-is-read-where-the-declaration-is-seen
  (tu/with-terms [alphaKind betaKind]
    (let [cx (tu/tmp-ctx)]
      (v/assert kb (list 'genlCx cx 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genl 'alphaKind 'thing) 'CxUniverse)
      (v/assert kb (list 'genl 'betaKind 'thing) 'CxUniverse)
      (v/assert kb (list 'disjoint 'alphaKind 'betaKind) 'CxUniverse)
      (v/assert kb (list 'orthogonal 'alphaKind 'betaKind) cx)
      (is (false? (v/disjoint? kb 'alphaKind 'betaKind cx)) "spared where it is stated")
      (is (true? (v/disjoint? kb 'alphaKind 'betaKind 'CxUniverse)) "separated above it")
      (is (= #{} (clashes kb)) "and no reader reads a clash"))))

;; ---- not preserved along genl --------------------------------------------------
;;
;; That two types could overlap says nothing about a subtype or a supertype of either: a
;; subtype of one may be disjoint from the other, and a supertype of one may subsume the
;; other.  CxCore denies both directions of preservation along genl at both positions.
;;
;; `transitiveInArg` and `transitiveInArgInverse` are both on the forced-monotonic roster,
;; so the four denials are stored and held OUT alike (`why-not` answers `:inert`): they
;; record the decision for a reader, and nothing concludes any of the four preservations,
;; so orthogonal is inherited neither way.

(def ^:private preservation-denials
  '[(not (transitiveInArgInverse orthogonal 1 genl))
    (not (transitiveInArgInverse orthogonal 2 genl))
    (not (transitiveInArg orthogonal 1 genl))
    (not (transitiveInArg orthogonal 2 genl))])

(tu/deftest-kb cxcore-denies-preserving-orthogonal-along-genl
  (doseq [s preservation-denials
          :let [h (v/handle-of kb s 'CxCore)]]
    (is (some? h) (str (pr-str s) " is stated in CxCore"))
    (is (= :inert (:reason (v/why-not kb h)))
        (str (pr-str s) " denies a forced-monotonic literal, so it is held OUT")))
  (doseq [s preservation-denials]
    (is (false? (v/ask? kb (second s) 'CxCore))
        (str (pr-str (second s)) " does not hold"))))

(tu/deftest-kb orthogonal-is-not-inherited-down-or-up-genl
  (tu/with-terms [alphaKind betaKind subAlpha superAlpha]
    (v/assert kb (list 'genl 'superAlpha 'thing) 'CxUniverse)
    (v/assert kb (list 'genl 'alphaKind 'superAlpha) 'CxUniverse)
    (v/assert kb (list 'genl 'subAlpha 'alphaKind) 'CxUniverse)
    (v/assert kb (list 'genl 'betaKind 'thing) 'CxUniverse)
    (v/assert kb (list 'orthogonal 'alphaKind 'betaKind) 'CxUniverse)
    (is (true? (v/ask? kb (list 'orthogonal 'alphaKind 'betaKind) 'CxUniverse)))
    (is (false? (v/ask? kb (list 'orthogonal 'subAlpha 'betaKind) 'CxUniverse))
        "a subtype of one side is not thereby orthogonal to the other")
    (is (false? (v/ask? kb (list 'orthogonal 'superAlpha 'betaKind) 'CxUniverse))
        "nor is a supertype")
    (is (false? (v/ask? kb (list 'orthogonal 'betaKind 'subAlpha) 'CxUniverse))
        "in either argument position")))

;; ---- the related-terms links ---------------------------------------------------

(tu/deftest-kb cxcore-links-orthogonal-to-its-neighbours
  (doseq [s '[(termsRelated sibling_disjoint disjoint_metatype disjoint orthogonal)
              (seeAlso sibling_disjoint genl)
              (termsRelated genl disjoint orthogonal)]]
    (is (some? (v/handle-of kb s 'CxCore)) (str (pr-str s) " is stated in CxCore")))
  (is (nil? (v/handle-of kb '(termsRelated disjoint orthogonal) 'CxCore))
      "the pairwise link the two rosters cover is gone"))

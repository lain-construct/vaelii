;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.context-nat-test
  "Reified-NAT contexts and structural genlCx — docs/context-nat.md.

  A `contextDenotingFunction` `Cx*Fn` reifies its ground applications to an opaque `cx/`
  context constant, so `(CxTimeFn CxMonad (DatetimeFn \"2000\"))` is a context a sentex can
  be stored in and a `genlCx` node — while its unreifiable argument stays structural in the
  `termOfUnit` map, readable to the producer.  `(contextArgSubrelation F pos R)` then orders
  sibling contexts structurally: `(CxTimeFn CxMonad (DatetimeFn \"2000-01\"))` is a spec of
  `(CxTimeFn CxMonad (DatetimeFn \"2000\"))` because January 2000 is inside 2000, with nobody
  asserting the `genlCx` edge."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.nat :as nat]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded core-context/load-into))
(use-fixtures :each (tu/neutral))

(def ^:private ctr (atom 0))
(defn- fresh-cxfn
  "A gensym'd context-function name — `Cx*Fn`-shaped so `naming/context-function?` reads it,
  unique per call so the net-neutral fixture's retraction leaves nothing behind."
  [base] (symbol (str "CxTmp" base (swap! ctr inc) "Fn")))

(defn- declare-datetime-dimension!
  "Declare a fresh `Cx*Fn` context function ordered by `subintervalOf` on its datetime
  argument, plus `DatetimeFn` as a structural (unreifiable) constructor.  Returns the
  context-function symbol."
  [kb]
  (let [cxfn (fresh-cxfn "Time")]
    (v/assert kb (list 'contextDenotingFunction cxfn) 'CxUniverse)
    (v/assert kb '(unreifiableFunction DatetimeFn) 'CxUniverse)
    cxfn))

;; ---- Layer 1: a Cx*Fn application reifies to a cx/ context ---------------

(tu/deftest-kb a-context-fn-application-reifies-to-a-cx-context
  (let [cxfn (declare-datetime-dimension! kb)
        expr (list cxfn 'CxMonad (list 'DatetimeFn "2000"))
        h    (v/assert kb '(likes Tom Ann) expr)
        k    (:context (v/sentex kb h))]
    (testing "the context slot is a reified cx/ constant that classifies as a context"
      (is (nat/reified-context-symbol? k))
      (is (= :context (v/term-role k))))
    (testing "the unreifiable datetime argument stays structural in the termOfUnit map"
      (is (= [(list 'termOfUnit k expr)]
             (map :sentence (v/sentexes-matching kb (list 'termOfUnit k '?e) 'CxUniverse)))))
    (testing "the fact reads back from the compound context (read-side reify is symmetric)"
      (is (= [{'?x 'Ann}] (v/ask kb '(likes Tom ?x) expr))))
    (testing "the same compound dedups to one context constant"
      (let [h2 (v/assert kb '(knows Tom Bob) expr)]
        (is (= k (:context (v/sentex kb h2))))))))

;; ---- Layer 1: a cx/ constant is a well-formed genlCx node ----------------

(tu/deftest-kb a-cx-context-is-a-well-formed-genlcx-node
  (let [cxfn (declare-datetime-dimension! kb)
        h    (v/assert kb '(likes Tom Ann) (list cxfn 'CxMonad (list 'DatetimeFn "2000")))
        k    (:context (v/sentex kb h))]
    (testing "a hand-asserted genlCx edge over the cx/ constant is accepted and wires it in"
      (v/assert kb (list 'genlCx k 'CxCore) 'CxUniverse)
      (is (contains? (set (v/contexts kb)) k))
      (is (v/sees? kb k 'CxCore)))))

;; ---- object nat/ constants are still refused as contexts -----------------

(tu/deftest-kb an-object-nat-is-still-not-a-context
  (tu/with-terms [FruitFn AppleTree]
    (v/assert kb (list 'reifiableFunction FruitFn) 'CxUniverse)
    (let [h (v/assert kb (list 'color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k (second (:sentence (v/sentex kb h)))]
      (is (nat/reified-nat-symbol? k) "it is a reified constant")
      (is (not (nat/reified-context-symbol? k)) "but an object one, not a context")
      (is (not= :context (v/term-role k)))
      (testing "storing a fact in an object nat/ context is refused by naming"
        (is (= :naming
               (try (v/assert kb '(likes Tom Ann) k) ::stored
                    (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))))))

;; ---- Layer 2: structural genlCx from a declared arg sub-relation ---------

(defn- year-and-month
  "Declare the datetime dimension + the subintervalOf ordering, store one fact in the
  year context and one in the month, and return `{:cxfn :year :month :ky :km}`."
  [kb]
  (let [cxfn  (declare-datetime-dimension! kb)
        _     (v/assert kb (list 'contextArgSubrelation cxfn 2 'subintervalOf) 'CxUniverse)
        year  (list cxfn 'CxMonad (list 'DatetimeFn "2000"))
        month (list cxfn 'CxMonad (list 'DatetimeFn "2000-01"))
        hy    (v/assert kb '(holiday NewYear) year)
        hm    (v/assert kb '(weather Cold) month)]
    {:cxfn cxfn :year year :month month
     :ky (:context (v/sentex kb hy)) :km (:context (v/sentex kb hm))}))

(tu/deftest-kb a-month-context-is-a-computed-spec-of-its-year
  (let [{:keys [year month ky km]} (year-and-month kb)]
    (testing "the producer materialized (genlCx month year) with nobody asserting it"
      (is (v/sees? kb km ky) "the month context sees the year context")
      (is (not (v/sees? kb ky km)) "but the year does not see the month"))
    (testing "the edge is a real justified sentex, and the month is in the hierarchy"
      (is (contains? (set (v/contexts kb)) km))
      (is (= [(list 'genlCx km ky)]
             (map :sentence (v/sentexes-matching kb (list 'genlCx km ky) 'CxUniverse)))))
    (testing "a fact in the year is visible from the month (inheritance up the cone)"
      (is (= [{'?h 'NewYear}] (v/ask kb '(holiday ?h) month))))
    (testing "a fact in the month is NOT visible from the year"
      (is (empty? (v/ask kb '(weather ?w) year))))))

(tu/deftest-kb the-computed-edge-belief-follows-its-reasons
  (let [{:keys [cxfn km ky]} (year-and-month kb)]
    (is (v/sees? kb km ky) "baseline: the edge holds")
    (testing "retracting the subrelation declaration withdraws the computed edge"
      (let [decl (tu/sentex-matching kb (list 'contextArgSubrelation cxfn 2 'subintervalOf)
                                     'CxUniverse)]
        (v/retract! kb (:id decl))
        (is (not (v/sees? kb km ky)) "the month no longer sees the year")))))

(tu/deftest-kb the-order-of-arrival-does-not-decide-the-edge
  ;; declaration last, contexts first — the retroactive sweep must reach them
  (let [cxfn  (declare-datetime-dimension! kb)
        year  (list cxfn 'CxMonad (list 'DatetimeFn "2000"))
        month (list cxfn 'CxMonad (list 'DatetimeFn "2000-01"))]
    (v/assert kb '(holiday NewYear) year)
    (v/assert kb '(weather Cold) month)
    (let [km (:context (tu/sentex-matching kb '(weather Cold) month))
          ky (:context (tu/sentex-matching kb '(holiday NewYear) year))]
      (is (not (v/sees? kb km ky)) "no edge before the declaration")
      (v/assert kb (list 'contextArgSubrelation cxfn 2 'subintervalOf) 'CxUniverse)
      (is (v/sees? kb km ky) "the declaration arriving last sweeps the existing contexts"))))

;; ---- Finding #1: the producer reacts to belief REVIVAL, not only to assert ----

(defn- refusal
  "The `:type` a thrown assert refused with, or ::stored when it did not throw."
  [f]
  (try (f) ::stored
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(tu/deftest-kb a-revived-subrelation-declaration-rebuilds-the-computed-edge
  ;; The producer runs only on the assert choke-point, but the belief of a
  ;; `contextArgSubrelation` declaration can flip OUT→IN with NO assert — retracting a
  ;; monotonic defeater above it revives it.  An edge never built while the declaration was
  ;; OUT has no justification to revive, so `retract!` must re-run the producer
  ;; (`reconcile-revivals!`) against the settled belief (docs/context-nat.md).
  (let [cxfn  (declare-datetime-dimension! kb)
        year  (list cxfn 'CxMonad (list 'DatetimeFn "2000"))
        month (list cxfn 'CxMonad (list 'DatetimeFn "2000-01"))
        hy    (v/assert kb '(holiday NewYear) year)
        hm    (v/assert kb '(weather Cold) month)
        ky    (:context (v/sentex kb hy))
        km    (:context (v/sentex kb hm))]
    (testing "baseline: no declaration, so the month does not see the year"
      (is (not (v/sees? kb km ky))))
    ;; the declaration is stored-but-defeated (a monotonic negation wins) → not believed →
    ;; the producer builds no edge
    (v/assert kb (list 'not (list 'contextArgSubrelation cxfn 2 'subintervalOf)) 'CxUniverse
              {:strength :monotonic})
    (v/assert kb (list 'contextArgSubrelation cxfn 2 'subintervalOf) 'CxUniverse)
    (testing "a defeated declaration builds no edge"
      (is (not (v/in? kb (:id (tu/sentex-matching
                               kb (list 'contextArgSubrelation cxfn 2 'subintervalOf)
                               'CxUniverse))))
          "the declaration is stored but OUT")
      (is (not (v/sees? kb km ky))))
    ;; retract the monotonic negation — the declaration REVIVES with no further assert
    (let [neg (tu/sentex-matching
               kb (list 'not (list 'contextArgSubrelation cxfn 2 'subintervalOf)) 'CxUniverse)]
      (v/retract! kb (:id neg)))
    (testing "reviving the declaration rebuilds the computed edge, before any further assert"
      (is (v/sees? kb km ky) "the month now sees the year")
      (is (= [{'?h 'NewYear}] (v/ask kb '(holiday ?h) month))
          "and a fact in the year is visible from the month up the cone"))))

;; ---- Finding #2: a Cx*Fn in ARGUMENT position does not alias the context ----

(tu/deftest-kb a-context-fn-in-argument-position-does-not-alias-the-context
  ;; A context-denoting `Cx*Fn` application reifies to a `cx/` constant only in the CONTEXT
  ;; slot; the sentence/argument reify walk must leave it structural, or one `cx/` constant
  ;; would be both a context and an untyped object relatum (docs/context-nat.md).
  (let [cxfn (declare-datetime-dimension! kb)
        expr (list cxfn 'CxMonad (list 'DatetimeFn "2000"))
        hc   (v/assert kb '(likes Tom Ann) expr)              ; context-slot use → cx/ constant
        kctx (:context (v/sentex kb hc))
        ha   (v/assert kb (list 'happenedDuring 'Event1 expr) 'CxUniverse)  ; argument-position use
        arg2 (nth (:sentence (v/sentex kb ha)) 2)]
    (testing "the context slot reified to a cx/ constant"
      (is (nat/reified-context-symbol? kctx)))
    (testing "the same expression in argument position is NOT that cx/ constant"
      (is (not= kctx arg2) "the argument must not alias the context slot")
      (is (not (nat/reified-context-symbol? arg2)) "and is no cx/ context constant at all")
      (is (and (sequential? arg2) (= cxfn (first arg2)))
          "it stays a structural compound, exactly as an unreifiable NAT does"))))

;; ---- Finding #3: the context-slot shape gate does not depend on the naming policy ----

(tu/deftest-kb naming-off-still-refuses-a-non-symbol-context-for-shape
  ;; `check-shape!` runs independent of the naming policy, and the gate re-checks that
  ;; reification would yield a symbol — so an undeclared or non-ground compound context is a
  ;; `:shape` refusal even under `:naming :off`, never a raw list in a sentex's context slot
  ;; (docs/context-nat.md).
  (let [cxfn   (declare-datetime-dimension! kb)
        kb-off (assoc kb :naming :off)]
    (testing "an UNDECLARED context-function compound is a shape error even with naming off"
      (is (= :shape (refusal #(v/assert kb-off '(likes Tom Ann)
                                        (list 'CxBogusFn 'CxMonad (list 'DatetimeFn "2000")))))))
    (testing "a DECLARED but NON-GROUND context is a shape error even with naming off"
      (is (= :shape (refusal #(v/assert kb-off '(likes Tom Ann)
                                        (list cxfn 'CxMonad '?x))))))
    (testing "a declared ground context still reifies to a symbol and stores (control)"
      (let [h (v/assert kb-off '(likes Tom Ann) (list cxfn 'CxMonad (list 'DatetimeFn "2000")))]
        (is (symbol? (:context (v/sentex kb-off h))))))))

;; ---- Finding #4: the stored-fact R oracle picks its supporter content-keyed ----

(tu/deftest-kb the-stored-fact-oracle-chooses-its-supporter-by-content
  ;; `subintervalOf` answers `::pure`, so exercise the stored-fact branch with a
  ;; sub-relation that has no registered comparator.  With two believed `(R a b)` facts —
  ;; the same ground relation in two contexts — the edge's supporter must be chosen by
  ;; content (the lexicographically-smallest context), never by handle/retrieval order
  ;; (docs/context-nat.md, order independence).
  (let [cxfn  (declare-datetime-dimension! kb)
        yterm (list 'DatetimeFn "2000")
        mterm (list 'DatetimeFn "2000-01")
        year  (list cxfn 'CxMonad yterm)
        month (list cxfn 'CxMonad mterm)
        rfact (list 'subFooOf mterm yterm)]
    ;; two R-evidence facts, CxUniverse first (lower handle), CxCore second (higher handle
    ;; but the smaller context by content) — so a handle/retrieval-first pick and a
    ;; content-first pick disagree.
    (v/assert kb rfact 'CxUniverse)
    (v/assert kb rfact 'CxCore)
    (v/assert kb '(holiday NewYear) year)
    (v/assert kb '(weather Cold) month)
    (v/assert kb (list 'contextArgSubrelation cxfn 2 'subFooOf) 'CxUniverse)
    (let [ky (:context (tu/sentex-matching kb '(holiday NewYear) year))
          km (:context (tu/sentex-matching kb '(weather Cold) month))]
      (testing "the stored-fact oracle materialized the edge"
        (is (v/sees? kb km ky)))
      (let [edge (tu/sentex-matching kb (list 'genlCx km ky) 'CxUniverse)
            just (first (filter #(= 'contextArgSubrelation (:informant %))
                                (v/supporting-justifications kb (:id edge))))
            ev   (first (filter #(= rfact (:sentence (v/sentex kb %))) (:antecedents just)))]
        (testing "its R-evidence supporter is the fact in the smallest context, not the first"
          (is (= 'CxCore (:context (v/sentex kb ev)))))))))

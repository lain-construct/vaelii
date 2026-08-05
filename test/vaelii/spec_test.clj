;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.spec-test
  "Instrument the public API with `vaelii.impl.spec` and confirm the boundary bites:
  well-formed argument shapes pass, malformed option/budget maps and bad handles are
  rejected before the function body runs.

  **A refusal is only evidence when it names its source.**  The engine refuses malformed
  input on its own account too — a non-map `opts` is `:unknown-option`, a non-symbol
  context is `:shape`, a string handle is a cast error — so `(thrown? Exception …)` here
  passes whether the spec bit or the body did, and every spec in `vspec/public-syms`
  could be dropped with this file green.  `rejection` below is what separates them: a
  spec refusal carries `::s/failure :instrument`, and that is what the instrumented
  tests assert.

  The last test is deliberately **outside** instrumentation, because
  `core/check-assert-opts!` is unreachable under it — the spec rejects the same call
  first — and it is the only refusal a caller who never opted in ever sees."
  (:require [clojure.spec.alpha :as s]
            [clojure.spec.test.alpha :as stest]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.spec :as vspec]
            [vaelii.test-util :as tu]))

(defn- rejection
  "How a thunk was refused: `:instrument` when a spec caught it at the boundary, else
  the engine's own `ex-data` `:type`, else the class of whatever was thrown.  nil when
  nothing was."
  [f]
  (try (f) nil
       (catch clojure.lang.ExceptionInfo e
         (let [d (ex-data e)]
           (or (::s/failure d) (:type d) :ex-info-carrying-neither)))
       (catch Throwable t (class t))))

(defmacro ^:private instrumented
  "Run `body` with the whole public roster instrumented, unstrumenting whatever happens."
  [& body]
  `(do (stest/instrument vspec/public-syms)
       (try ~@body
            (finally (stest/unstrument vspec/public-syms)))))

(deftest instrumented-boundary-accepts-valid-and-rejects-malformed
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Fido Rex SpecContext]
      (instrumented
       (testing "a well-formed assert (valid opts) passes instrumentation"
         (is (some? (v/assert kb (list dog Fido) SpecContext {:strength :monotonic}))))
       (testing "an unknown :strength keyword is rejected at the boundary"
         (is (= :instrument
                (rejection #(v/assert kb (list dog Rex) SpecContext {:strength :monotone})))))
       (testing "a non-map opts is rejected"
         (is (= :instrument
                (rejection #(v/assert kb (list dog Rex) SpecContext :nope)))))
       (testing "a non-symbol context is rejected"
         (is (= :instrument
                (rejection #(v/assert kb (list dog Rex) (str SpecContext))))))
       (testing "a malformed budget (string where a ms count belongs) is rejected"
         (is (= :instrument
                (rejection #(v/ask-within kb (list dog Fido) SpecContext {:max-ms "soon"})))))
       (testing "a bad :max-cost tier is rejected"
         (is (= :instrument
                (rejection #(v/ask-within kb (list dog Fido) SpecContext {:max-cost :instant})))))
       (testing "a non-integer handle to retract! is rejected"
         (is (= :instrument (rejection #(v/retract! kb "not-a-handle")))))
       (testing "and none of the refusals stored anything"
         (is (nil? (v/handle-of kb (list dog Rex) SpecContext))))))))

(deftest every-public-sym-resolves
  ;; a symbol in the roster that names no var is a stale spec — instrument would
  ;; silently skip it, so the coverage claim would be a lie
  (doseq [sym vspec/public-syms]
    (is (some? (resolve sym)) (str sym " does not resolve to a var"))))

(deftest instrumented-boundary-accepts-the-expanded-surface
  ;; `public-syms` spans the whole shape-carrying API, so instrument the lot and
  ;; run one valid call through every arg spec that is more than `[kb x]`: a vector
  ;; goal, a level integer, an escalate floor, the `{:believed? true}` extent opt,
  ;; both `why-not` arities, a `:direction` rule opt.  A wrong spec would reject a
  ;; call the engine accepts — this is what catches it.  Answers are irrelevant.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog cat animal Fido Felix Rex parentOf childOf SpecContext]
      (instrumented
       (testing "writes: rule direction opt + provenance"
         (let [h (v/assert kb (list dog Fido) SpecContext {:strength :monotonic})]
           (is (nat-int? h))
           (is (map? (v/add-provenance kb h {:source :test})))
           (is (nat-int? (v/ist kb SpecContext (list cat Felix))))
           (v/assert-rule kb [(list parentOf '?x '?y)] (list childOf '?y '?x)
                          SpecContext {:direction :forward})))
       (testing "reads: query 2- and 3-arity, ask, prove single + vector goal"
         (is (some? (seq (concat (v/sentexes-matching kb (list dog '?x))
                                 (v/sentexes-matching kb (list dog '?x) SpecContext)))))
         (dorun (v/ask kb (list dog '?x) SpecContext))
         (v/prove kb (list dog '?x) SpecContext)
         (v/prove kb [(list parentOf '?x '?y) (list dog '?y)] SpecContext)
         (is (boolean? (v/provable? kb (list dog Fido) SpecContext)))
         (v/query-plan kb [(list parentOf '?x '?y) (list dog '?y)] SpecContext))
       (testing "the lookup-to-query stack: every level + escalate floor"
         (doseq [lvl (range 0 8)] (dorun (v/lookup kb lvl (list dog '?x) SpecContext)))
         (v/escalate kb (list dog Fido) SpecContext)
         (v/escalate kb (list dog Fido) SpecContext 3)
         (v/explain-levels kb (list dog Fido) SpecContext))
       (testing "taxonomy + equality + metadata reads"
         (v/genls kb animal) (v/specs kb animal) (v/genl? kb dog animal)
         (v/types kb) (v/contexts kb)
         (v/context-up kb SpecContext) (v/sees? kb SpecContext SpecContext)
         (is (boolean? (v/isa? kb Fido dog SpecContext)))
         (v/types-of kb Fido SpecContext)
         (is (boolean? (v/has-prop? kb :symmetric parentOf)))
         (v/props kb :transitive) (v/inverse-of kb parentOf)
         (v/representative kb Fido) (v/equiv-class kb Fido)
         (is (boolean? (v/same-class? kb Fido Fido)))
         (is (boolean? (v/deprecated? kb Fido))))
       (testing "browser-support reads: term-role, metatypes, readable, indexable"
         (is (= :individual (v/term-role Fido)))
         (is (= :context (v/term-role SpecContext)))
         (is (= :variable (v/term-role '?x)))
         (v/disjoint-metatypes kb)
         (v/metatype-members kb dog)
         (let [sx (v/sentex kb (v/handle-of kb (list dog Fido) SpecContext))]
           (is (= (list dog Fido) (v/readable-sentence sx)))
           (is (coll? (v/indexable-terms sx)))))
       (testing "term index + extents with the {:believed? true} opt"
         (v/find-sentexes kb Fido) (v/find-sentexes-all kb [Fido dog])
         (v/sentexes-in-context kb SpecContext {:believed? true})
         (is (nat-int? (v/context-size kb SpecContext)))
         (v/sentexes-with-functor kb dog)
         (is (nat-int? (v/count-with-functor kb dog)))
         (v/sentexes-with-arg kb 1 Fido {:believed? true})
         (is (nat-int? (v/count-with-arg kb 1 Fido))))
       (testing "the vocabulary: enumerate, count, and search with every opt"
         (is (vector? (v/terms kb)))
         (is (nat-int? (v/term-count kb)))
         (let [head (subs (name Fido) 0 4)]
           (v/find-terms kb head)
           (v/find-terms kb (symbol head) {:match :prefix :case-sensitive? true}))
         (v/find-terms kb (subs (name Fido) 1 4) {:match :substring})
         (v/find-terms kb (str "^" Fido "$") {:match :regex :limit 5}))
       (testing "introspection + both why-not arities"
         (let [h (v/handle-of kb (list dog Fido) SpecContext)]
           (is (nat-int? h))
           (is (boolean? (v/in? kb h)))
           (is (map? (v/sentex kb h)))
           (v/premise? kb h) (v/defeat-class kb h)
           (v/supporting-justifications kb h) (v/dependent-justifications kb h)
           (is (map? (v/why kb h)))
           (is (map? (v/why-not kb h)))
           (is (map? (v/why-not kb (list dog Rex) SpecContext)))
           (v/contexts-of kb (list dog Fido))))))))

;; ---- the guard instrumentation hides ------------------------------------

(deftest a-non-map-opts-is-refused-without-instrumentation-too
  ;; `check-assert-opts!` is the first thing `assert` runs, and under `instrument` the
  ;; spec rejects the same call before it — so the instrumented tests above cannot see
  ;; this guard at all, and deleting it would leave them green.  A caller who never
  ;; opted in gets *only* this reading, and what it must not do is take every default
  ;; in silence: `{:strength :monotone}` ignored stores a defeasible sentex where
  ;; known-true was meant, and nothing downstream can tell it from one that was asked
  ;; for.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Fido SpecContext]
      (testing "a non-map opts is refused rather than ignored"
        (is (= :unknown-option
               (rejection #(v/assert kb (list dog Fido) SpecContext :nope)))))
      (testing "an unread key, and a :strength that is not an assertable class, likewise"
        (is (= :unknown-option
               (rejection #(v/assert kb (list dog Fido) SpecContext {:strenth :monotonic}))))
        (is (= :unknown-option
               (rejection #(v/assert kb (list dog Fido) SpecContext {:strength :monotone})))))
      (testing "and `check` agrees with `assert` about the non-map, which is why the
                guard is there rather than a look inside the map"
        (is (= [:shape] (mapv :type (v/check kb (list dog Fido) SpecContext :nope)))))
      (testing "none of them stored the sentence"
        (is (nil? (v/handle-of kb (list dog Fido) SpecContext)))))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.spec-test
  "Instrument the public API with `vaelii.impl.spec` and confirm the boundary bites:
  well-formed argument shapes pass, malformed option/budget maps and bad handles are
  rejected before the function body runs."
  (:require [clojure.spec.test.alpha :as stest]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.spec :as vspec]
            [vaelii.test-util :as tu]))

(deftest instrumented-boundary-accepts-valid-and-rejects-malformed
  (stest/instrument vspec/public-syms)
  (try
    (let [kb (tu/fresh)]
      (testing "a well-formed assert (valid opts) passes instrumentation"
        (is (some? (v/assert kb '(dog Fido) 'UniverseContext {:strength :monotonic}))))
      (testing "an unknown :strength keyword is rejected at the boundary"
        (is (thrown? Exception
                     (v/assert kb '(dog Rex) 'UniverseContext {:strength :monotone}))))
      (testing "a non-map opts is rejected"
        (is (thrown? Exception
                     (v/assert kb '(dog Rex) 'UniverseContext :nope))))
      (testing "a non-symbol context is rejected"
        (is (thrown? Exception
                     (v/assert kb '(dog Rex) "UniverseContext"))))
      (testing "a malformed budget (string where a ms count belongs) is rejected"
        (is (thrown? Exception
                     (v/ask-within kb '(dog Fido) 'UniverseContext {:max-ms "soon"}))))
      (testing "a bad :max-cost tier is rejected"
        (is (thrown? Exception
                     (v/ask-within kb '(dog Fido) 'UniverseContext {:max-cost :instant}))))
      (testing "a non-integer handle to retract! is rejected"
        (is (thrown? Exception (v/retract! kb "not-a-handle")))))
    (finally
      (stest/unstrument vspec/public-syms)))
  (tu/clear-kb! (tu/test-kb)))

(deftest every-public-sym-resolves
  ;; a symbol in the roster that names no var is a stale spec — instrument would
  ;; silently skip it, so the coverage claim would be a lie
  (doseq [sym vspec/public-syms]
    (is (some? (resolve sym)) (str sym " does not resolve to a var"))))

(deftest instrumented-boundary-accepts-the-expanded-surface
  ;; `public-syms` now spans the whole shape-carrying API, so instrument the lot and
  ;; run one valid call through every arg spec that is more than `[kb x]`: a vector
  ;; goal, a level integer, an escalate floor, the `{:believed? true}` extent opt,
  ;; both `why-not` arities, a `:direction` rule opt.  A wrong spec would reject a
  ;; call the engine accepts — this is what catches it.  Answers are irrelevant.
  (stest/instrument vspec/public-syms)
  (try
    (let [kb (tu/fresh)]
      (testing "writes: rule direction opt + provenance"
        (let [h (v/assert kb '(dog Fido) 'SpecContext {:strength :monotonic})]
          (is (nat-int? h))
          (is (map? (v/add-provenance kb h {:source :test})))
          (is (nat-int? (v/ist kb 'SpecContext '(cat Felix))))
          (v/assert-rule kb '[(parentOf ?x ?y)] '(childOf ?y ?x)
                         'SpecContext {:direction :forward})))
      (testing "reads: query 2- and 3-arity, ask, prove single + vector goal"
        (is (some? (seq (concat (v/sentexes-matching kb '(dog ?x))
                                (v/sentexes-matching kb '(dog ?x) 'SpecContext)))))
        (dorun (v/ask kb '(dog ?x) 'SpecContext))
        (v/prove kb '(dog ?x) 'SpecContext)
        (v/prove kb '[(parentOf ?x ?y) (dog ?y)] 'SpecContext)
        (is (boolean? (v/provable? kb '(dog Fido) 'SpecContext)))
        (v/query-plan kb '[(parentOf ?x ?y) (dog ?y)] 'SpecContext))
      (testing "the lookup-to-query stack: every level + escalate floor"
        (doseq [lvl (range 0 8)] (dorun (v/lookup kb lvl '(dog ?x) 'SpecContext)))
        (v/escalate kb '(dog Fido) 'SpecContext)
        (v/escalate kb '(dog Fido) 'SpecContext 3)
        (v/explain-levels kb '(dog Fido) 'SpecContext))
      (testing "taxonomy + equality + metadata reads"
        (v/genls kb 'animal) (v/specs kb 'animal) (v/genl? kb 'dog 'animal)
        (v/types kb) (v/contexts kb)
        (v/context-up kb 'SpecContext) (v/sees? kb 'SpecContext 'SpecContext)
        (is (boolean? (v/isa? kb 'Fido 'dog 'SpecContext)))
        (v/types-of kb 'Fido 'SpecContext)
        (is (boolean? (v/has-prop? kb :symmetric 'parentOf)))
        (v/props kb :transitive) (v/inverse-of kb 'parentOf)
        (v/representative kb 'Fido) (v/equiv-class kb 'Fido)
        (is (boolean? (v/same-class? kb 'Fido 'Fido)))
        (is (boolean? (v/deprecated? kb 'Fido))))
      (testing "browser-support reads: term-role, metatypes, readable, indexable"
        (is (= :individual (v/term-role 'Fido)))
        (is (= :context (v/term-role 'SpecContext)))
        (is (= :variable (v/term-role '?x)))
        (v/disjoint-metatypes kb)
        (v/metatype-members kb 'dog)
        (let [sx (v/sentex kb (v/handle-of kb '(dog Fido) 'SpecContext))]
          (is (= '(dog Fido) (v/readable-sentence sx)))
          (is (coll? (v/indexable-terms sx)))))
      (testing "term index + extents with the {:believed? true} opt"
        (v/find-sentexes kb 'Fido) (v/find-sentexes-all kb '[Fido dog])
        (v/sentexes-in-context kb 'SpecContext {:believed? true})
        (is (nat-int? (v/context-size kb 'SpecContext)))
        (v/sentexes-with-functor kb 'dog)
        (is (nat-int? (v/count-with-functor kb 'dog)))
        (v/sentexes-with-arg kb 1 'Fido {:believed? true})
        (is (nat-int? (v/count-with-arg kb 1 'Fido))))
      (testing "the vocabulary: enumerate, count, and search with every opt"
        (is (vector? (v/terms kb)))
        (is (nat-int? (v/term-count kb)))
        (v/find-terms kb "Fi")
        (v/find-terms kb 'Fi {:match :prefix :case-sensitive? true})
        (v/find-terms kb "id" {:match :substring})
        (v/find-terms kb "^Fido$" {:match :regex :limit 5}))
      (testing "introspection + both why-not arities"
        (let [h (v/handle-of kb '(dog Fido) 'SpecContext)]
          (is (nat-int? h))
          (is (boolean? (v/in? kb h)))
          (is (map? (v/sentex kb h)))
          (v/premise? kb h) (v/defeat-class kb h)
          (v/supporting-justifications kb h) (v/dependent-justifications kb h)
          (is (map? (v/why kb h)))
          (is (map? (v/why-not kb h)))
          (is (map? (v/why-not kb '(dog Rex) 'SpecContext)))
          (v/contexts-of kb '(dog Fido)))))
    (finally
      (stest/unstrument vspec/public-syms)))
  (tu/clear-kb! (tu/test-kb)))

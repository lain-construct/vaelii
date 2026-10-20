;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.common-genls-test
  "The common supertypes and common subtypes of several types, read through the API
  (`common-genls`, `min-common-genls`, `common-specs`, `max-common-specs`) and through
  the two computed predicates `minCommonGenl` and `maxCommonSpec`.

  The hierarchy every test builds has a diamond and a chain under one top:

      a ⊂ left, a ⊂ right, b ⊂ left, b ⊂ right, left ⊂ top, right ⊂ top
      c ⊂ mid, d ⊂ mid, mid ⊂ top, top ⊂ thing"
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (tu/load-core!))))

(defn- edges!
  "Assert each `[sub super]` pair as a `genl` edge in `context`."
  [kb context pairs]
  (doseq [[sub super] pairs]
    (v/assert kb (list 'genl sub super) context)))

(defmacro ^:private with-hierarchy
  "Bind the diamond-and-chain types and assert their edges in CxUniverse."
  [& body]
  `(tu/with-terms [~'top ~'left ~'right ~'mid ~'a ~'b ~'c ~'d]
     (edges! ~'kb ~''CxUniverse [[~'top ~''thing] [~'left ~'top] [~'right ~'top]
                                 [~'a ~'left] [~'a ~'right] [~'b ~'left] [~'b ~'right]
                                 [~'mid ~'top] [~'c ~'mid] [~'d ~'mid]])
     ~@body))

;; ---- the API ---------------------------------------------------------------

(tu/deftest-kb common-genls-is-the-intersection-of-the-reflexive-genls
  (with-hierarchy
    (testing "one type: its own genls, itself included"
      (is (= (v/genls kb a) (v/common-genls kb [a])))
      (is (contains? (v/common-genls kb [a]) a)))
    (testing "two types: the supertypes both have"
      (is (= (set/intersection (v/genls kb a) (v/genls kb b)) (v/common-genls kb [a b])))
      (is (set/subset? #{left right top 'thing} (v/common-genls kb [a b])))
      (is (not (contains? (v/common-genls kb [a b]) a))))
    (testing "a type below the other: the upper one is a common genl of both"
      (is (contains? (v/common-genls kb [c mid]) mid)))
    (testing "three types"
      (is (= (set/intersection (v/genls kb a) (v/genls kb b) (v/genls kb c))
             (v/common-genls kb [a b c])))
      (is (contains? (v/common-genls kb [a b c]) top))
      (is (not-any? (v/common-genls kb [a b c]) [left right mid])))))

(tu/deftest-kb common-specs-is-the-intersection-of-the-reflexive-specs
  (with-hierarchy
    (is (= (v/specs kb top) (v/common-specs kb [top])))
    (is (= #{a b} (v/common-specs kb [left right])))
    (is (= #{a b} (v/common-specs kb [left right top])))
    (is (= #{c} (v/common-specs kb [c mid])))
    (is (= #{} (v/common-specs kb [a c])))))

(tu/deftest-kb min-common-genls-keeps-the-minimal-strict-common-supertypes
  (with-hierarchy
    (testing "a diamond keeps both sides"
      (is (= #{left right} (v/min-common-genls kb [a b]))))
    (testing "a chain keeps its nearest member"
      (is (= #{mid} (v/min-common-genls kb [c d]))))
    (testing "an input is not its own common genl: the answer is strictly above every input"
      (is (= #{top} (v/min-common-genls kb [c mid]))))
    (testing "three types meet at the top"
      (is (= #{top} (v/min-common-genls kb [a b c]))))
    (testing "one type: exactly min-genls"
      (doseq [t [a b c mid top]]
        (is (= (v/min-genls kb t) (v/min-common-genls kb [t])) (str t))))))

(tu/deftest-kb max-common-specs-keeps-the-maximal-strict-common-subtypes
  (with-hierarchy
    (is (= #{a b} (v/max-common-specs kb [left right])))
    (is (= #{c d} (v/max-common-specs kb [mid top])))
    (is (= #{a b} (v/max-common-specs kb [left right top])))
    (is (= #{} (v/max-common-specs kb [a c])))
    (testing "one type: exactly max-specs"
      (doseq [t [top left mid a]]
        (is (= (v/max-specs kb t) (v/max-common-specs kb [t])) (str t))))))

(tu/deftest-kb the-api-reads-the-edges-a-context-sees
  (with-hierarchy
    (tu/with-terms [CxSide side_kind]
      (v/assert kb (list 'genlCx CxSide 'CxUniverse) 'CxUniverse)
      (edges! kb 'CxUniverse [[side_kind 'thing]])
      (edges! kb CxSide [[a side_kind] [b side_kind]])
      (is (= #{left right side_kind} (v/min-common-genls kb [a b] CxSide)))
      (is (= #{left right} (v/min-common-genls kb [a b] 'CxUniverse)))
      (is (contains? (v/common-genls kb [a b] CxSide) side_kind))
      (is (not (contains? (v/common-genls kb [a b] 'CxUniverse) side_kind)))
      (is (= #{a b} (v/max-common-specs kb [side_kind top] CxSide)))
      (is (= #{} (v/max-common-specs kb [side_kind top] 'CxUniverse))))))

(defn- answers
  "The values `query` binds `?x` to for `goal` in `context`, as a set."
  [kb goal context]
  (into #{} (map #(get % '?x)) (v/query kb goal context)))

;; ---- the predicates ----------------------------------------------------------

(tu/deftest-kb min-common-genl-with-an-open-first-argument-binds-each-minimum
  (with-hierarchy
    (is (= #{left right} (answers kb (list 'minCommonGenl '?x a b) 'CxUniverse)))
    (is (= #{mid} (answers kb (list 'minCommonGenl '?x c d) 'CxUniverse)))
    (is (= #{top} (answers kb (list 'minCommonGenl '?x a b c) 'CxUniverse)))
    (testing "one input type: the bindings are its min-genls"
      (is (= (v/min-genls kb a) (answers kb (list 'minCommonGenl '?x a) 'CxUniverse))))))

(tu/deftest-kb max-common-spec-with-an-open-first-argument-binds-each-maximum
  (with-hierarchy
    (is (= #{a b} (answers kb (list 'maxCommonSpec '?x left right) 'CxUniverse)))
    (is (= #{c d} (answers kb (list 'maxCommonSpec '?x mid top) 'CxUniverse)))
    (is (= #{} (answers kb (list 'maxCommonSpec '?x a c) 'CxUniverse)))))

(tu/deftest-kb a-closed-first-argument-proves-true-or-proves-false
  (with-hierarchy
    (testing "a minimum proves true"
      (is (= :true (:verdict (v/argue kb (list 'minCommonGenl left a b) 'CxUniverse))))
      (is (= :true (:verdict (v/argue kb (list 'maxCommonSpec a left right) 'CxUniverse)))))
    (testing "a common genl that is not minimal proves false, not unknown"
      (is (= :false (:verdict (v/argue kb (list 'minCommonGenl top a b) 'CxUniverse))))
      (is (v/ask? kb (list 'not (list 'minCommonGenl top a b)) 'CxUniverse)))
    (testing "a type that is no common genl at all proves false"
      (is (= :false (:verdict (v/argue kb (list 'minCommonGenl mid a b) 'CxUniverse))))
      (is (= :false (:verdict (v/argue kb (list 'maxCommonSpec c left right) 'CxUniverse)))))))

(tu/deftest-kb the-predicates-read-the-edges-the-asking-context-sees
  (with-hierarchy
    (tu/with-terms [CxSide side_kind]
      (v/assert kb (list 'genlCx CxSide 'CxUniverse) 'CxUniverse)
      (edges! kb 'CxUniverse [[side_kind 'thing]])
      (edges! kb CxSide [[a side_kind] [b side_kind]])
      (is (= #{left right side_kind} (answers kb (list 'minCommonGenl '?x a b) CxSide)))
      (is (= #{left right} (answers kb (list 'minCommonGenl '?x a b) 'CxUniverse)))
      (is (= :true (:verdict (v/argue kb (list 'minCommonGenl side_kind a b) CxSide))))
      (is (= :false (:verdict (v/argue kb (list 'minCommonGenl side_kind a b) 'CxUniverse)))))))

(tu/deftest-kb the-predicates-are-declared-variable-arity-and-are-not-assertible
  (with-hierarchy
    (doseq [p '[minCommonGenl maxCommonSpec]]
      (testing (str p)
        (is (v/ask? kb (list 'variable_arity_predicate p) 'CxUniverse))
        (is (v/ask? kb (list 'arityMin p 2) 'CxUniverse))
        (is (:enforced (v/interpreted p)))
        (let [e (try (v/assert kb (list p top a b) 'CxUniverse)
                     nil
                     (catch clojure.lang.ExceptionInfo e e))]
          (is (= :not-well-formed (:type (ex-data e))))
          (is (str/includes? (str (ex-message e)) (str p " is not assertible"))))))))

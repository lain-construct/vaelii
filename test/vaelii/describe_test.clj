;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.describe-test
  "`describe` over the shipped schema and the test-world's cast: what can I ask about
  this term?

  The question a reader arriving at a term actually has is answered by a dozen separate
  reads — `genls`, `props`, `inverse-of`, the argument declarations, the extent counts —
  and the risk in assembling them is not that one of them is wrong but that the
  *assembly* is: a predicate described as a type, a declaration reported from a context
  the reader cannot see, a window shown without its size.  So the tests here are about
  the assembly.

  The one that matters most is the **scoping**: an `arg` declaration binds a predicate's
  arguments only for a reader whose context sees the declaration, so `describe` at
  `CxCore` and at `CxWell` are two different answers about one predicate and both are
  right.  A `describe` that read the whole KB would answer the second everywhere, and
  every context-scoped vocabulary would look global."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :once (tu/loaded (fn [kb] (-> kb starter/load-into world/load-into))))
(use-fixtures :each (tu/neutral))

(def ^:private N 'CxNaturalWorld)
(def ^:private W 'CxWell)

;; ---- one shape per role -------------------------------------------------

(tu/deftest-kb a-predicate-is-described-by-what-binds-its-arguments
  (let [d (v/describe kb 'parentOf W)]
    (testing "it is a predicate, and the KB says how long a parentOf sentence is"
      (is (= :predicate (:role d)))
      (is (= 2 (:arity d))))
    (testing "both argument positions are declared, and each declaration says where"
      (is (= '[(arg parentOf 1 animal) (arg parentOf 2 animal)]
             (mapv :sentence (:arg-declarations d))))
      (is (every? #(= :arg (:kind %)) (:arg-declarations d)))
      (is (every? #(symbol? (:context %)) (:arg-declarations d))))
    (testing "the inverse the KB declares"
      (is (= 'childOf (:inverse d))))
    (testing "the four grants are answered, and none of them is given here"
      (is (false? (:abducible? d)))
      (is (false? (:modal? d)))
      (is (false? (:closed-extent? d)))
      (is (false? (:decontextualized? d))))
    (testing "and the KB's own comment on it"
      (is (seq (:comment d)))
      (is (every? string? (:comment d))))))

(tu/deftest-kb a-predicates-algebraic-properties-are-the-ones-it-carries
  (testing "an ancestor relation is transitive and says so"
    (is (contains? (:props (v/describe kb 'ancestorOf W)) :transitive)))
  (testing "a sibling relation is symmetric"
    (is (contains? (:props (v/describe kb 'siblingOf W)) :symmetric)))
  (testing "a parent relation is neither"
    (is (empty? (:props (v/describe kb 'parentOf W))))))

(tu/deftest-kb a-type-is-described-by-what-it-is-under-and-what-it-rules-out
  (let [d (v/describe kb 'dog W)]
    (testing "the taxonomy overrides the spelling: `dog` is a unary predicate and a type,
             and a reader asking about it means the type"
      (is (= :type (:role d))))
    (testing "its supertypes, up the genl chain, reflexively minus itself"
      (is (contains? (set (:terms (:genls d))) 'animal))
      (is (not (contains? (set (:terms (:genls d))) 'dog))))
    (testing "what it is disjoint from"
      (is (contains? (set (:terms (:disjoint d))) 'cat)))
    (testing "and how many instances are stored"
      (is (pos? (:instance-count d))))))

(tu/deftest-kb a-type-names-the-predicates-whose-declarations-admit-it
  ;; The question behind it: I have a `dog`, what may I say about one?  A predicate
  ;; admits it when some `arg` / `genlArg` declaration names a type `dog` is under, so
  ;; the answer is read off the declarations' own argument root rather than by trying
  ;; every predicate in the KB against it.
  ;; `dog` sits under five types between them declaring well over fifty positions, so the
  ;; default window is a window: the limit is raised here to ask about the whole answer
  ;; rather than about the first page of it.
  (let [line (:predicates-for-type (v/describe kb 'dog W {:limit 500}))
        rows (:rows line)
        of   (fn [p] (filter #(= p (:predicate %)) rows))
        up   (set (:terms (:genls (v/describe kb 'dog W))))]
    (testing "a relation declared over animals admits a dog"
      (is (seq (of 'parentOf)))
      (is (= #{1 2} (set (map :position (of 'parentOf))))))
    (testing "each row says which declared type let it in, and that type is one of dog's"
      (is (every? #(contains? up (:type %)) (of 'parentOf))))
    (testing "the list is a window with its size beside it"
      (is (contains? line :total))
      (is (true? (:exact? line))))
    (testing "and the default window really is one on this term"
      (let [d (:predicates-for-type (v/describe kb 'dog W))]
        (is (= 50 (count (:rows d))))
        (is (> (:total d) 50))))))

(tu/deftest-kb an-individual-is-described-by-its-types-and-where-it-is-mentioned
  (let [d (v/describe kb 'Muffet N)]
    (testing "an individual, by the spelling and by the taxonomy alike"
      (is (= :individual (:role d))))
    (testing "the types asserted of it — not their supertypes"
      (is (contains? (set (:types d)) 'dog))
      (is (not (contains? (set (:types d)) 'animal))))
    (testing "the predicates it appears under, with a count each"
      (let [rows (:rows (:predicates d))
            n    (into {} (map (juxt :predicate :count)) rows)]
        (is (= 1 (n 'dog)))
        (is (pos? (n 'eats)))
        (is (every? pos? (vals n)))))
    (testing "the row list is exact when the scan did not bite"
      (is (true? (:exact? (:predicates d)))))))

(tu/deftest-kb a-context-is-described-by-what-it-sees-and-what-sees-it
  (let [d (v/describe kb 'CxKinship W)]
    (is (= :context (:role d)))
    (testing "its up-cone holds the contexts it reads, reflexively"
      (is (contains? (set (:terms (:up d))) 'CxKinship))
      (is (contains? (set (:terms (:up d))) 'CxCore)))
    (testing "its down-cone holds the contexts that read it"
      (is (contains? (set (:terms (:down d))) 'CxWell)))
    (testing "and how many sentexes hold in it"
      (is (pos? (:sentex-count d))))
    (testing "a context nobody computed carries no computed-spec-of key at all"
      (is (not (contains? d :computed-spec-of))))))

;; ---- the scoping, which is the whole point ------------------------------

(tu/deftest-kb an-argument-declaration-is-reported-only-where-the-reader-can-see-it
  ;; `(arg parentOf 1 animal)` is stated in the upper band; `CxCore` sits above it and
  ;; sees nothing below.  A `describe` that read the whole KB would report the
  ;; declaration to a reader for whom it does not bind, which is the failure this
  ;; scoping exists to stop — and it is invisible from the answer, since a declaration
  ;; reported is a declaration that looks like it applies.
  (testing "a reader below the declaration sees it"
    (is (= 2 (count (:arg-declarations (v/describe kb 'parentOf W))))))
  (testing "a reader above it does not"
    (is (empty? (:arg-declarations (v/describe kb 'parentOf 'CxCore)))))
  (testing "and the unscoped read sees every context's"
    (is (= 2 (count (:arg-declarations (v/describe kb 'parentOf '?ctx)))))))

(tu/deftest-kb a-grant-is-a-policy-of-the-context-that-gives-it
  ;; `modalPredicate` and `abduciblePredicate` are grants read up the genlCx cone, so a
  ;; predicate granted in one theory is not granted in a sibling.  Net-neutral: the
  ;; grant is asserted on a temporary in a temporary context and retracted with it.
  (tu/with-terms [thinks CxGrantA CxGrantB]
    (v/assert kb (list 'genlCx CxGrantA 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxGrantB 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'binaryPredicate thinks) 'CxUniverse)
    (v/assert kb (list 'modalPredicate thinks) CxGrantA)
    (is (true?  (:modal? (v/describe kb thinks CxGrantA))))
    (is (false? (:modal? (v/describe kb thinks CxGrantB))))))

;; ---- the envelopes ------------------------------------------------------

(tu/deftest-kb every-list-is-a-window-that-says-how-big-the-answer-is
  (let [d (v/describe kb 'thing W {:limit 3})]
    (testing "the window is the limit, and the total is the whole answer"
      (is (<= (count (:terms (:specs d))) 3))
      (is (> (:total (:specs d)) 3)))
    (testing "a windowed answer still says whether the count is exact and sorted"
      (is (true? (:exact? (:specs d))))
      (is (true? (:sorted? (:specs d)))))))

(tu/deftest-kb a-window-nothing-reads-is-refused-rather-than-dropped
  ;; The silent failure a roster exists to stop: `{:limt 3}` would answer the default
  ;; fifty under a map that looks exactly like the one asked for.
  (is (= :unknown-option
         (try (v/describe kb 'dog W {:limt 3})
              (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))))
  (is (= v/describe-opt-keys #{:limit})))

(tu/deftest-kb a-spelling-that-declares-no-role-answers-the-common-shape-and-no-more
  (let [d (v/describe kb '?x W)]
    (is (= :variable (:role d)))
    (is (contains? d :genls))
    (is (not (contains? d :arity)))
    (is (not (contains? d :types)))))

;; ---- what the browser renders is what this answers ----------------------

(tu/deftest-kb the-default-limit-is-the-one-the-term-page-lists-with
  ;; The term page reads `describe`'s windows straight through and applies no cap of its
  ;; own, so the two agreeing is not a coincidence to be preserved by hand: the page
  ;; shows exactly what this answered, `:total` and all.
  (is (= 50 v/default-describe-limit))
  (is (= 50 (count (:terms (:specs (v/describe kb 'thing W)))))))

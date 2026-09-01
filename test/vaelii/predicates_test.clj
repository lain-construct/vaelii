;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.predicates-test
  "That `vaelii.impl.predicates` says what the engine already does.

  The declaration namespace began as a claim about twenty-odd rosters it did not feed,
  and these tests were the only honest proof its population was right before a single
  consumer moved.  Consumers have moved since — `taxonomy`'s three rosters,
  `spec/::prop-kind`, `vocabulary/roster` and `settle`'s eight — so the tests come in
  **two kinds**, and which kind a roster gets is decided by whether it has moved.  One
  still written by hand is **reconstructed** from the declaration and asserted equal to
  itself, which is what says a consumer switching over later cannot change behaviour.
  One that has moved states its **value** as a literal instead: reconstructing a derived
  var proves the wiring and nothing about what it holds.

  **Six facets are reconstructible and four are claims.**  `:cached`, `:derived`,
  `:migrates`, `:arbitrable`, `:reach` and `:query-only` each have a data structure in
  the tree stating them, and are pinned below against it.  `:answers`, `:retriggers`,
  `:convicts` and `:inert` have none — a prover's `applicable?` is per-prover code over
  goal shape, a re-check posting is a line inside an arm, and being read by nothing is
  the absence of code rather than any of it.  Those four are exactly the ones that go
  wrong quietly, which is why the facet validator exists; here they are checked only for
  being drawn from the closed vocabulary.

  No KB is involved, so no fixture is either."
  (:require [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.test :refer [deftest is testing]]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.predicates :as pr]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.spec :as vspec]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.vocabulary :as vocab]))

(def ^:private table-functors (into #{} (map first) special/entries))

(defn- live
  "The functors `special/entries` gives arm `k`, as a set."
  [k]
  (into #{} (comp (filter #(get (second %) k)) (map first)) special/entries))

;; ---- the table the whole design is modelled on ---------------------------

(deftest the-declaration-reconstructs-the-special-table
  ;; `special/entries` is a **join** now: the functor list, its order, each `:prop` kind
  ;; and each `:derived?` are read off the declaration, and `special/check-declarations`
  ;; refuses a `:cached` or `:checked` disagreement at namespace load.  So what this
  ;; deftest proves has changed from what the values *are* to that the join is wired to
  ;; them — the same thing `special-table-test/the-live-table-passes-its-own-check`
  ;; proves about `check-entries`, and it fails the same way, on a refactor that stops
  ;; routing the table through the declaration.
  ;;
  ;; What the values are is `special-table-test/frozen-table`, which is a literal
  ;; precisely because nothing here can state it any more.
  (testing "the same functors, and nothing else"
    (is (= table-functors pr/in-special-table)
        "a functor in one and not the other is a hole in the population"))
  (testing "in the same order — rebuild-taxonomy replays the table top to bottom and a
            rebuild arm may read what an earlier one wrote, so the order is content"
    (is (= (mapv first special/entries)
           (filterv table-functors (mapv first pr/entries)))))
  (testing ":cached is the integrate/disintegrate/rebuild triple"
    ;; one arm is enough to test for: `check-entries` refuses a partial triple at
    ;; namespace load, so having the add arm and having all three are the same fact
    (is (= (live :integrate) pr/cached))
    (is (= (live :disintegrate) pr/cached))
    (is (= (live :rebuild) pr/cached)))
  (testing ":derived is the flag that also runs the arm on the derivation path"
    (is (= (live :derived?) pr/derived)))
  (testing ":checked is the structural well-formedness arm"
    (is (= (live :wff) pr/checked)))
  (testing "every :cached term names a storage kind, and no other term does"
    (is (= pr/cached
           (into #{} (comp (remove #(= [:none] (:storage (second %)))) (map first))
                 pr/entries)))))

;; ---- the taxonomy's three rosters ----------------------------------------

(deftest the-declaration-reconstructs-the-taxonomy-rosters
  (testing "the prop kinds a declaration maintains are the ones the table marks"
    (is (= (into {} (comp (filter #(:prop (second %)))
                          (map (fn [[f spec]] [f (:prop spec)])))
                 special/entries)
           (pr/by-storage :prop))))
  (testing "…and are exactly what ::prop-kind admits — the spec is this field read back,
            generated rather than written, so the two cannot say different things"
    (is (every? #(s/valid? ::vspec/prop-kind %) (pr/prop-kinds)))
    (is (not (s/valid? ::vspec/prop-kind :declares-max-cardinality))))
  ;; The three rosters below are *read off* the declaration now, so a test that derives
  ;; them from it and compares proves the wiring and nothing about the values.  Each
  ;; therefore states its value as a literal first — small enough to write out, and the
  ;; only place left that says what it is — and pins the derivation second, which is what
  ;; fails on a refactor that stops routing the var through `predicates`.
  (testing "the argument constraints' subject props"
    (is (= '{arg :declares-arg-isa, genlArg :declares-arg-genl,
             quotedArg :declares-quoted-arg, interArg :declares-inter-arg-isa}
           tax/arg-declaration-props))
    (is (= tax/arg-declaration-props
           (select-keys (pr/by-storage :prop) (pr/family :argument-constraint)))))
  (testing "the functional family, spellings and written shapes both"
    (is (= '{functional :mark, functionalInArg :mark-in-arg} tax/functional-family-marks))
    (is (= tax/functional-family-marks (pr/by-family :functional))))
  (testing "the two cached closures are the only :edge storage"
    (is (= '#{genl genlCx} tax/closure-relations))
    (is (= tax/closure-relations (set (keys (pr/by-storage :edge)))))))

;; ---- the merge and arbitration rosters -----------------------------------

(deftest the-declaration-reconstructs-the-belief-rosters
  (testing ":migrates is the set of relations whose own assertion is a merge"
    (is (= kb/equality-predicates (pr/by-facet :migrates))))
  (testing ":arbitrable, read as the violation kind each names, is checks/arbitrable-kinds"
    ;; A `:pred-position` declaration is a *generalization* of a mark off its fixed slot,
    ;; so its breach carries the mark's kind rather than one of its own: a
    ;; `functionalInArg` violation is a `:functional` violation, arbitrated identically,
    ;; and holds no keyword of its own. Every other arbitrable term stores under the
    ;; keyword its violation is named by.
    (is (= checks/arbitrable-kinds
           (into #{} (comp (filter #(contains? (:facets (second %)) :arbitrable))
                           (remove #(= :pred-position (first (:storage (second %)))))
                           (map #(second (:storage (second %)))))
                 pr/entries)))
    (is (= '#{functionalInArg}
           (into #{} (comp (filter #(contains? (:facets (second %)) :arbitrable))
                           (filter #(= :pred-position (first (:storage (second %)))))
                           (map first))
                 pr/entries))
        "the one arbitrable spelling that takes its kind from the mark it generalizes")))

(deftest the-declaration-reconstructs-the-reach-rosters
  ;; `clash-declaration-functors` is `clash-declaration-kinds`' functors, which are the
  ;; terms carrying a `:sweeps` kind — so this reads the declaration on both sides and is
  ;; about the *facet*: which terms settle sweeps for, against which terms claim to reach
  ;; at all.  The values themselves are pinned in the test below.
  (let [clash (set (keys (pr/sweeps)))]
    (testing "every functor settle sweeps for is declared :reach"
      (is (set/subset? clash (pr/by-facet :reach))))
    (testing "and the terms that reach some *other* way are named, because :reach is one
              facet over three mechanisms"
      ;; `arity` and the three predicate-type memberships — the second way to write an
      ;; arity — reach through `settle/report-arity-reach!`, which *names* the facts a
      ;; late declaration convicts and moves no belief, deliberately: the arity table
      ;; follows belief, so a nogood that defeated the declaration would destroy its own
      ;; premise. The argument constraints reach through `special/entail-existing`, which
      ;; *mints* rather than convicting, being open-world, and is gated on
      ;; `checks/*assertive-arg-types?*`.
      (is (= (into '#{arity arg genlArg interArg} (keys checks/predicate-type-arities))
             (set/difference (pr/by-facet :reach) clash))))))

(deftest the-declaration-writes-settles-three-questions
  ;; The three rosters `settle` no longer writes.  Each states its **value** as a literal
  ;; rather than reconstructing it: the vars are derived now, so rebuilding one from the
  ;; declaration would prove the wiring and nothing about what it holds, and a roster that
  ;; comes out one functor short is a pair that stops being reported in one arrival order
  ;; with no other test necessarily seeing it (`declaration-implicates`: the sweep is the
  ;; only route in).
  (testing "which prop keyword each definitional mark stores under"
    (is (= '#{[asymmetric :asymmetric] [functional :functional]
              [anti_transitive :anti-transitive]}
           (set @#'settle/definitional-marks))
        "as a set: the vector's order is entries' order and is read by nobody"))
  (testing "what each declaration's arrival puts back in question"
    (is (= '{:both             #{genl}
             :type-separating  #{genlCx disjoint disjoint_metatype sibling_disjoint}
             :predicate-marked #{functional asymmetric anti_transitive functionalInArg}}
           @#'settle/clash-declaration-kinds)))
  (testing "and what arity each trigger is written at"
    (is (= '{genl :edge, genlCx :edge, functional :mark, asymmetric :mark,
             anti_transitive :mark, functionalInArg :mark-in-arg}
           @#'settle/trigger-functor-kind)))
  (testing "the five derived beside them, which stay derived one step further back"
    (is (= '#{functional asymmetric anti_transitive} @#'settle/definitional-mark-symbols))
    (is (= '#{:functional :asymmetric :anti-transitive} @#'settle/definitional-mark-keywords))
    (is (= '#{genl genlCx disjoint disjoint_metatype sibling_disjoint
              functional asymmetric anti_transitive functionalInArg}
           @#'settle/clash-declaration-functors))
    (is (= '#{genl genlCx disjoint disjoint_metatype sibling_disjoint}
           @#'settle/type-reach-functors)
        "the reach over terms, which is :type-separating and :both and not the marks")
    (is (= '{genl :both, genlCx :type-separating, disjoint :type-separating,
             disjoint_metatype :type-separating, sibling_disjoint :type-separating,
             functional :predicate-marked, asymmetric :predicate-marked,
             anti_transitive :predicate-marked, functionalInArg :predicate-marked}
           @#'settle/clash-declaration-kind))))

(deftest a-family-spelling-wired-into-one-lane-does-not-load
  ;; The load check itself, driven — `every-functional-family-mark-is-in-both-of-settles-
  ;; rosters` in `exposure_test` asserts the same thing about the real declarations, and
  ;; only fails if this mechanism works.  Both stay until the facet validator subsumes
  ;; them.
  (let [check   @#'pr/check-families
        refusal (fn [entries] (try (check entries) nil
                                   (catch clojure.lang.ExceptionInfo e (ex-data e))))]
    (is (= pr/entries (check pr/entries)) "the real table passes and comes back unchanged")
    (testing "#54 itself: one spelling reaches stored content and the other does not"
      (let [data (refusal '[[functional {:family :functional :sweeps :predicate-marked
                                         :shape {:args [:predicate]}}]
                            [functionalInArg {:family :functional
                                              :shape {:args [:predicate :position]}}]])]
        (is (= :bad-table-entry (:type data)))
        (is (= :family (:mismatch data)))))
    (testing "and a declaration no trigger can recognize at an arity"
      (let [data (refusal '[[functional {:family :functional :sweeps :predicate-marked}]])]
        (is (= :bad-table-entry (:type data)))
        (is (= :sweeps (:mismatch data)))))))

(deftest the-terms-that-convict-with-no-retroactive-half-are-exactly-three
  ;; The facet validator's rule is that a term convicting at the door and nowhere behind
  ;; it decides by arrival order. Three terms break it today. This pins the set rather
  ;; than the rule, because whether each is a defect or a documented open-world non-reach
  ;; is a question about the engine and not about the declaration — but a *fourth* one
  ;; appearing is a regression either way, and that is what fails here.
  (is (= '#{quotedArg instance_relation_predicate type_relation_predicate}
         (set/difference (pr/by-facet :convicts) (pr/by-facet :reach))))
  (testing "and each says in its own entry what is unresolved about it"
    (doseq [t (set/difference (pr/by-facet :convicts) (pr/by-facet :reach))]
      (is (:notes (pr/entry t))))))

;; ---- the query operators -------------------------------------------------

(deftest the-declaration-reconstructs-the-query-only-set
  (testing "the aggregates are query-only, all five, and take one shape"
    (is (set/subset? (set (keys sx/aggregate-functors)) pr/query-only))
    (is (= 1 (count (set (map pr/shape-of (keys sx/aggregate-functors)))))
        "one prover answers all five because they are one shape"))
  (testing "a query-only term is refused at the door and caches nothing"
    (doseq [t pr/query-only]
      (is (contains? pr/checked t) (str t " must carry the refusal arm"))
      (is (not (contains? pr/cached t)) (str t " must cache nothing"))
      (is (= [:none] (:storage (pr/entry t))) (str t " must name no storage")))))

;; ---- the population ------------------------------------------------------

(deftest the-population-is-the-grammar
  ;; The first of these is true by construction now — `vocabulary/roster` is the entries
  ;; carrying `:enforced` or `:inert` prose, so its keys cannot fail to be declared here.
  ;; It stays as the statement that the roster is still that read: a refactor putting the
  ;; prose back in a list of its own fails here rather than passing quietly.  What the
  ;; population actually rests on is `vocabulary_audit_test`, which asks CxCore.
  (testing "every term CxCore's roster answers for is declared here"
    (is (empty? (remove pr/table (keys vocab/roster)))))
  (testing "every functor the special table interprets is declared here"
    (is (empty? (remove pr/table table-functors))))
  (testing "and nothing else is — the population is the grammar, not the KB"
    (is (empty? (remove (into (set (keys vocab/roster)) table-functors)
                        (keys pr/table)))))
  (testing "no term is declared twice"
    (is (= (count pr/entries) (count pr/table)))))

;; ---- the vocabularies are closed -----------------------------------------

(deftest every-field-is-drawn-from-its-closed-vocabulary
  (doseq [[term spec] pr/entries]
    (testing (str term)
      (is (set/subset? (:facets spec) pr/facets)
          "a facet outside the vocabulary is a roster again, with none of the checking")
      (is (contains? pr/storage-kinds (first (:storage spec))))
      (is (or (nil? (:family spec)) (contains? pr/mark-families (:family spec))))
      (when-let [{:keys [args optional variadic]} (:shape spec)]
        (is (set/subset? (set (concat args optional (when variadic [variadic])))
                         pr/argument-kinds))))))

(deftest a-term-that-is-never-a-sentence-functor-has-no-shape
  (testing "a collection's membership shape is not per-term data, so it holds none"
    (doseq [[term spec] pr/entries :when (nil? (:shape spec))]
      (is (= [:none] (:storage spec)) (str term " caches nothing"))
      (is (not (contains? pr/checked term))
          (str term " has no sentence to check the structure of")))))

(deftest the-inert-terms-are-inert-in-every-lane
  (testing "nothing reads them, so they carry that facet and no other"
    (doseq [t (pr/by-facet :inert)]
      (is (= #{:inert} (:facets (pr/entry t))))
      (is (:inert (vocab/roster t))
          (str t " is called inert here and must be called inert there too")))))

(deftest the-vocabulary-answer-is-one-answer
  ;; `vocabulary/roster` reads the *class* off `:facets` and the prose off whichever key
  ;; it was written under, so the two must not be able to say different things.  The
  ;; `inert` constructor is what holds them together — it writes the facet with the prose
  ;; — and this is what fails if an entry is ever assembled without it.
  (doseq [[term spec] pr/entries]
    (testing (str term)
      (is (not (and (:enforced spec) (:inert spec)))
          "a term is enforced or inert, never both")
      (is (= (boolean (:inert spec)) (contains? (:facets spec) :inert))
          "the :inert prose and the :inert facet are one decision, not two")))
  (testing "and the roster is exactly the entries carrying prose — the wiring, since what
            the prose says is now only written here"
    (is (= (set (keys vocab/roster))
           (into #{} (comp (filter #(or (:enforced (second %)) (:inert (second %))))
                           (map first))
                 pr/entries)))))

;; ---- what the rest of the tree already knows ------------------------------

(deftest the-declaration-agrees-with-the-provers-and-inherit
  (testing "the closure relations answer their own transitivity"
    (is (= provers/transitive-predicates (set (keys (pr/by-storage :edge))))))
  (testing "the two preservation declarations are read back rather than cached"
    (doseq [t (keys inherit/declarations)]
      (is (= [:none] (:storage (pr/entry t))))
      (is (contains? (:facets (pr/entry t)) :answers))))
  (testing "the evaluable predicates answer and store nothing"
    (doseq [t provers/evaluable-predicates]
      (is (contains? (:facets (pr/entry t)) :answers))
      (is (= [:none] (:storage (pr/entry t)))))))

;; ---- the notes are findings ----------------------------------------------

(deftest a-note-names-a-lane-the-facet-vocabulary-does-not-reach
  ;; A note is the record of a term doing something no facet covers, so it is the
  ;; backlog the facet validator will work through — not prose to accumulate.  Pinning
  ;; the count keeps a note from being added silently as an alternative to a facet.
  (let [noted (into #{} (comp (filter #(:notes (second %))) (map first)) pr/entries)]
    (is (seq noted))
    (testing "every term the vocabulary calls inert carries one, since :inert is a
              decision and a decision has a reason"
      (is (set/subset? (pr/by-facet :inert) noted)))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.ontology-test
  "The shipped ontology as a *modelling* claim, where `starter-test` reads it as a schema
  that loads and reasons.

  What is pinned here is the structure of the mini-ontology rather than any one inference:
  which names are types and which are properties, that every type is placed under the
  root, that a capability is related to a kind rather than spelled as a predicate of its
  own, and how a claim about a kind reaches the kinds beneath it and stops where a nearer
  claim contradicts it.  Those are decisions somebody made, and every one of them is
  invisible to a test that only asks whether the KB answers a question.

  The genl-level exception is the centre of it.  A rule states its exception with
  `exceptWhen` (docs/exceptions.md); an *inherited* claim has no rule to except, and is
  stopped instead by a more specific claim — which works only for a default, never for a
  monotonic one, and both halves of that are tested because the asymmetry is the design."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.io.text :as text]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :once (tu/loaded (fn [kb] (-> kb tu/load-starter! world/load-into))))
(use-fixtures :each (tu/neutral))

(def ^:private B 'CxBiology)
(def ^:private N 'CxNaturalWorld)

;; ---- capabilities are related to a kind, not spelled as predicates -------

(tu/deftest-kb a-capability-is-a-noun-related-to-a-kind
  ;; `flies` as a one-place predicate says the same thing, and says it in a shape that
  ;; cannot be generalized: every further ability needs a further predicate, and nothing
  ;; relates them.  As a capability it is a term, so the abilities form a hierarchy.
  (testing "the capability names a kind of its own, under capability"
    (is (v/genl? kb 'flying 'capability))
    (is (v/genl? kb 'travelling 'capability))
    (is (v/genl? kb 'flying 'travelling)))
  (testing "and no one-place flight predicate survives beside it"
    (is (empty? (v/sentexes-matching kb '(arity flies ?n) '?ctx)))
    (is (empty? (v/sentexes-matching kb '(arity can_travel ?n) '?ctx)))))

(tu/deftest-kb what-a-kind-can-do-reaches-the-kinds-beneath-it
  ;; One sentence is stored.  Everything else here is the taxonomy being read.
  ;; `capabilityType`, not `hasCapability`: this is the kind talking, and the two readings
  ;; are two predicates (`the-two-capability-readings-are-two-predicates-and-say-so`).
  (testing "the stated claim"
    (is (v/ask? kb '(capabilityType bird flying) B)))
  (testing "and the kinds nobody wrote anything about"
    (is (v/ask? kb '(capabilityType eagle flying) B))
    (is (v/ask? kb '(capabilityType sparrow flying) B)))
  (testing "inherited rather than stored — one sentex carries all of it"
    (is (empty? (v/sentexes-matching kb '(capabilityType eagle flying) '?ctx))))
  (testing "and it climbs the capability hierarchy: what flies travels"
    (is (v/ask? kb '(capabilityType bird travelling) B))
    (is (v/ask? kb '(capabilityType eagle travelling) B)))
  (testing "answered by transitiveInArgInverse, so the kind level stores no rule's output"
    (is (empty? (v/sentexes-matching kb '(capabilityType bird travelling) '?ctx)))))

(tu/deftest-kb a-nearer-claim-stops-an-inherited-default-at-itself
  ;; The genl-level counterpart of `exceptWhen`.  There is no rule to block here — the
  ;; reach is the taxonomy's — so what stops it is a claim about the nearer kind.
  (testing "the excepted kind"
    (is (not (v/ask? kb '(capabilityType penguin flying) B))))
  (testing "its siblings are untouched, which is what makes this an exception"
    (is (v/ask? kb '(capabilityType eagle flying) B))
    (is (v/ask? kb '(capabilityType crow flying) B)))
  (testing "and the general claim survives being excepted"
    (is (v/ask? kb '(capabilityType bird flying) B))))

(tu/deftest-kb the-exception-is-a-claim-and-not-merely-a-silence
  ;; "Penguins do not fly" is something the KB says, not something it fails to say.  An
  ;; application can query it and argue from it; an absence supports no argument.
  (testing "at the kind"
    (is (seq (v/sentexes-matching kb '(not (capabilityType penguin flying)) '?ctx))))
  (testing "and at the member, by its own rule"
    (is (seq (v/sentexes-matching kb '(not (hasCapability Tweety flying)) N)))))

(tu/deftest-kb a-claim-about-a-kind-does-not-reach-its-members-on-its-own
  ;; The bridge is a rule, written once and deliberately, because "every bird flies" and
  ;; "this bird flies" differ by a quantifier the KB will not guess (typeToInstancePred).
  (testing "the member's flight is derived, and it is a record"
    (is (v/ask? kb '(hasCapability Sam flying) N))
    (is (seq (v/sentexes-matching kb '(hasCapability Sam flying) N))))
  (testing "travelling follows from the hierarchy, not a stored forward-rule conclusion"
    (is (v/ask? kb '(hasCapability Sam travelling) N))
    (is (empty? (v/sentexes-matching kb '(hasCapability Sam travelling) N))
        "answered by transitiveInArgInverse, not stored — no redundant rule"))
  (testing "and the flightless member gets neither"
    (is (not (v/ask? kb '(hasCapability Tweety flying) N)))
    (is (empty? (v/sentexes-matching kb '(hasCapability Tweety travelling) N)))))

(tu/deftest-kb the-two-capability-readings-are-two-predicates-and-say-so
  ;; One symbol read at both levels has to pick one argument check for both, and whichever
  ;; it picks convicts the half it was not written for: `arg … 1 animal` is right for
  ;; `(… Tweety flying)` and wrong for `(… bird flying)`, since a kind is not a member of
  ;; the type it lies under.  So: two predicates, the kind-level one marked, and the pair
  ;; named in prose because the predicate that names pairs cannot take a mixed half.
  (testing "the kind-level half relates kinds, and says so"
    (is (v/ask? kb '(type_relation_predicate capabilityType))))
  (testing "the instance-level half is MIXED — one animal to one capability kind — so it
            carries no relation_kind, and its two positions take different checks"
    (is (not (v/ask? kb '(instance_relation_predicate hasCapability))))
    (is (not (v/ask? kb '(type_relation_predicate hasCapability))))
    (is (v/ask? kb '(arg hasCapability 1 animal)))
    (is (v/ask? kb '(genlArg hasCapability 2 capability))))
  (testing "so the pairing cannot be declared — typeToInstancePred constrains its second
            argument to a marked instance half, and this one is mixed"
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/assert kb '(typeToInstancePred capabilityType hasCapability)
                           'CxLife))))
  (testing "and neither reading answers the other's question"
    (is (not (v/ask? kb '(hasCapability bird flying) B)))
    (is (not (v/ask? kb '(capabilityType Sam flying) N)))))

(tu/deftest-kb every-fact-the-starter-ships-satisfies-the-declarations-it-ships
  ;; The guard the `hasCapability` split existed to install.  A declaration arriving after
  ;; the content it convicts is accepted — that is the open-world reading, and `violations`
  ;; carries no retroactive report for `:arg-type` — so the starter could hold seven facts
  ;; its own checker rejected and nothing said a word.  Loading is not the check; this is.
  ;;
  ;; Facts only.  A rule reaches `check` as its `implies` form and an `exceptWhen` as a
  ;; `sentexHandle` reference, and both are engine-minted encodings rather than anything a
  ;; `.txt` author wrote — `check` reads them out of the rule that gives their variables
  ;; meaning, so convicting them says nothing about the shipped content.
  (let [encoding? (fn [s] (let [s (if (and (seq? s) (= 'not (first s))) (second s) s)]
                            (and (seq? s) (contains? '#{implies exceptWhen} (first s)))))
        facts     (->> (v/terms kb)
                       (mapcat #(v/find-sentexes kb %))
                       (reduce (fn [m sx] (assoc m (:id sx) sx)) {})
                       vals
                       (remove #(some? (:antecedent %)))
                       (remove #(encoding? (:sentence %))))
        guilty  (for [sx    facts
                      :let  [ps (v/check kb (:sentence sx) (:context sx))]
                      :when (seq ps)]
                  [(:sentence sx) (:context sx) (mapv :type ps)])]
    (is (empty? guilty)
        (str "shipped facts their own declarations convict: " (vec guilty)))))

(def ^:private untyped-positions
  "The argument positions of arity **2 and up** that the shipped text contexts leave
  undeclared, each with the reason no `arg` / `genlArg` / `quotedArg` can name it.  A
  position that is not here and not declared fails the test below; a position here that
  gains a declaration fails it too, so the roster stays a list of reasons rather than a
  list of debts.

  A **unary** predicate's one position is exempt as a class and is not rostered — see
  the test."
  (merge
   {'[genl 1]  "predicate specializations: (genlArg genl 1 thing) is false of (genl predicateTypeByArity relationTypeByArity), whose ends are binary predicates"
    '[genl 2]  "the root: (genlArg genl 2 thing) would entail (genl thing thing), refused as irreflexive"}
   ;; the five aggregation operators: a result variable, a census variable, a sentence body
   (into {} (for [op '[agg/count agg/sum agg/avg agg/min agg/max] i [1 2 3]]
              [[op i] "an operator slot — a variable, a variable and a sentence body"]))
   ;; koinii's speech acts name their target as (sentexHandle H) — a mention the engine
   ;; mints with no result type — or carry a proposition; a demand on either would
   ;; convict every meta-sentex the app writes
   (into {} (for [[p i] '[[asserts 2] [queries 2] [answers 2] [answers 3] [justifies 2]
                          [justifies 3] [disputes 2] [endorses 2] [refuse 2] [retracts 2]
                          [votesFor 2] [votesAgainst 2] [notUnderstood 2]]]
              [[p i] "a sentex handle or a proposition, a mention no argument type names"]))))

(deftest every-position-of-a-shipped-arity-above-one-is-typed-or-excused
  ;; Read off the text files rather than a loaded KB, because the claim is about what the
  ;; contexts *write*: an author declaring (arity P n) for n above 1, or a class that
  ;; fixes such an n, owes a type for every one of the n positions — `check` reads only
  ;; what is declared, so an undeclared position admits any term and a bad index or a
  ;; wrong-kinded argument stores clean.  Every kb/*.txt is read, the app's koinii
  ;; contexts included.
  ;;
  ;; **A unary predicate owes nothing here.**  Its one position is its membership, so
  ;; `(arg P 1 T)` says what `(genl P T)` says of the same extent — one per instance
  ;; against one edge — and for the terms the engine interprets the shape in
  ;; `vaelii.impl.predicates` refuses a wrong argument before any declaration is read
  ;; (`(symmetric Fred)` is `:not-well-formed`, not `:arg-type`).  A declaration that
  ;; convicts nothing and mints a record per instance under `*assertive-arg-types?*` is
  ;; not a debt to collect, so the demand stops at arity 2 (docs/argtypes.md).  A unary
  ;; predicate whose position is the only check it has still declares one — the eight
  ;; state predicates in CxLife and CxTime do — and this test does not ask it to.
  (let [files    (->> (file-seq (io/file "resources/kb"))
                      (filter #(.endsWith (.getName ^java.io.File %) ".txt")))
        sents    (mapcat text/read-forms files)
        of       (fn [functors] (filter #(and (seq? %) (contains? functors (first %))) sents))
        arities  (merge (into {} (for [s (of '#{unary_predicate binary_predicate ternary_predicate})]
                                   [(second s) ('{unary_predicate 1 binary_predicate 2 ternary_predicate 3}
                                                (first s))]))
                        (into {} (for [s (of '#{arity})] [(second s) (nth s 2)])))
        declared (set (for [s (of '#{arg genlArg quotedArg}) :when (integer? (nth s 2))]
                        [(second s) (nth s 2)]))
        gaps     (set (for [[p n] arities
                            :when (and (integer? n) (< 1 n))
                            i    (range 1 (inc n))
                            :when (not (declared [p i]))]
                        [p i]))
        excused  (set (keys untyped-positions))]
    (is (seq arities) "the text contexts were found and read")
    (is (empty? (remove excused gaps))
        (str "positions the shipped contexts leave untyped: " (pr-str (sort (remove excused gaps)))))
    (is (empty? (remove gaps excused))
        (str "excused positions that are now declared (drop them from the roster): "
             (pr-str (sort (remove gaps excused)))))))

;; ---- the exception mechanism itself, apart from birds --------------------

(tu/deftest-kb an-inherited-default-is-undercut-and-an-inherited-monotonic-one-is-not
  ;; `transitiveInArg`'s contract in one test, both halves.  A default yields to a nearer
  ;; claim; a monotonic claim does not, because yielding would make a stated certainty
  ;; depend on what else got said, and the strength is exactly the author saying it must
  ;; not.  Two independent hierarchies so neither answer can come from the other.
  (tu/with-terms [carriesLoad pack_animal mule_kind hauler_kind cart_kind]
    (v/assert kb (list 'binary_predicate carriesLoad) 'CxUniverse)
    (v/assert kb (list 'transitiveInArg carriesLoad 1 'genl) 'CxUniverse)
    (v/assert kb (list 'genl pack_animal 'animal) 'CxUniverse)
    (v/assert kb (list 'genl mule_kind pack_animal) 'CxUniverse)
    (v/assert kb (list 'genl hauler_kind 'animal) 'CxUniverse)
    (v/assert kb (list 'genl cart_kind hauler_kind) 'CxUniverse)
    (testing "a default reaches the subkind"
      (v/assert kb (list carriesLoad pack_animal 'Bone1) 'CxUniverse)
      (is (v/ask? kb (list carriesLoad mule_kind 'Bone1) 'CxUniverse)))
    (testing "and a nearer claim stops it there"
      (v/assert kb (list 'not (list carriesLoad mule_kind 'Bone1)) 'CxUniverse)
      (is (not (v/ask? kb (list carriesLoad mule_kind 'Bone1) 'CxUniverse)))
      (is (v/ask? kb (list carriesLoad pack_animal 'Bone1) 'CxUniverse)))
    (testing "a monotonic claim reaches the subkind the same way"
      (v/assert kb (list carriesLoad hauler_kind 'Bone1) 'CxUniverse {:strength :monotonic})
      (is (v/ask? kb (list carriesLoad cart_kind 'Bone1) 'CxUniverse)))
    (testing "and a nearer default does NOT displace it — the general claim still stands"
      (v/assert kb (list 'not (list carriesLoad cart_kind 'Bone1)) 'CxUniverse)
      (is (v/ask? kb (list carriesLoad hauler_kind 'Bone1) 'CxUniverse)
          "the monotonic claim is not undercut, which is inherit/undercut?'s contract"))
    (testing "the disagreement is a dilemma, and asking the subkind answers nothing"
      ;; Both claims survive `undercut?` — the monotonic one because it is known-true,
      ;; the negative one because nothing is more specific than it — so `verdict` sees
      ;; both polarities and returns `:ambiguous`, which `ask?` renders as false.  Not
      ;; the same as the negative winning: the general claim above is still believed.
      (is (not (v/ask? kb (list carriesLoad cart_kind 'Bone1) 'CxUniverse))))
    (testing "and the dilemma is reported, which is what makes it a dilemma and not silence"
      ;; `inherit`'s own docstring calls a contrary specific claim against a monotonic one
      ;; "a contradiction to report rather than a refinement to defer to", and this is
      ;; where it is reported.  The inherited claim has no handle, so the nogood's members
      ;; are the stored claim and everything the reading rests on — the general claim, the
      ;; declaration and the `genl` edge — and `:inherited` carries the claim nobody wrote.
      ;; The mule/pack_animal half above is a `:default` general claim and is undercut, so
      ;; it contributes nothing: one entry, from the monotonic half.
      (let [rs (filter #(= :inherited (:kind %)) (v/contradictions kb))
            r  (first rs)]
        (is (= 1 (count rs)))
        (is (empty? (v/conflicts kb))
            "at :default against :monotonic the pair is a dilemma, not an unsolved clash")
        (is (= (list carriesLoad cart_kind 'Bone1) (:sentence (:inherited r)))
            "the report names the claim that was never stored")
        (is (= (list carriesLoad hauler_kind 'Bone1)
               (:sentence (first (filter #(= (:handle %) (:claim (:inherited r)))
                                         (:sides r)))))
            "and the sentex it was inherited from, by handle")
        (is (contains? (set (map :sentence (:sides r)))
                       (list 'genl cart_kind hauler_kind))
            "and the genl edge it travelled, so `why` can explain the reach")
        (is (contains? (set (map :sentence (:sides r)))
                       (list 'transitiveInArg carriesLoad 1 'genl))
            "and the declaration that licensed the move")))))

;; ---- what is a type, and what is only a property ------------------------

(tu/deftest-kb a-type-is-a-noun-and-a-property-is-not-a-type
  ;; The naming rules make `alive` and `mortal` legal unary predicates, and nothing in
  ;; them says whether a name belongs in the genl hierarchy.  That is a modelling
  ;; decision: a type is a kind of thing and wants a noun, while a property is something
  ;; a thing *is*, and putting one in the hierarchy would make "mortal" a kind that
  ;; organisms are a kind OF.  Were one wanted as a type it would be spelled for it —
  ;; `mortal_being`, not `mortal`.
  (testing "the properties the biology theory concludes are outside the hierarchy"
    (doseq [p '[alive dead awake asleep mortal warm_blooded breathes_air]]
      (is (empty? (v/sentexes-matching kb (list 'genl p '?super) '?ctx))
          (str p " is a property, not a type — it must carry no genl edge"))
      (is (v/isa? kb p 'unary_predicate)
          (str p " is still a one-place predicate"))))
  (testing "while the kinds they are said of are types, and reach the root"
    (doseq [t '[animal bird penguin dog person tangible capability flying]]
      (is (v/genl? kb t 'thing) (str t " must reach thing")))))

(tu/deftest-kb every-shipped-type-is-placed-under-the-root
  ;; An unplaced type is invisible to every closure the engine reads, so it is a type in
  ;; spelling only.  `islands` is the taxonomy's own count of them.
  (let [q (v/kb-quality kb)]
    (is (zero? (:islands (:taxonomy q)))
        "a type with no path to thing answers nothing and is a type in spelling only")
    (is (= (:edged (:taxonomy q)) (:rooted (:taxonomy q)))
        "every name with a genl edge reaches the root")))

(def ^:private type-relating-predicates
  "The predicates whose every argument is a TYPE (or a predicate) the claim relates, so the
  claim is meaningful only in a context that sees all of them at once.  A `genl`, `disjoint`,
  `orthogonal`, `intersection` or `typeGenl` between two members' terms therefore belongs at
  the context
  that sees both — the collector (CxUniverse for the upper spindle), never the head, which
  sees no member (docs/contexts.md, and the rule `resources/kb/CxUniverse.txt`'s own header
  states).

  `arg` / `genlArg` / `quotedArg` / `result` / `interArg` and the relation-metadata marks are
  deliberately NOT here: they constrain a relation's OWN argument or classify the relation
  itself, and the type they name is checked from the DATA context that asserts a tuple — every
  data context sits below the collector and sees the whole upper spindle — so a member
  declaring `(arg parentOf 1 animal)` over CxOrganism's `animal` is checked where it bites and
  is not misplaced."
  '#{genl disjoint typeGenl genlInverse intersection partitionedByType
     covering separating partition orthogonal})

(tu/deftest-kb no-authored-type-relation-names-a-term-its-own-context-cannot-see
  ;; The scoped complement of `every-shipped-type-is-placed-under-the-root`.  That test asks
  ;; whether a type reaches `thing` from SOME context; this one asks whether a claim RELATING
  ;; types (`type-relating-predicates`) is written where every type it names reaches `thing`
  ;; from that same context.  A relating claim written where one side is invisible does not
  ;; separate or subsume the two types in that context, and names a term that context does
  ;; not root.
  ;;
  ;; The spindle is what makes this possible.  CxCore, the head, sees no member
  ;; (docs/contexts.md), so `(typeGenl stuff_type_by_substance substance)` in CxCore over a
  ;; `substance` defined in CxAbstract stores clean — an undeclared symbol cannot violate an
  ;; assert-time check (open-world, docs/taxonomy.md) — and the claim lands in a context that
  ;; cannot read its own subject.  A relation between two members' terms therefore belongs at
  ;; or above the collector that sees both.
  ;;
  ;; Read off the text files the starter actually loads — `CxCore.txt`, `upper/`, `middle/`
  ;; (`vaelii.host.starter`) — because the claim is about what those contexts *write*, not
  ;; what the engine derives or the starter publishes (`(unary_predicate T)` is asserted into
  ;; CxCore for every subtype of `thing`, and the arity rules conclude from those in CxCore
  ;; too; both are deliberate).  A top-level `CxUniverse.txt` is NOT among the loaded files,
  ;; so a relating claim placed there would not be read at all — a separate defect this test
  ;; is not the guard for.  The loaded KB still answers rooting, since `v/genl?` scoped to a
  ;; context is the exact visibility the write side checks against.
  (let [anywhere (fn [t]   (v/genl? kb t 'thing))          ; reaches the root from some context
        rooted?  (fn [t c] (v/genl? kb t 'thing c))        ; reaches it from context c
        up       (memoize (fn [c] (set (v/context-up kb c))))
        homes    (fn [ts]                                  ; most-general contexts rooting every t in ts
                   (let [all (filter (fn [c] (every? #(rooted? % c) ts)) (v/contexts kb))]
                     (filterv (fn [c] (not-any? #(and (not= % c) (contains? (up c) %)) all))
                              all)))
        relating? (fn [s] (and (seq? s) (contains? type-relating-predicates (first s))))
        resolve*  (fn [[form fctx]]                         ; (ist Cx S) writes S into Cx
                    (if (and (seq? form) (= 'ist (first form)))
                      [(nth form 2) (nth form 1)]
                      [form fctx]))
        names    (fn [sentence] (distinct (filter symbol? (tree-seq seq? seq sentence))))
        files    (cons (io/file "resources/kb/CxCore.txt")
                       (filter text/kb-file? (mapcat #(file-seq (io/file (str "resources/kb/" %)))
                                                     ["upper" "middle"])))
        forms    (->> files
                      (mapcat (fn [f] (let [c (text/context-of f)]
                                        (map #(vector % c) (text/read-forms f)))))
                      (map resolve*)
                      (filter (fn [[s _]] (relating? s))))
        blind    (for [[s c] forms
                       :let  [miss (filter #(and (anywhere %) (not (rooted? % c))) (names s))]
                       :when (seq miss)]
                   {:context c :sentence s :cannot-see (vec miss) :move-to (homes (distinct miss))})]
    (is (seq forms) "the shipped context files were found and read")
    (is (empty? blind)
        (str "type relations written where a term they name is invisible — move each to a "
             "context that sees the named types (or root the types at/above the head):\n"
             (apply str (interpose "\n"
                                   (for [b blind]
                                     (str "  " (:context b) " asserts " (pr-str (:sentence b))
                                          "\n    cannot see " (pr-str (:cannot-see b))
                                          " — defined in " (pr-str (:move-to b))
                                          ", so move the assertion there"))))))))

(def ^:private head-terms-one-member-may-keep
  "CxCore inert terms only one spindle member references today, kept in the head on
  purpose — each with the reason.  A term absent from this roster that only one member uses
  fails the test below; a term here that gains a second member user fails it too, so the
  roster stays a list of reasons rather than a list of debts."
  '{capability "the upper-ontology skeleton collection CxLife extends (vaelii.impl.predicates); the head holds it so a member can place a capability under the root"
    denotational_term "the logic sense of `term`, vocabulary the head documents; only CxAbstract links it into the expression lattice today"
    formula "the formula-ladder type the head documents beside the grammar sense; only CxAbstract places it under expression today"
    relation_application "an expression kind the head documents; only CxAbstract places it under expression today"
    typeToInstancePred "a relation-linking predicate the head declares as vocabulary; only CxAbstract uses it (partType / partOf) today"})

(tu/deftest-kb head-vocabulary-a-single-member-uses-belongs-in-that-member
  ;; The inverse of `no-authored-type-relation-names-a-term-its-own-context-cannot-see`.
  ;; CxCore, the head, holds a term because more than one spindle member has to SEE it — a
  ;; member sees the head and not its siblings, so a term two members share lives in the head
  ;; (docs/contexts.md).  A CxCore ontology term that only ONE member ever references does not
  ;; earn that placement: it could live in that member, and holding it in the head widens the
  ;; shared vocabulary for no reader that needs it there.  This names each such term and the
  ;; single member to move it to.
  ;;
  ;; Scope: the INERT vocabulary CxCore declares (`v/vocabulary-audit`'s `:inert`) — the
  ;; ontology terms the engine reads by no name.  An `:enforced` term (a code path reads it by
  ;; name) stays in the head whatever its members, so it is out of scope.  A term no member
  ;; references — used only by CxCore's own structure — is head vocabulary, not a member's, so
  ;; it is not flagged; only a count of exactly one member is.
  ;;
  ;; A term CxCore itself references from another term (a subtype, a disjoint partner, an arg
  ;; type, a rule that names it) cannot move down: the head would then reference a term it
  ;; cannot see.  `core-structural-use?` reads that off the head's own sentexes — the term
  ;; appears as a functor or an argument past the subject (the second element), rather than
  ;; only as the subject of its own declaration — and holds such a term in the head.
  (let [members  (set (map text/context-of
                           (mapcat #(filter text/kb-file? (file-seq (io/file (str "resources/kb/" %))))
                                   ["upper" "middle"])))
        ;; authored use only: a rule's conclusion placed in a member names the term there
        ;; without anybody having written it, and moving the term down would not move it
        users    (fn [t] (distinct (filter members (map :context (filter #(v/premise? kb (:id %))
                                                                         (v/find-sentexes kb t))))))
        core-structural-use?
        (fn [t] (some (fn [sx]
                        (let [s (:sentence sx)]
                          (and (seq? s) (not= 'comment (first s))
                               (some #{t} (cons (first s) (drop 2 s))))))
                      (filter #(= 'CxCore (:context %)) (v/find-sentexes kb t))))
        loners   (for [[t _why] (:inert (v/vocabulary-audit kb))
                       :let  [ms (users t)]
                       :when (and (= 1 (count ms))
                                  (not (core-structural-use? t))
                                  (not (contains? head-terms-one-member-may-keep t)))]
                   {:term t :used-only-by (first ms)})]
    (is (empty? loners)
        (str "CxCore ontology terms only one member uses — move each to that member (or add "
             "it to `head-terms-one-member-may-keep` with a reason):\n"
             (apply str (interpose "\n"
                                   (for [c loners]
                                     (str "  " (:term c) " — used only by " (:used-only-by c)
                                          ", so move it there"))))))))

(tu/deftest-kb every-type-a-loaded-membership-names-is-named-by-another-sentence
  ;; A membership in a type no other sentence names reaches no genl edge, argument
  ;; declaration or comment, so a misspelled or retired type name stores clean and nothing
  ;; reads it.  The starter and the test-world state no such membership.
  (let [membership? (fn [t s] (and (seq? s) (= 2 (count s)) (= t (first s))))
        types       (into #{} (comp (filter #(v/premise? kb (:id %)))
                                    (map :sentence)
                                    (keep #(when (and (seq? %) (= 2 (count %))) (first %)))
                                    (filter symbol?))
                          (v/sentexes-matching kb '(?p ?x) '?ctx))]
    (is (< 50 (count types)) "the reading ran over the loaded memberships")
    (is (= [] (filterv (fn [t] (every? #(membership? t (:sentence %)) (v/find-sentexes kb t)))
                       (sort types))))))

;; ---- the shipped rules, read against each other --------------------------

(tu/deftest-kb no-shipped-rule-is-covered-by-another
  ;; `kb-quality`'s subsumption reading over the shipped schema and the test-world's
  ;; fables.  Zero is the claim: nothing here fires wherever another rule fires and
  ;; concludes no more than it does, so no rule in the ontology is carrying its weight
  ;; only because somebody wrote it twice at two levels of the hierarchy.
  ;;
  ;; The arity generator is the case that tests the claim.  It stamps one rule per
  ;; `relationTypeByArity` fact, and CxCore ships three — over `unary`, `binary` and
  ;; `ternary`.  A `(predicateTypeByArity unary_predicate 1)` fact beside them would
  ;; stamp a fourth firing wherever the first already fires, since `unary_predicate`
  ;; is a `unary`; CxCore states that membership with a `genl` edge instead, so the
  ;; reading stays at zero and a mapping table that grew a redundant member would
  ;; show up here.
  (let [q (:subsumption (v/kb-quality kb {:limit 100}))]
    (is (pos? (:total q)) "the reading ran over rules rather than over nothing")
    (is (not (:truncated? q)) "and over all of them")
    (is (zero? (:subsumed-count q))
        (str "covered: " (pr-str (mapv (juxt :by-sentence :sentence) (:subsumed q)))))))

(tu/deftest-kb a-generated-rule-is-not-exempt-from-the-subsumption-reading
  ;; The reading does not spare a rule for having been stamped by a generator: a
  ;; mapping fact over a type and a second over its subtype mint two rules, and the
  ;; narrower one fires nowhere the broader does not.
  (tu/with-terms [broad_type narrow_type outcome_type generatesType]
    (v/assert kb (list 'genl broad_type 'thing) 'CxCore)
    (v/assert kb (list 'genl narrow_type broad_type) 'CxCore)
    (v/assert kb (list 'genl outcome_type 'thing) 'CxCore)
    (v/assert kb (list 'implies (list generatesType '?type)
                       (list 'implies (list '?type '?x) (list outcome_type '?x))) 'CxCore {:direction :forward})
    (doseq [type [broad_type narrow_type]]
      (v/assert kb (list generatesType type) 'CxCore))
    (let [rule (fn [type] (list 'implies (list type '?x) (list outcome_type '?x)))
          pair [(v/handle-of kb (rule broad_type) 'CxCore)
                (v/handle-of kb (rule narrow_type) 'CxCore)]
          q (:subsumption (v/kb-quality kb {:limit 100}))]
      (is (every? some? pair) "both rules are stamped")
      (is (not (:truncated? q)))
      (is (some #(= pair [(:by %) (:subsumed %)]) (:subsumed q))
          "the narrower generated rule is reported as covered"))))

(tu/deftest-kb every-negated-conclusion-the-ontology-can-clash-with-is-stated-as-an-exception
  ;; The other rule-hygiene reading, and the structure of what it finds here is the finding.
  ;; Every pair whose conclusions contradict outright — a bird's flight against a
  ;; penguin's, wakefulness against sleep, life against death, and the shepherd boy's
  ;; credibility against his lying — is one of the two rules **stating** the other as an
  ;; `exceptWhen`, which is what `:excepted` marks.  Nothing else is left: the arity table
  ;; would be three `:functional` pairs, each two of the classification rules concluding a
  ;; different `(arity ?p n)` for one `?p`, and the three classes are declared pairwise
  ;; `disjoint`, so no `?p` satisfies two antecedents and the pairs are unreachable rather
  ;; than unstated (docs/quality.md).
  ;;
  ;; No `:disjoint` pair is left.  CxCriedWolf's `lied_before → liar` concludes a person,
  ;; and three kinds of rule conclude a type disjoint from one: the signed refinements of
  ;; `integer`, the relation classifications (arity, `bijection`, the arity classes), and
  ;; the membership rule of `(intersection nowhere_never aspatial atemporal)`.  No ground
  ;; term satisfies both antecedents of any such pair — nothing is a person and an integer,
  ;; a relation, or in no space and at no time — and the checker reads that off the
  ;; `arg` declarations: `(arg lied_before 1 person)` types the liar rule's variable a
  ;; `person`, disjoint from what the other rule states or concludes about the same term,
  ;; so `arg-type-conflicted?` drops every such pair as unreachable (vaelii#95).
  (let [pairs (:pairs (:clashes (v/kb-quality kb {:limit 100})))
        kinds (frequencies (map :kind pairs))]
    (is (= {:negation 4} kinds)
        (str "clashes: " (pr-str (mapv (juxt :kind :sentences) pairs))))
    (is (every? :excepted (filter #(= :negation (:kind %)) pairs))
        "negation clashes are excepted")))

(tu/deftest-kb the-arity-rules-clash-with-each-other-in-neither-direction
  ;; The reading's own half of the arity separation.  The generator stamps one rule per
  ;; exact class, and two of them conclude two arities for one relation only where the
  ;; relation holds both classes — which `(disjoint unary binary)` and its two peers
  ;; refuse on the antecedents.  No `?relation` satisfies two of them, so the pair is
  ;; unreachable rather than unstated (docs/quality.md).
  ;;
  ;; `(partition thing tangible intangible)` makes a relation-classification conclusion and a
  ;; story-predicate conclusion disjoint, so the arity rules would pair with CxCriedWolf's
  ;; `lied_before → liar` if the checker read only the conclusions.  It reads the
  ;; antecedents' `arg` declarations too: `(arg arity 1 relation)` types the arity rule's
  ;; variable a `relation`, disjoint from the `person` the paired rule concludes, so
  ;; `arg-type-conflicted?` drops the pair as unreachable (vaelii#95).  The arity table
  ;; therefore pairs with nothing.
  (let [pairs   (:pairs (:clashes (v/kb-quality kb {:limit 100})))
        about   (fn [f] (filter (fn [p] (some #(some #{f} (flatten %)) (:sentences p)))
                                pairs))]
    (is (empty? (about 'arity))
        (str "the arity table pairs with nothing: " (pr-str (mapv :sentences (about 'arity)))))
    (is (empty? (about 'unary_predicate))
        (str "nor do the classes: " (pr-str (mapv :sentences (about 'unary_predicate)))))))

(tu/deftest-kb a-predicate-is-at-most-one-of-the-three-arity-classifications
  ;; The declaration that empties the reading above.  A predicate takes one number of
  ;; arguments, so a second classification is stored as a disjoint clash with the first,
  ;; which the settle weighs.
  (testing "the three pairs are separated, and pairwise — not by a mark on predicate"
    (is (v/disjoint? kb 'unary_predicate 'binary_predicate))
    (is (v/disjoint? kb 'unary_predicate 'ternary_predicate))
    (is (v/disjoint? kb 'binary_predicate 'ternary_predicate))
    (is (not (v/disjoint? kb 'binary_predicate 'instance_relation_predicate))
        "arity is both, so a sibling_disjoint mark on predicate would be too wide"))
  (testing "and the second classification is a clash, in either order"
    (tu/with-terms [zebraOf yakOf]
      (v/assert kb (list 'unary_predicate zebraOf) 'CxUniverse)
      (is (tu/stored-in-clash? kb (list 'binary_predicate zebraOf) 'CxUniverse))
      (v/assert kb (list 'binary_predicate yakOf) 'CxUniverse)
      (is (tu/stored-in-clash? kb (list 'unary_predicate yakOf) 'CxUniverse))))
  (testing "a mark below binary_predicate carries the separation with it"
    (tu/with-terms [emuOf]
      (v/assert kb (list 'functional emuOf) 'CxUniverse)
      (is (tu/stored-in-clash? kb (list 'ternary_predicate emuOf) 'CxUniverse))))
  (testing "belief-filtered: retracting the first frees the second"
    (tu/with-terms [oxOf]
      (let [h (v/assert kb (list 'unary_predicate oxOf) 'CxUniverse)]
        (is (tu/stored-in-clash? kb (list 'ternary_predicate oxOf) 'CxUniverse))
        (v/retract! kb h)
        (is (v/ask? kb (list 'ternary_predicate oxOf) 'CxUniverse))
        (is (not-any? #(some #{(v/handle-of kb (list 'ternary_predicate oxOf) 'CxUniverse)}
                             (:nogood %))
                      (concat (v/contradictions kb) (v/conflicts kb)))))))
  (testing "and scoped: two contexts neither of which sees the other keep both"
    (tu/with-terms [ibisOf CxLeft CxRight CxBelowLeft]
      (v/assert kb (list 'genlCx CxLeft 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxRight 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxBelowLeft CxLeft) 'CxUniverse)
      (v/assert kb (list 'unary_predicate ibisOf) CxLeft)
      (is (v/assert kb (list 'binary_predicate ibisOf) CxRight)
          "neither context sees the other, so both classifications stand")
      (is (tu/stored-in-clash? kb (list 'ternary_predicate ibisOf) CxBelowLeft)
          "the descendant sees the first classification, so the third clashes with it"))))

(tu/deftest-kb a-social-agent-is-a-person-but-not-a-mammal
  ;; The person/human split (#11): `human` is the biological type — a mammal — while
  ;; `person` is the broad class of anything with social agency.  A non-biological agent
  ;; is a person by the genl edge to `person`, and inherits none of the biology, so the
  ;; social predicates constrain their arguments to `person` and still admit it.
  (tu/with-terms [sentientAndroid CmdrData Geordi]
    (v/assert kb (list 'genl sentientAndroid 'person) N)
    (v/assert kb (list sentientAndroid CmdrData) N)
    (v/assert kb (list 'person Geordi) N)
    (testing "the android is a person by the edge to the broad class"
      (is (v/isa? kb CmdrData 'person))
      (is (v/ask? kb (list 'person CmdrData) N)))
    (testing "but not a mammal or an animal — person implies neither any more"
      (is (not (v/isa? kb CmdrData 'mammal)))
      (is (not (v/isa? kb CmdrData 'animal)))
      (is (not (v/ask? kb (list 'mammal CmdrData) N))))
    (testing "so a social relation type-checks between two persons"
      (is (v/assert kb (list 'friendOf CmdrData Geordi) N))
      (is (v/ask? kb (list 'friendOf CmdrData Geordi) N)))
    (testing "while a biological predicate refuses the person that is no organism"
      (is (thrown? clojure.lang.ExceptionInfo
                   (v/assert kb (list 'parentOf CmdrData Geordi) N))))
    (testing "and human, the biological half, reaches mammal, animal and person alike"
      (is (v/genl? kb 'human 'mammal))
      (is (v/genl? kb 'human 'animal))
      (is (v/genl? kb 'human 'person))
      (is (not (v/genl? kb 'person 'mammal))))))

(tu/deftest-kb the-types-added-for-argument-constraints-are-placed-where-they-are-used
  (testing "the two calculi types the argument declarations name"
    (is (v/genl? kb 'tangible 'spatial))
    (is (v/genl? kb 'time_point 'temporal)))
  (testing "and an animal reaches spatial, so a spatial relation admits one"
    (is (v/genl? kb 'dog 'spatial))))

;; ---- the upper divisions by location and by mass --------------------------
;; Two partitions of `thing`.  `spatial` / `aspatial` divides by a location in SOME space —
;; physical space, or a mathematical one, where a line or a square of an abstract board
;; has a location and none in the world.  `tangible` / `intangible` divides by mass.
;; `spatiotemporal` is the intersection of `spatial` and `temporal`: what has a location
;; in space and time.  The spatial calculi relate anything spatial.  A region is the case the
;; two partitions cross on: spatiotemporal, and massless.

(tu/deftest-kb spatiotemporal-is-the-intersection-of-spatial-and-temporal
  (testing "the combined kind is below each of its two types"
    (is (true? (v/genl? kb 'spatiotemporal 'spatial)))
    (is (true? (v/genl? kb 'spatiotemporal 'temporal))))
  (testing "something spatial and temporal is concluded spatiotemporal"
    (tu/with-terms [Puddle]
      (v/assert kb (list 'spatial Puddle) 'CxUniverse)
      (v/assert kb (list 'temporal Puddle) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list 'spatiotemporal Puddle) 'CxUniverse))))))

(tu/deftest-kb a-tangible-thing-is-spatiotemporal-and-so-spatial-and-temporal
  (testing "the type reaches all three"
    (is (true? (v/genl? kb 'tangible 'spatiotemporal)))
    (is (true? (v/genl? kb 'tangible 'spatial)))
    (is (true? (v/genl? kb 'tangible 'temporal))))
  (testing "and an instance carries the memberships"
    (tu/with-terms [Pebble]
      (v/assert kb (list 'tangible Pebble) 'CxUniverse)
      (is (true? (v/ask? kb (list 'spatiotemporal Pebble) 'CxUniverse)))
      (is (true? (v/ask? kb (list 'spatial Pebble) 'CxUniverse)))
      (is (true? (v/ask? kb (list 'temporal Pebble) 'CxUniverse))))))

(tu/deftest-kb an-abstract-figure-is-spatial-without-being-spatiotemporal
  ;; A line in a plane has a location in that plane and none in the world, no mass,
  ;; and no place in time.
  (tu/with-terms [Diagonal]
    (v/assert kb (list 'spatial Diagonal) 'CxUniverse)
    (v/assert kb (list 'atemporal Diagonal) 'CxUniverse)
    (is (not (tu/stored-in-clash? kb (list 'intangible Diagonal) 'CxUniverse))
        "spatial and intangible together are consistent")
    (is (true? (v/ask? kb (list 'spatial Diagonal) 'CxUniverse)))
    (is (true? (v/ask? kb (list 'intangible Diagonal) 'CxUniverse)))
    (is (not (v/ask? kb (list 'spatiotemporal Diagonal) 'CxUniverse))
        "it is not located in space and time")))

(tu/deftest-kb nowhere-never-is-the-intersection-of-aspatial-and-atemporal
  (testing "the combined kind is below each of its two types, and massless"
    (is (true? (v/genl? kb 'nowhere_never 'aspatial)))
    (is (true? (v/genl? kb 'nowhere_never 'atemporal)))
    (is (true? (v/genl? kb 'nowhere_never 'intangible))))
  (testing "an expression and a language are nowhere and never"
    (is (true? (v/genl? kb 'expression 'nowhere_never)))
    (is (true? (v/genl? kb 'language 'nowhere_never)))
    (tu/with-terms [Formula]
      (v/assert kb (list 'expression Formula) 'CxUniverse)
      (is (true? (v/ask? kb (list 'nowhere_never Formula) 'CxUniverse)))))
  (testing "something aspatial and atemporal is concluded nowhere_never"
    (tu/with-terms [Platitude]
      (v/assert kb (list 'aspatial Platitude) 'CxUniverse)
      (v/assert kb (list 'atemporal Platitude) 'CxUniverse)
      (is (seq (v/sentexes-matching kb (list 'nowhere_never Platitude) 'CxUniverse)))))
  (testing "a line in the plane is atemporal and spatial, so it is not"
    (tu/with-terms [Bisector]
      (v/assert kb (list 'spatial Bisector) 'CxUniverse)
      (v/assert kb (list 'atemporal Bisector) 'CxUniverse)
      (is (not (v/ask? kb (list 'nowhere_never Bisector) 'CxUniverse)))
      (is (empty? (v/sentexes-matching kb (list 'nowhere_never Bisector) 'CxUniverse))))))

(tu/deftest-kb spatial-and-aspatial-partition-thing
  (is (true? (v/disjoint? kb 'spatial 'aspatial)))
  (is (true? (v/disjoint? kb 'spatiotemporal 'aspatial))
      "the partition separates spatiotemporal from aspatial through the genl to spatial")
  (is (true? (v/genl? kb 'spatial 'thing)))
  (is (true? (v/genl? kb 'aspatial 'thing)))
  (testing "a thing cannot be both"
    (tu/with-terms [Figment]
      (v/assert kb (list 'spatial Figment) 'CxUniverse)
      (is (true? (tu/stored-in-clash? kb (list 'aspatial Figment) 'CxUniverse)))))
  (testing "and a thing denied a location in any space is aspatial — the coverage half"
    (tu/with-terms [Rumour]
      (v/assert kb (list 'thing Rumour) 'CxUniverse)
      (v/assert kb (list 'not (list 'spatial Rumour)) 'CxUniverse)
      (is (true? (v/ask? kb (list 'aspatial Rumour) 'CxUniverse))))))

(tu/deftest-kb temporal-and-atemporal-partition-thing
  (is (true? (v/disjoint? kb 'temporal 'atemporal)))
  (testing "a thing cannot be both"
    (tu/with-terms [Moment]
      (v/assert kb (list 'temporal Moment) 'CxUniverse)
      (is (true? (tu/stored-in-clash? kb (list 'atemporal Moment) 'CxUniverse)))))
  (testing "and a thing denied a place in time is atemporal — the coverage half"
    (tu/with-terms [Theorem]
      (v/assert kb (list 'thing Theorem) 'CxUniverse)
      (v/assert kb (list 'not (list 'temporal Theorem)) 'CxUniverse)
      (is (true? (v/ask? kb (list 'atemporal Theorem) 'CxUniverse))))))

(tu/deftest-kb tangible-and-intangible-partition-thing
  (is (true? (v/disjoint? kb 'tangible 'intangible)))
  (is (true? (v/genl? kb 'tangible 'thing)))
  (is (true? (v/genl? kb 'intangible 'thing)))
  (testing "a thing cannot be both"
    (tu/with-terms [Boulder]
      (v/assert kb (list 'tangible Boulder) 'CxUniverse)
      (is (true? (tu/stored-in-clash? kb (list 'intangible Boulder) 'CxUniverse)))))
  (testing "and a thing denied mass is intangible — the coverage half"
    (tu/with-terms [Echo]
      (v/assert kb (list 'thing Echo) 'CxUniverse)
      (v/assert kb (list 'not (list 'tangible Echo)) 'CxUniverse)
      (is (true? (v/ask? kb (list 'intangible Echo) 'CxUniverse))))))

(tu/deftest-kb what-has-no-place-in-space-or-time-has-no-mass
  ;; Mass entails a location in space and time, so what lacks either lacks mass.
  (is (true? (v/genl? kb 'aspatial 'intangible)))
  (is (true? (v/genl? kb 'atemporal 'intangible)))
  (tu/with-terms [Prime]
    (v/assert kb (list 'atemporal Prime) 'CxUniverse)
    (is (true? (v/ask? kb (list 'intangible Prime) 'CxUniverse)))
    (is (true? (tu/stored-in-clash? kb (list 'tangible Prime) 'CxUniverse)))))

(def ^:private aspatial-kinds
  "The kinds with no location in any space, each with the contexts that read it as
  aspatial.  `context` and `language` are read from two band contexts besides CxCore:
  their route through `expression` is CxAbstract's, which no band context sees."
  '{attribute     [CxAbstract]
    relation_type [CxAbstract]
    fluent        [CxAbstract]
    capability    [CxCore CxLife]
    organization  [CxAbstract]
    context       [CxCore CxSpace CxSociety]
    language      [CxCore CxSpace CxSociety]})

(tu/deftest-kb a-kind-with-no-location-in-any-space-is-disjoint-from-spatial
  (doseq [[kind ctxs] aspatial-kinds
          ctx         (conj ctxs 'CxUniverse)
          located     '[spatial spatiotemporal]]
    (is (true? (v/disjoint? kb kind located ctx)) (str kind " and " located " in " ctx)))
  (testing "a spatial relation between an attribute and an organization derives two clashes"
    ;; The northOf is stated in CxSpace, whose own declaration mints (spatial X) there;
    ;; CxUniverse sees the mints beside the memberships.  Pinned to the entailing
    ;; reading: the clash sides are the minted (spatial X), which the constraint-only
    ;; reading does not mint.
    (tu/with-entailing
      (tu/with-terms [Redness AcmeCo]
        (v/assert kb (list 'attribute Redness) 'CxUniverse)
        (v/assert kb (list 'organization AcmeCo) 'CxUniverse)
        (v/assert kb (list 'northOf Redness AcmeCo) 'CxSpace)
        (let [clashes (into #{} (comp (filter #(= :disjoint (:kind %)))
                                      (map #(into #{} (map :sentence) (:sides %))))
                            (v/contradictions kb))]
          (is (contains? clashes #{(list 'attribute Redness) (list 'spatial Redness)}))
          (is (contains? clashes #{(list 'organization AcmeCo) (list 'spatial AcmeCo)}))))))
  (testing "and a dog stays disjoint from a number and a relation"
    (is (true? (v/disjoint? kb 'dog 'number)))
    (is (true? (v/disjoint? kb 'dog 'relation)))))

(tu/deftest-kb a-region-is-spatiotemporal-and-intangible-at-once
  ;; A region of space has a location and no mass.  Nothing separates intangible from
  ;; spatial or from spatiotemporal, so the pair is consistent.
  (is (not (v/disjoint? kb 'intangible 'spatiotemporal)))
  (is (not (v/disjoint? kb 'intangible 'spatial)))
  (tu/with-terms [Meadow]
    (v/assert kb (list 'spatiotemporal Meadow) 'CxUniverse)
    (is (not (tu/stored-in-clash? kb (list 'intangible Meadow) 'CxUniverse)))
    (is (true? (v/ask? kb (list 'intangible Meadow) 'CxUniverse)))
    (is (true? (v/ask? kb (list 'spatial Meadow) 'CxUniverse)))
    (is (not (v/ask? kb (list 'tangible Meadow) 'CxUniverse)))))

(def ^:private derivable-and-unstated
  "Relations the shipped KB holds without stating them, each with the context that held
  the sentence before it was removed and the route it is derived by instead.  A
  partition installs a genl edge from each part to the whole and separates the parts,
  an intersection installs an edge to each of its types, genl is transitive, and a
  disjointness descends a genl edge — so a stated sentence repeating one of those is not
  written."
  '[[genl aspatial thing CxCore "partition thing spatial aspatial"]
    [disjoint spatiotemporal aspatial CxCore "spatiotemporal genl spatial (intersection); partition thing spatial aspatial"]
    [genl intangible thing CxCore "partition thing tangible intangible"]
    [genl nowhere_never intangible CxCore "nowhere_never genl aspatial genl intangible"]
    [genl nowhere_never aspatial CxCore "intersection nowhere_never aspatial atemporal"]
    [genl nowhere_never atemporal CxCore "intersection nowhere_never aspatial atemporal"]
    [genl capability intangible CxCore "capability genl aspatial genl intangible"]
    [genl attribute intangible CxAbstract "attribute genl aspatial genl intangible"]
    [genl relation_type intangible CxAbstract "relation_type genl aspatial genl intangible"]
    [genl fluent intangible CxAbstract "fluent genl aspatial genl intangible"]
    [genl organization intangible CxAbstract "organization genl aspatial genl intangible"]
    [genl temporal thing CxCore "partition thing temporal atemporal"]
    [genl atemporal thing CxCore "partition thing temporal atemporal"]
    [disjoint temporal atemporal CxCore "partition thing temporal atemporal"]
    [genl spatiotemporal thing CxCore "spatiotemporal genl spatial (intersection), spatial genl thing (partition)"]
    [genl organism tangible CxCore "organism genl biological genl tangible"]
    [genl body_part tangible CxAbstract "body_part genl biological genl tangible"]
    [genl body_part biological CxAbstract "separating biological organism body_part"]
    [disjoint organism substance CxAbstract "organism genl biological; disjoint biological substance"]
    [disjoint substance body_part CxAbstract "body_part genl biological; disjoint biological substance"]
    [genl tangible temporal CxAbstract "tangible genl spatiotemporal genl temporal (intersection)"]
    [disjoint tangible intangible CxAbstract "partition thing tangible intangible"]
    [disjoint attribute tangible CxAbstract "attribute genl aspatial genl intangible; partition thing tangible intangible"]
    [disjoint organization substance CxAbstract "organization genl aspatial genl intangible, substance genl tangible; partition thing tangible intangible"]
    [disjoint language substance CxAbstract "language genl nowhere_never genl aspatial genl intangible, substance genl tangible; partition thing tangible intangible"]
    [disjoint attribute substance CxAbstract "attribute genl aspatial genl intangible, substance genl tangible; partition thing tangible intangible"]
    [disjoint organization animal CxUniverse "organization genl aspatial genl intangible, animal genl organism genl biological genl tangible; partition thing tangible intangible"]
    [genl string intangible CxAbstract "string genl unrepresented_term genl expression genl nowhere_never genl intangible"]
    [genl number intangible CxAbstract "number genl unrepresented_term genl expression genl nowhere_never genl intangible"]
    [genl keyword intangible CxAbstract "keyword genl unrepresented_term genl expression genl nowhere_never genl intangible"]
    [genl boolean intangible CxAbstract "boolean genl unrepresented_term genl expression genl nowhere_never genl intangible"]
    [genl character intangible CxAbstract "character genl unrepresented_term genl expression genl nowhere_never genl intangible"]
    [genl context intangible CxAbstract "context genl expression genl nowhere_never genl intangible"]
    [genl language intangible CxAbstract "language genl nowhere_never genl intangible"]
    [genl building artifact CxAbstract "building genl container genl artifact"]
    [genl asymmetric binary_predicate CxCore "asymmetric genl anti_symmetric genl binary_predicate"]
    [disjoint string predicate CxAbstract "string genl unrepresented_term, predicate genl relation; disjoint unrepresented_term relation"]
    [disjoint number predicate CxAbstract "number genl unrepresented_term, predicate genl relation; disjoint unrepresented_term relation"]
    [disjoint keyword predicate CxAbstract "keyword genl unrepresented_term, predicate genl relation; disjoint unrepresented_term relation"]
    [disjoint boolean predicate CxAbstract "boolean genl unrepresented_term, predicate genl relation; disjoint unrepresented_term relation"]
    [disjoint character predicate CxAbstract "character genl unrepresented_term, predicate genl relation; disjoint unrepresented_term relation"]
    [disjoint glass_stuff stone CxAbstract "disjoint_metatype stuff_type_by_substance"]
    [disjoint metal glass_stuff CxAbstract "disjoint_metatype stuff_type_by_substance"]
    [disjoint metal stone CxAbstract "disjoint_metatype stuff_type_by_substance"]
    [disjoint metal wood CxAbstract "disjoint_metatype stuff_type_by_substance"]
    [disjoint wood glass_stuff CxAbstract "disjoint_metatype stuff_type_by_substance"]
    [disjoint wood stone CxAbstract "disjoint_metatype stuff_type_by_substance"]
    [genl function relation CxCore "partition relation function predicate"]
    [genl predicate relation CxCore "partition relation function predicate"]
    [disjoint function predicate CxCore "partition relation function predicate"]
    [genl reifiable_function function CxCore "partition function reifiable_function unreifiable_function"]
    [genl unreifiable_function function CxCore "partition function reifiable_function unreifiable_function"]
    [genl fixed_order_type unary_predicate CxCore "partition unary_predicate fixed_order_type variable_order_type"]
    [genl variable_order_type unary_predicate CxCore "partition unary_predicate fixed_order_type variable_order_type"]
    [genl equivalence_relation binary_predicate CxCore "intersection equivalence_relation reflexive symmetric transitive; reflexive genl binary_predicate"]])

(tu/deftest-kb the-kb-states-no-relation-it-already-derives
  ;; Each relation is read from the context that held the removed sentence, so a removal
  ;; that left a context unable to see the route would fail here.
  (doseq [[pred a b ctx route] derivable-and-unstated]
    (is (true? (if (= 'genl pred) (v/genl? kb a b ctx) (v/disjoint? kb a b ctx)))
        (str "(" pred " " a " " b ") holds in " ctx " by " route))
    ;; stated means a premise: a derived copy is the KB deriving it, which is the point
    (is (not-any? #(v/premise? kb (:id %)) (v/sentexes-matching kb (list pred a b) '?ctx))
        (str "and (" pred " " a " " b ") is not stated"))))

;; ---- the literal types: one vocabulary, and one exception ----------------
;; `string` / `number` / `integer` / `symbol` are the KB's only names for text, numbers
;; and names, and both argument declarations read the same four (docs/argtypes.md).  The
;; distinction between them is carried by *which predicate you write* — `arg` types what
;; an argument denotes, `quotedArg` the term written there — so a second set of type
;; names would be redundancy plus a trap, a `quotedArg` outside the syntactic lattice
;; convicting nothing for the life of the KB.  These pin the modelling half of that: the
;; placement, the two disjointness claims, and the one type the pattern does not reach.

(tu/deftest-kb the-value-kinds-are-placed-in-the-domain-lattice
  (testing "text and a number have no mass and no location"
    (is (v/genl? kb 'string 'intangible))
    (is (v/genl? kb 'number 'intangible)))
  (testing "integer reaches intangible through number, carrying no edge of its own"
    (is (v/genl? kb 'integer 'number))
    (is (v/genl? kb 'integer 'intangible))
    (is (empty? (v/sentexes-matching kb '(genl integer intangible) 'CxUniverse))
        "the reach is transitive: no second parent is asserted for it"))
  (testing "and neither of them is a relation"
    (is (v/disjoint? kb 'string 'predicate))
    (is (v/disjoint? kb 'number 'predicate))
    (is (v/disjoint? kb 'integer 'predicate)
        "the declaration on number carries integer with it")))

(tu/deftest-kb symbol-is-mention-only-and-carries-neither-claim
  ;; the deliberate absence, and the one a later reader is most likely to "fix": a symbol
  ;; does not denote itself, so the set of names and the set of things named are two sets
  ;; — parentOf is written as a symbol and denotes a predicate.  Both claims below would
  ;; be false of every predicate name in the KB.
  (is (not (v/disjoint? kb 'symbol 'predicate))
      "a name is exactly how a predicate is written")
  (is (not (v/genl? kb 'symbol 'intangible))
      "and nothing places it in the domain lattice, there being no use-level reading"))

(tu/deftest-kb the-comment-text-position-refuses-a-relation-and-exempts-a-name
  ;; `(arg comment 2 string)` at the ground level, and the mechanism is `args-problem`'s
  ;; own rather than the disjointness above: a term already in the hierarchy that reaches
  ;; no path to the declared type is convicted, and one the KB classifies not at all is
  ;; exempt.  The disjointness does two other jobs — it refuses a term asserted both at
  ;; once, and it is what the rule-variable arm reads (docs/taxonomy.md).
  (tu/with-terms [SomeDoc]
    (testing "a predicate in the text position is convicted"
      (is (= :arg-type (:type (first (v/check kb (list 'comment 'thing 'genl) 'CxUniverse))))))
    (testing "an unclassified name is exempt — nothing says what it denotes"
      (is (= [] (v/check kb (list 'comment 'thing SomeDoc) 'CxUniverse))))
    (testing "and a string value is what the position is for"
      (is (= [] (v/check kb (list 'comment 'thing "some text") 'CxUniverse))))))

(tu/deftest-kb a-term-cannot-be-both-a-string-and-a-relation
  (tu/with-terms [Thing1]
    (v/assert kb (list 'string Thing1) 'CxUniverse)
    (is (tu/stored-in-clash? kb (list 'predicate Thing1) 'CxUniverse))))

;; ---- what is biological ---------------------------------------------------
;; An organism and a part it grew are both biological, and tangible through it.  The two
;; are separated without being said to exhaust biological.

(tu/deftest-kb an-organism-and-a-body-part-are-biological-and-tangible
  (doseq [t '[organism body_part]]
    (is (true? (v/genl? kb t 'biological)) (str t " is biological"))
    (is (true? (v/genl? kb t 'tangible)) (str t " is tangible through biological")))
  (is (true? (v/genl? kb 'biological 'tangible)))
  (testing "a kind CxOrganism places reaches tangible from CxOrganism itself"
    (is (true? (v/genl? kb 'animal 'tangible 'CxOrganism))))
  (tu/with-terms [Gizzard]
    (v/assert kb (list 'body_part Gizzard) 'CxUniverse)
    (is (true? (v/ask? kb (list 'biological Gizzard) 'CxUniverse)))
    (is (true? (v/ask? kb (list 'tangible Gizzard) 'CxUniverse)))))

(tu/deftest-kb a-biological-thing-is-not-a-substance
  ;; Stated once, of biological and substance, and read down to both of biological's
  ;; parts: neither an organism nor a part it grew is stuff.
  (is (true? (v/disjoint? kb 'biological 'substance)))
  (testing "the separation reaches organism and body_part, which state none of their own"
    (is (true? (v/disjoint? kb 'organism 'substance)))
    (is (true? (v/disjoint? kb 'body_part 'substance)))
    (is (true? (v/disjoint? kb 'leaf 'wood)) "and the kinds below each"))
  (tu/with-terms [Gristle]
    (v/assert kb (list 'biological Gristle) 'CxUniverse)
    (is (true? (tu/stored-in-clash? kb (list 'substance Gristle) 'CxUniverse))
        "a biological thing that is also a substance is a clash")))

(tu/deftest-kb an-organism-is-not-a-body-part
  (is (true? (v/disjoint? kb 'organism 'body_part)))
  (is (true? (v/disjoint? kb 'animal 'feather))
      "the separation reaches the kinds below each part")
  (tu/with-terms [Polyp]
    (v/assert kb (list 'organism Polyp) 'CxUniverse)
    (is (true? (tu/stored-in-clash? kb (list 'body_part Polyp) 'CxUniverse))))
  (testing "and nothing says a biological thing is one or the other"
    (tu/with-terms [Spore]
      (v/assert kb (list 'biological Spore) 'CxUniverse)
      (v/assert kb (list 'not (list 'organism Spore)) 'CxUniverse)
      (is (not (v/ask? kb (list 'body_part Spore) 'CxUniverse))))))

(tu/deftest-kb a-body-part-can-be-food
  ;; A leg of lamb or a chicken wing is both, so the pair is declared orthogonal rather
  ;; than disjoint.
  (is (not (v/disjoint? kb 'food 'body_part)))
  (tu/with-terms [Drumstick]
    (v/assert kb (list 'body_part Drumstick) 'CxUniverse)
    (is (not (tu/stored-in-clash? kb (list 'food Drumstick) 'CxUniverse))
        "a body part that is also food is no clash")
    (is (true? (v/ask? kb (list 'food Drumstick) 'CxUniverse)))
    (is (true? (v/ask? kb (list 'body_part Drumstick) 'CxUniverse)))))

(tu/deftest-kb an-organism-or-a-body-part-can-be-an-artifact
  ;; An artifact is something intentionally made, so an engineered bacterium or an organ
  ;; grown in a lab is both.  The pair is declared orthogonal rather than disjoint.
  (is (not (v/disjoint? kb 'biological 'artifact)))
  (is (not (v/disjoint? kb 'organism 'artifact)))
  (is (not (v/disjoint? kb 'body_part 'artifact)))
  (tu/with-terms [Engineered LabKidney]
    (v/assert kb (list 'organism Engineered) 'CxUniverse)
    (is (not (tu/stored-in-clash? kb (list 'artifact Engineered) 'CxUniverse))
        "an organism that is also an artifact is no clash")
    (is (true? (v/ask? kb (list 'artifact Engineered) 'CxUniverse)))
    (v/assert kb (list 'body_part LabKidney) 'CxUniverse)
    (is (not (tu/stored-in-clash? kb (list 'artifact LabKidney) 'CxUniverse))
        "a body part that is also an artifact is no clash"))
  (testing "while a biological thing stays apart from a substance"
    (is (true? (v/disjoint? kb 'organism 'substance)))
    (is (true? (v/disjoint? kb 'body_part 'substance)))))

;; ---- the relation vocabulary: what divides a relation ---------------------
;; A relation is a function or a predicate, a function is reifiable or not, and a
;; unary_predicate is of one fixed order or of variable order.  Each is a partition, so
;; the parts are separated and cover their whole: a member denied every part but one is
;; concluded the last.

(tu/deftest-kb function-and-predicate-partition-relation
  (is (true? (v/disjoint? kb 'function 'predicate 'CxCore)))
  (testing "a relation that is not a predicate is a function — the coverage half"
    (tu/with-terms [relatesTo]
      (v/assert kb (list 'relation relatesTo) 'CxUniverse)
      (v/assert kb (list 'not (list 'predicate relatesTo)) 'CxUniverse)
      (is (true? (v/ask? kb (list 'function relatesTo) 'CxUniverse))))))

(tu/deftest-kb reifiable-and-unreifiable-partition-function
  (is (true? (v/disjoint? kb 'reifiable_function 'unreifiable_function 'CxCore)))
  (is (true? (v/genl? kb 'reifiable_function 'function 'CxCore)))
  (is (true? (v/genl? kb 'unreifiable_function 'function 'CxCore)))
  (testing "the separation is not quoting_function's: that mark crosses both parts"
    (is (not (v/disjoint? kb 'quoting_function 'reifiable_function)))
    (is (not (v/disjoint? kb 'quoting_function 'unreifiable_function)))))

(tu/deftest-kb fixed-and-variable-order-partition-unary-predicate
  (is (true? (v/disjoint? kb 'fixed_order_type 'variable_order_type 'CxCore)))
  (is (true? (v/genl? kb 'fixed_order_type 'unary_predicate 'CxCore)))
  (is (true? (v/genl? kb 'variable_order_type 'unary_predicate 'CxCore)))
  (testing "so a type of one order is never of variable order"
    (is (true? (v/disjoint? kb 'metatype 'variable_order_type 'CxCore)))))

(tu/deftest-kb an-equivalence-relation-is-the-intersection-of-its-three-marks
  (is (true? (v/genl? kb 'equivalence_relation 'reflexive 'CxCore)))
  (is (true? (v/genl? kb 'equivalence_relation 'symmetric 'CxCore)))
  (is (true? (v/genl? kb 'equivalence_relation 'transitive 'CxCore)))
  (testing "a predicate carrying all three marks is concluded an equivalence_relation"
    (tu/with-terms [sameShadeAs]
      (doseq [m '[reflexive symmetric transitive]]
        (v/assert kb (list m sameShadeAs) 'CxUniverse))
      (is (true? (v/ask? kb (list 'equivalence_relation sameShadeAs) 'CxUniverse)))))
  (testing "and one carrying two of them is not"
    (tu/with-terms [nearTo]
      (v/assert kb (list 'reflexive nearTo) 'CxUniverse)
      (v/assert kb (list 'symmetric nearTo) 'CxUniverse)
      (is (not (v/ask? kb (list 'equivalence_relation nearTo) 'CxUniverse))))))

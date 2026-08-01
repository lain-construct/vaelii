(ns vaelii.naming-test
  "Pure unit tests for the naming invariants, plus the KB-level policy that decides how
  hard they are enforced."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.naming :as nm]
            [vaelii.test-util :as tu]))

(deftest temp-terms-are-valid-and-debuggable
  (testing "the role is inferred from the symbol's own shape"
    (is (= :type       (tu/term-role 'dog)))
    (is (= :individual (tu/term-role 'Fido)))
    (is (= :predicate  (tu/term-role 'parentOf)))
    (is (= :context    (tu/term-role 'StoryContext))))
  (tu/with-terms [dog Fido parentOf StoryContext]
    (testing "each generated term satisfies the invariant for its role"
      (is (nm/type-symbol? dog))
      (is (nm/individual? Fido))
      (is (nm/predicate? parentOf))
      (is (nm/context? StoryContext))
      (is (empty? (nm/problems (list dog Fido) StoryContext))))
    (testing "and embeds the symbol it was named after, so a failure is readable"
      (is (re-find #"dog"      (name dog)))
      (is (re-find #"Fido"     (name Fido)))
      (is (re-find #"ParentOf" (name parentOf)))
      (is (re-find #"Story"    (name StoryContext))))
    (testing "a type temp named after a bare word stays as ambiguous as the word"
      ;; `dog` satisfies both conventions and is disambiguated by arity, so the temp
      ;; is spelled to be usable either way — underscores would pin it to arity 1
      (is (nm/predicate? dog))
      (is (empty? (nm/problems (list dog Fido) StoryContext)))
      (is (empty? (nm/problems (list dog Fido Fido) StoryContext))))
    (testing "roles stay distinct — a context is not an individual"
      (is (not (nm/individual? StoryContext)))))
  (testing "a base spelled snake_case is a type and only a type"
    (let [t (tu/fresh-term :type "physical object")]
      (is (nm/type-symbol? t))
      (is (not (nm/predicate? t)))
      (is (empty? (nm/problems (list t 'Rock1) 'WellContext)))
      (is (seq (nm/problems (list t 'Rock1 'Rock2) 'WellContext)))))
  (testing "the same name twice still yields distinct terms"
    (is (not= (tu/fresh-term :type "dog") (tu/fresh-term :type "dog")))))

(deftest role-predicates
  (testing "contexts"
    (is (nm/context? 'UniverseContext))
    (is (not (nm/context? 'Universe))))
  (testing "individuals are CapitalCamelCase but not contexts"
    (is (nm/individual? 'Fido))
    (is (not (nm/individual? 'dog)))
    (is (not (nm/individual? 'UniverseContext))))
  (testing "predicates are camelCase, types are snake_case"
    (is (nm/predicate? 'parentOf))
    (is (nm/type-symbol? 'physical_object))
    (is (not (nm/predicate? 'physical_object)))          ; underscore ⇒ not a predicate
    (is (not (nm/type-symbol? 'parentOf)))))             ; uppercase ⇒ not snake_case

(deftest a-bare-lowercase-word-satisfies-both-conventions
  ;; The footing of the whole arity coupling: `problems` refuses a snake_case functor at
  ;; arity ≠ 1 *because* an underscore rules out `predicate?`, and leaves a bare word
  ;; alone *because* it satisfies both, so only arity can decide its role.  The test
  ;; harness relies on the same fact (`test-util/fresh-term`, a `:type` temp named after
  ;; a bare word).  Should these two ever stop overlapping, the design loses its footing
  ;; somewhere far from here, so it is enforced rather than left to prose.
  (doseq [w '[dog likes genl thing p q rel]]
    (testing (str w)
      (is (nm/predicate? w))
      (is (nm/type-symbol? w))
      (testing "so it is unconstrained in arity"
        (is (empty? (nm/problems (list w 'Fido) 'WellContext)))
        (is (empty? (nm/problems (list w 'Fido 'Rex) 'WellContext))))))
  (testing "an underscore rules out the predicate convention, and only then does arity bite"
    (doseq [t '[physical_object lives_in tmp_dog_17]]
      (testing (str t)
        (is (not (nm/predicate? t)))
        (is (nm/type-symbol? t))
        (is (empty? (nm/problems (list t 'Fido) 'WellContext)))
        (is (seq (nm/problems (list t 'Fido 'Rex) 'WellContext)))))))

(deftest structural-accessors
  (is (= 'parentOf (nm/functor '(parentOf Tom Bob))))
  (is (= '(Tom Bob) (nm/args '(parentOf Tom Bob))))
  (is (= 2 (nm/arity '(parentOf Tom Bob)))))

(deftest problem-detection
  (is (empty? (nm/problems '(dog Fido) 'NaturalWorldContext)))
  (is (seq (nm/problems '(dog Fido) 'NaturalWorld)))      ; context does not end in Context
  (is (seq (nm/problems '(Dog Fido) 'NaturalWorldContext))))   ; functor not lowercase-initial

;; ---- the literals a sentence contains -----------------------------------
;; `problems` checks a functor per *literal*, so which positions count as literals is
;; the whole substance of the check.  A frame is descended through; an argument is not.

(deftest literals-are-found-inside-every-frame
  (testing "a plain fact is one literal"
    (is (= [[:sentence '(dog Fido)]] (nm/literals '(dog Fido)))))
  (testing "a rule's antecedents and consequent each carry their own role"
    (is (= [[:antecedent '(dog ?x)] [:antecedent '(pet ?x)] [:consequent '(animal ?x)]]
           (nm/literals '(implies (and (dog ?x) (pet ?x)) (animal ?x)))))
    (is (= [[:antecedent '(dog ?x)] [:consequent '(animal ?x)]]
           (nm/literals '(implies (dog ?x) (animal ?x))))))
  (testing "a `not` body is the literal, at whatever role the negation sits in"
    (is (= [[:sentence '(flies Tweety)]] (nm/literals '(not (flies Tweety)))))
    (is (= [[:antecedent '(bird ?x)] [:consequent '(flies ?x)]]
           (nm/literals '(implies (bird ?x) (not (flies ?x)))))))
  (testing "an exceptWhen query's conjuncts are literals of their own"
    (is (= [[:exception '(penguin ?x)] [:antecedent '(bird ?x)] [:consequent '(flies ?x)]]
           (nm/literals '(exceptWhen (penguin ?x)
                                     (set/defaultRule (implies (bird ?x) (flies ?x)))))))
    (testing "written as a vector conjunction"
      (is (= [[:exception '(penguin ?x)] [:exception '(sick ?x)]
              [:antecedent '(bird ?x)] [:consequent '(flies ?x)]]
             (nm/literals '(exceptWhen [(penguin ?x) (sick ?x)]
                                       (implies (bird ?x) (flies ?x))))))))
  (testing "an `ist` redirection frames the sentence it directs"
    (is (= [[:antecedent '(arity ?p 1)] [:consequent '(unaryPredicate ?p)]]
           (nm/literals '(implies (arity ?p 1) (ist CoreContext (unaryPredicate ?p)))))))
  (testing "a negation-as-failure query is framed by `unknown` / `thereExists`"
    (is (= [[:antecedent '(bird ?x)] [:antecedent '(nestOf ?x ?y)] [:consequent '(homeless ?x)]]
           (nm/literals '(implies (and (bird ?x) (unknown (thereExists ?y (nestOf ?x ?y))))
                                  (homeless ?x))))))
  (testing "a head existential frames the consequent it quantifies"
    (is (= [[:antecedent '(person ?x)] [:consequent '(childOf ?x ?y)]]
           (nm/literals '(implies (person ?x) (exists ?y (childOf ?x ?y)))))))
  (testing "the rule wrappers nest in any order and none of them is a literal"
    (is (= [[:antecedent '(bird ?x)] [:consequent '(flies ?x)]]
           (nm/literals '(set/forwardRule
                          (set/defaultRule (implies (bird ?x) (flies ?x)))))))))

(deftest literals-stops-at-what-is-not-a-literal
  (testing "a variable in functor position is a pattern, not a named predicate"
    (is (= [] (nm/literals '(?pred . ?args))))
    (is (= [] (nm/literals '(?p ?x))))
    (testing "so the decontextualization rule's dotted rest pattern names nothing"
      (is (= [] (nm/literals '(set/inertRule
                               (implies (?pred . ?args)
                                        (ist UniverseContext (?pred . ?args)))))))))
  (testing "`(sentexHandle N)` names a stored sentex by id"
    (is (= [[:exception '(penguin ?x)]]
           (nm/literals '(exceptWhen (penguin ?x) (sentexHandle 7))))))
  (testing "a `do/` imperative is an instruction, not a predicate application"
    (is (= [] (nm/literals '(do/labeling SudokuContext)))))
  (testing "arguments are terms, and a compound one is never walked as a literal"
    (is (= [[:sentence '(evaluate ?s (+ 1 2))]] (nm/literals '(evaluate ?s (+ 1 2)))))
    (is (= [[:sentence '(comment not "the negation connective")]]
           (nm/literals '(comment not "the negation connective"))))
    (is (= [[:sentence '(mass Rock1 (QuantityFn 5 Kilogram))]]
           (nm/literals '(mass Rock1 (QuantityFn 5 Kilogram)))))))

;; ---- the invariants below the top level ---------------------------------

(deftest nested-literals-are-name-checked
  (testing "a rule consequent's functor is checked, not the outermost `implies`"
    (is (seq (nm/problems '(implies (penguin ?x) (lives_in ?x cold_place)) 'WellContext)))
    (is (seq (nm/problems '(implies (penguin ?x) (Flies ?x)) 'WellContext))))
  (testing "so is an antecedent's, an exceptWhen query's, and a `not` body's"
    (is (seq (nm/problems '(implies (lives_in ?x cold_place) (penguin ?x)) 'WellContext)))
    (is (seq (nm/problems '(exceptWhen (lives_in ?x cold_place)
                                       (implies (bird ?x) (flies ?x)))
                          'WellContext)))
    (is (seq (nm/problems '(not (lives_in Tweety cold_place)) 'WellContext))))
  (testing "an admissible rule still has no problems"
    (is (empty? (nm/problems '(implies (and (parentOf ?x ?y) (parentOf ?y ?z))
                                       (grandparentOf ?x ?z))
                             'KinshipContext)))))

(deftest snake-case-is-a-type-name-and-therefore-unary-only
  (testing "at arity 1 it is a type"
    (is (empty? (nm/problems '(physical_object Rock1) 'WellContext))))
  (testing "at any other arity it is a type name doing a relation's job"
    (is (seq (nm/problems '(lives_in penguin cold_place) 'WellContext)))
    (is (seq (nm/problems '(disjoint_with penguin fish) 'WellContext))))
  (testing "a camelCase predicate is unconstrained in arity"
    (is (empty? (nm/problems '(livesIn Tweety Antarctica) 'WellContext)))
    (is (empty? (nm/problems '(between A B C) 'WellContext))))
  (testing "an implausible *unary* name is still a well-formed type name — this check is"
    ;; about the shape of a name, never about whether the vocabulary wants it
    (is (empty? (nm/problems '(implies (penguin ?x) (has_black_and_white_feathers ?x))
                             'WellContext)))))

(deftest a-rejection-names-the-literal-and-its-frame
  ;; a repair loop is handed the message verbatim, so it has to say which literal of
  ;; which frame broke, and what to write instead
  (let [[p :as ps] (nm/problems '(implies (penguin ?x) (lives_in ?x cold_place)) 'WellContext)]
    (is (= 1 (count ps)))
    (is (re-find #"lives_in" p))
    (is (re-find #"rule consequent" p))
    (is (re-find #"\(lives_in \?x cold_place\)" p))
    (is (re-find #"livesIn" p) "and the camelCase spelling to use instead"))
  (let [[p] (nm/problems '(implies (Penguin ?x) (flies ?x)) 'WellContext)]
    (is (re-find #"rule antecedent" p))
    (is (re-find #"Penguin" p))))

(deftest an-argument-names-something-and-is-held-to-the-conventions
  ;; a model asked for a relation's second argument writes CapitalCamel-with-underscore
  ;; — a spelling that claims the individual role and the type role and fills neither
  (testing "a symbol matching no role is refused wherever it sits"
    (is (seq (nm/problems '(locatedIn penguin South_Pole) 'WellContext)))
    (is (seq (nm/problems '(genl Baby_Penguin penguin) 'WellContext)))
    (is (seq (nm/problems '(implies (penguin ?x) (locatedIn ?x Cold_Tolerant))
                          'WellContext))))
  (testing "both repairs are named, since only the author knows which role was meant"
    (let [[p] (nm/problems '(locatedIn penguin South_Pole) 'WellContext)]
      (is (re-find #"South_Pole" p))
      (is (re-find #"SouthPole" p) "the individual spelling")
      (is (re-find #"south_pole" p) "the type spelling")))
  (testing "and the frame is named, exactly as a functor rejection names it"
    (let [[p] (nm/problems '(implies (penguin ?x) (locatedIn ?x Cold_Tolerant))
                           'WellContext)]
      (is (re-find #"rule consequent" p))))
  (testing "every well-formed role passes"
    (is (empty? (nm/problems '(locatedIn penguin south_pole) 'WellContext)))
    (is (empty? (nm/problems '(locatedIn Pingu SouthPole) 'WellContext)))
    (is (empty? (nm/problems '(genl penguin bird) 'WellContext)))
    (is (empty? (nm/problems '(inverse parentOf childOf) 'WellContext))))
  (testing "what names nothing is not judged: numbers, strings, variables"
    (is (empty? (nm/problems '(arity penguin 1) 'WellContext)))
    (is (empty? (nm/problems '(argIsa eats 1 animal) 'WellContext)))
    (is (empty? (nm/problems '(comment penguin "A flightless bird.") 'WellContext)))
    (is (empty? (nm/problems '(implies (bird ?x) (flies ?x)) 'WellContext))))
  (testing "a compound argument is a term, so its head is a function and not a name"
    ;; descending into it would judge `+` and every NAUT functor by naming rules that
    ;; were never about them
    (is (empty? (nm/problems '(evaluate Sum (+ 1 2)) 'WellContext)))
    (is (empty? (nm/problems '(termOfUnit Rod1 (QuantityFn 5 Meter)) 'WellContext)))))

(deftest ist-directs-into-a-context
  (is (empty? (nm/problems '(implies (bird ?x) (ist CoreContext (flies ?x))) 'WellContext)))
  (testing "a variable context is bound at firing time"
    (is (empty? (nm/problems '(implies (and (bird ?x) (ctxOf ?x ?c))
                                       (ist ?c (flies ?x)))
                             'WellContext))))
  (testing "anything else is not a context name"
    (is (seq (nm/problems '(implies (bird ?x) (ist Fido (flies ?x))) 'WellContext)))))

(deftest the-dotted-marker-is-still-refused-at-the-top-level
  (is (seq (nm/problems '(parentOf Tom . Bob) 'WellContext)))
  (testing "but is legal inside a rule pattern"
    (is (empty? (nm/problems '(set/inertRule
                               (implies (?pred . ?args)
                                        (ist UniverseContext (?pred . ?args))))
                             'CoreContext)))))

;; ---- a problem is data before it is prose --------------------------------

(deftest a-violation-is-a-class-and-a-symbol-before-it-is-a-sentence
  ;; `assert` wants the sentence it refused spelled out; an audit over a corpus wants to
  ;; group.  A message embeds the literal, so it is unique per record and counting
  ;; messages counts records — which is why the class is the datum and the prose is
  ;; rendered from it.
  (testing "each shape reports its own class, naming the symbol that broke"
    (is (= [{:class :context-name :role :sentence :symbol 'NotAThing}]
           (map #(dissoc % :literal) (nm/problems* '(dog Fido) 'NotAThing))))
    (is (= [{:class :functor :role :sentence :symbol 'Flies}]
           (map #(dissoc % :literal) (nm/problems* '(Flies Tweety) 'WellContext))))
    (is (= [{:class :functor-arity :role :sentence :symbol 'lives_in}]
           (map #(dissoc % :literal) (nm/problems* '(lives_in Tweety cold_place) 'WellContext))))
    (is (= [{:class :argument :role :sentence :symbol 'Baby_Penguin}]
           (map #(dissoc % :literal) (nm/problems* '(parentOf Baby_Penguin Tom) 'WellContext))))
    (is (= [{:class :ist-context :role :sentence :symbol 'Fido}]
           (map #(dissoc % :literal)
                (nm/problems* '(implies (bird ?x) (ist Fido (flies ?x))) 'WellContext)))))
  (testing "every class it can report is one `problem-classes` names"
    (is (every? nm/problem-classes
                (map :class (nm/problems* '(Flies Baby_Penguin) 'NotAThing)))))
  (testing "and `problems` is exactly those rendered, one message each, in order"
    (let [s '(Flies Baby_Penguin)]
      (is (= (mapv nm/message (nm/problems* s 'NotAThing))
             (nm/problems s 'NotAThing)))
      (is (= 3 (count (nm/problems s 'NotAThing)))
          "the context, the functor and the argument — all of them, not the first"))))

;; ---- the policy is the KB's, not the build's -----------------------------

(defn- kb-with
  "A cleared KB on the scratch pair under one naming policy."
  [policy]
  (fn [] (doto (v/open-kb (assoc tu/scratch-space :naming policy)) (tu/clear-kb!))))

(def ^:private misnamed '(parentOf Baby_Penguin Tom))

(deftest the-naming-policy-belongs-to-the-kb
  ;; The conventions are how *this* KB reads a role off a spelling, so a KB holding a
  ;; corpus that spells its names differently is not malformed — it is a KB whose front
  ;; door is set differently.  Neither has to win, and both can be open at once.
  (testing ":strict is the default, and refuses with a :naming type"
    (tu/with-cleared-kb [kb (kb-with :strict)]
      (is (= :strict (:naming kb)))
      (is (= :strict (:naming (v/open-kb tu/scratch-space))) "the default, unasked for")
      (is (= :naming (:type (try (v/assert kb misnamed 'WellContext)
                                 (catch clojure.lang.ExceptionInfo e (ex-data e))))))
      (is (zero? (v/sentex-count kb)) "and nothing was stored")))

  (testing ":off stores it, and it is findable by the name that broke the convention"
    (tu/with-cleared-kb [kb (kb-with :off)]
      (let [h (v/assert kb misnamed 'WellContext)]
        (is (integer? h))
        (is (= 1 (v/sentex-count kb)))
        (is (= misnamed (:sentence (v/sentex kb h))) "stored verbatim, not repaired")
        (is (= [misnamed] (map :sentence (v/find-sentexes kb 'Baby_Penguin)))))))

  (testing ":warn stores it too — the difference is what it says, not what it keeps"
    (tu/with-cleared-kb [kb (kb-with :warn)]
      (is (integer? (v/assert kb misnamed 'WellContext)))
      (is (= 1 (v/sentex-count kb)))))

  (testing "an unknown policy is refused rather than defaulted"
    ;; on the same ground as an unknown `open-kb` key: a KB that silently took :strict
    ;; when it was told :lenient refuses content the caller expected to land
    (is (= :unknown-option
           (:type (try (v/open-kb (assoc tu/scratch-space :naming :lenient))
                       (catch clojure.lang.ExceptionInfo e (ex-data e))))))))

(deftest two-doors-over-one-store-disagree-and-both-are-right
  ;; The policy travels with the KB, not with the records, so a lenient loader and a
  ;; strict editor can hold the same store at once — which is the whole point of it
  ;; being per-KB rather than a property of the build.
  (tu/with-cleared-kb [lenient (kb-with :off)]
    (let [strict (v/open-kb (assoc tu/scratch-space :naming :strict :recover? false))]
      (v/assert lenient misnamed 'WellContext)
      (testing "the strict KB reads what the lenient one stored"
        (is (= [misnamed] (map :sentence (v/find-sentexes strict 'Baby_Penguin)))))
      (testing "but still refuses to be the one that writes it"
        (is (= :naming (:type (try (v/assert strict '(parentOf Other_Penguin Tom) 'WellContext)
                                   (catch clojure.lang.ExceptionInfo e (ex-data e))))))))))

(deftest a-policy-moves-what-is-refused-never-how-a-role-is-read
  ;; The one cost of `:off`, stated as a test so it cannot be forgotten: the KB stores a
  ;; name it *cannot classify*, rather than classifying it differently.  Nothing
  ;; downstream starts reading `Baby_Penguin` as an individual because the door was open.
  (is (nil? (v/term-role 'Baby_Penguin)))
  (is (= :individual (v/term-role 'BabyPenguin)))
  (is (not (nm/individual? 'Baby_Penguin)))
  (testing "so the messages do not move either — only whether anyone throws them"
    (is (seq (nm/problems misnamed 'WellContext)))
    (is (seq (nm/blocking-problems :strict misnamed 'WellContext)))
    (is (empty? (nm/blocking-problems :warn misnamed 'WellContext)))
    (is (empty? (nm/blocking-problems :off  misnamed 'WellContext)))))

(deftest the-other-door-counts-what-it-does-not-check
  ;; A bulk path stores what `assert` refuses — that is what it is for — so the two
  ;; doors are reconciled by a count rather than by a check.
  (let [t (-> nm/empty-tally
              (nm/tally '(dog Fido) 'WellContext)
              (nm/tally misnamed 'WellContext)
              (nm/tally '(Flies Tweety) 'NotAThing))]
    (is (= 3 (:checked t)))
    (is (= 2 (:refused t)) "records, not violations — one sentence can break three")
    (is (= {:argument 1 :functor 1 :context-name 1} (:by-class t)))
    (is (re-find #"2 of 3 records" (nm/tally-line t)))
    (is (re-find #"66\.7%" (nm/tally-line t))))
  (testing "and says nothing at all when the corpus and the front door agree"
    (is (nil? (nm/tally-line (nm/tally nm/empty-tally '(dog Fido) 'WellContext))))))

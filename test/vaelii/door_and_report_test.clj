;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.door-and-report-test
  "One fact, one wording: a definitional check's **door** and its **retroactive reader**
  describe the same KB the same way.

  Several checks exist twice — once refusing content as it arrives, once reading back over
  content admitted before the check could convict it — and the pair answers one question
  about one KB.  Neither half is wrong on its own, which is what makes the class expensive
  to debug: both messages are true statements about the same knowledge, so a reader who
  meets one and greps for the other finds nothing, and a reader who meets both concludes
  there are two problems.  The measured case is `arity`, where an inherited length reads as
  `fatherOf takes 2 arguments through parentOf` and the door that credited `fatherOf` with
  a declaration of its own sent an author looking for a sentence nobody wrote.

  So this is a **roster** rather than one assertion each, on `vector-spelling-test`'s
  model: the defect is never in one half, it is in two halves disagreeing, and a roster is
  what fails when the next pair is added on one side only.  The rows are
  [docs/taxonomy.md](../../docs/taxonomy.md)'s \"What each constraint does in each arrival
  order\" table, **including the cells that read \"nothing\"** — a check documented as
  having no retroactive half is a fact about the KB, and a sweep that quietly acquires one
  turns an open-world check into a closed-world one.

  What the two halves must agree on is the vocabulary a reader carries from one to the
  other: the **predicate or term blamed**, whether the constraint was **inherited** or
  declared outright, and **which stored sentex convicted**.  What they may differ on is
  said row by row, because the difference is real rather than sloppy: a door refuses one
  arriving sentence and names one reason, where a reader swept an extent and names a
  count, and a nogood names a pair in which neither side is the newcomer."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.test-util :as tu]))

;; ---- reading the two halves ---------------------------------------------

(defn- door
  "What a writer meets: the first problem `sentence` draws from a KB `setup` wrote, plus
  `:against` — the **sentence** its `:opposing-handle` names.

  Resolved to a sentence rather than compared as a handle, because the two halves of a
  pair are built in two KBs and a handle is allocation order.  The sentex convicted
  against is what the halves have to agree on; the integer naming it is not."
  [setup sentence context]
  (tu/with-cleared-kb [kb tu/fresh]
    (setup kb)
    (when-let [v (first (v/check kb sentence context))]
      (assoc v :against (:sentence (v/sentex kb (:opposing-handle v)))))))

(defn- reported
  "The `violations` entries of kind `k` a KB `setup` writes, each as its `:detail` with
  `:against` resolved from `:declared-after` where the kind carries one — the same
  handle-to-sentence step `door` takes, for the same reason."
  [setup k]
  (tu/with-cleared-kb [kb tu/fresh]
    (setup kb)
    (into []
          (comp (filter #(= k (:violation %)))
                (map (fn [e]
                       (assoc (:detail e)
                              :against (:sentence
                                        (v/sentex kb (:declared-after (:detail e))))))))
          (v/violations kb))))

(defn- writing
  "A `setup` that asserts each of `sentences` into `CxUniverse`, in order."
  [& sentences]
  (fn [kb] (doseq [s sentences] (v/assert kb s 'CxUniverse))))

(defn- arbitrating-fresh
  "An empty KB under `:constraints :arbitrate` — the policy the three arbitrable kinds
  reach back under, where `:refuse` leaves an identical pair to the door."
  []
  (doto (v/open-kb (assoc tu/scratch-space :constraints :arbitrate)) (tu/clear-kb!)))

;; ---- arity: the pair with a binding to describe -------------------------
;;
;; The row of the table that reaches back *and reports*, and the one with the most for two
;; halves to disagree about: a length binds a predicate through its own declaration or
;; through a super-predicate's, so each half has a predicate, an inheritance and a
;; declaration to name, and each is its own chance to name it differently.

(deftest the-arity-door-and-its-report-word-one-binding-the-same-way
  (tu/with-terms [parentOf fatherOf A B C]
    (let [declaration (list 'binaryPredicate parentOf)
          edge        (list 'genl fatherOf parentOf)]
      (doseq [{:keys [binding pred via fact ingredients]}
              [{:binding     "declared of the predicate itself"
                :pred        parentOf :via parentOf
                :fact        (list parentOf A B C)
                :ingredients [declaration]}
               {:binding     "inherited, with the edge arriving last"
                :pred        fatherOf :via parentOf
                :fact        (list fatherOf A B C)
                :ingredients [declaration edge]}
               {:binding     "inherited, with the length arriving last onto the super"
                :pred        fatherOf :via parentOf
                :fact        (list fatherOf A B C)
                :ingredients [edge declaration]}]]
        (testing binding
          (let [d  (door (apply writing ingredients) fact 'CxUniverse)
                rs (reported (apply writing fact ingredients) :arity)
                r  (first rs)]
            (is (= :arity (:type d)) "the door refuses the fact")
            (is (= 1 (count rs))     "and the other order files one finding")
            (testing "both blame the predicate the fact is of"
              (is (= pred (:predicate d) (:predicate r))))
            (testing "both read the binding off the same predicate"
              (is (= via (:via d) (:via r)))
              (is (= 2 (:expected d) (:expected r))))
            (testing "both convict against the declaration the KB actually holds"
              (is (= declaration (:against d) (:against r))))
            (testing "and both word the binding with the one clause that describes it"
              (let [clause (checks/arity-binding-clause pred via 2)]
                (is (str/includes? (:message d) clause) (:message d))
                (is (str/includes? (:message r) clause) (:message r))))
            (when (not= pred via)
              (testing "an inherited length credits no declaration the predicate carries"
                ;; the drift this roster exists for: "is declared with" is true of the
                ;; super and false of the sub, and a reader who believes it goes looking
                ;; for a sentence nobody wrote
                (is (not (str/includes? (:message d) "is declared with")) (:message d))
                (is (not (str/includes? (:message r) "is declared with")) (:message r))))
            ;; the door refuses **one** sentence, so it names that sentence's length; the
            ;; report swept the predicate's extent, so it names how many facts disagreed.
            ;; Neither statement is available to the other half, and asserting a similarity
            ;; here would be asserting one that is not there.
            (testing "where the two legitimately differ, and why"
              (is (= 3 (:actual d)) "the door names the length of the sentence it refused")
              (is (nil? (:count d)))
              (is (= 1 (:count r))  "the report names the size of the sweep's finding")
              (is (nil? (:actual r))))))))))

;; ---- disjointness: every trigger, one exposure --------------------------
;;
;; Four rows of the table share one retroactive reader (`settle/expose-clashes!`) and one
;; door (`checks/disjoint-problems`), and each row is a different sentence arriving last:
;; the separation itself, a metatype declaring its members pairwise separate, a term
;; joining such a metatype, a `genl` edge closing a separation over content already
;; stored, and a `genlCx` edge putting two contexts' memberships in one reader's sight.
;; A trigger added to one side and not the other is what this row cannot survive.

(deftest every-disjointness-trigger-refuses-and-exposes-the-same-clash
  (tu/with-terms [dog_t cat_t pup_t meta_t alpha_t beta_t Rex CxLeft CxRight]
    (let [ground (fn [& ts] (map #(list 'genl % 'thing) ts))
          rows
          [{:trigger 'disjoint
            :ground  (ground dog_t cat_t)
            :closing (list 'disjoint dog_t cat_t)
            :facts   [[(list dog_t Rex) 'CxUniverse] [(list cat_t Rex) 'CxUniverse]]}
           {:trigger 'disjointMetatype
            :ground  (concat (ground meta_t alpha_t beta_t)
                             [(list meta_t alpha_t) (list meta_t beta_t)])
            :closing (list 'disjointMetatype meta_t)
            :facts   [[(list alpha_t Rex) 'CxUniverse] [(list beta_t Rex) 'CxUniverse]]}
           {:trigger "a term joining a disjoint metatype"
            :ground  (concat (ground meta_t alpha_t beta_t)
                             [(list 'disjointMetatype meta_t) (list meta_t alpha_t)])
            :closing (list meta_t beta_t)
            :facts   [[(list alpha_t Rex) 'CxUniverse] [(list beta_t Rex) 'CxUniverse]]}
           {:trigger 'genl
            :ground  (concat (ground dog_t cat_t pup_t) [(list 'disjoint dog_t cat_t)])
            :closing (list 'genl pup_t dog_t)
            :facts   [[(list cat_t Rex) 'CxUniverse] [(list pup_t Rex) 'CxUniverse]]}
           {:trigger 'genlCx
            :ground  (concat [(list 'genlCx CxLeft 'CxUniverse)
                              (list 'genlCx CxRight 'CxUniverse)]
                             (ground dog_t cat_t)
                             [(list 'disjoint dog_t cat_t)])
            :closing (list 'genlCx CxLeft CxRight)
            :facts   [[(list cat_t Rex) CxRight] [(list dog_t Rex) CxLeft]]}]]
      (doseq [{:keys [trigger ground closing facts]} rows]
        (testing (str trigger " arriving last")
          (let [[[held held-ctx] [arriving arriving-ctx]] facts
                d (door (fn [kb]
                          (doseq [s (concat ground [closing])] (v/assert kb s 'CxUniverse))
                          (v/assert kb held held-ctx))
                        arriving arriving-ctx)
                r (first (reported (fn [kb]
                                     (doseq [s ground] (v/assert kb s 'CxUniverse))
                                     (v/assert kb held held-ctx)
                                     (v/assert kb arriving arriving-ctx)
                                     (v/assert kb closing 'CxUniverse))
                                   :disjoint))]
            (is (= :disjoint (:type d)) "the door refuses the second membership")
            (is (some? r)               "and the other order exposes the pair")
            (testing "both name the term the two memberships are about"
              (is (= Rex (:term r)))
              (is (str/includes? (:message d) (str Rex))))
            (testing "both name the two types, and neither adds one"
              (is (= (set [(first held) (first arriving)])
                     (set (:types d))
                     (set (map first (:held r))))))
            ;; the door names the membership it refused *against* by handle; the exposure
            ;; names both by `[type context]`, which with `:term` reconstructs each
            ;; sentence.  Neither half can borrow the other's spelling — a pair exposed by
            ;; a declaration has no newcomer, so there is nothing for it to call opposing.
            (testing "both identify the memberships, so a reader reaches the sentexes"
              (is (= held (:against d)))
              (is (= #{held arriving}
                     (set (map (fn [[t _]] (list t (:term r))) (:held r))))))
            (testing "and the exposure adds what only a sweep can know"
              (is (seq (:visible-from r))
                  "which contexts see the whole clash — a question no single writer asks")
              (is (nil? (:visible-from d))))))))))

;; ---- functional and asymmetric: a pair, not a message -------------------
;;
;; The other two arbitrable kinds, and the rows where the retroactive half is a **decision**
;; rather than a report: under `:arbitrate` a declaration reaching back over stored facts
;; hands `settle` a nogood, re-derived by calling the very check the door calls.  So the
;; vocabulary cannot drift — there is one check — and what the roster pins instead is that
;; the pair the nogood names is the two sentences the door named, since a nogood carries no
;; message at all and a reader matching one against the other has only the sentences.
;;
;; Both rows put the mark on a **super-predicate**, which is this family's version of an
;; inherited arity: the checks read the mark up the hierarchy, so `(functional parentOf)`
;; convicts two `fatherOf` mothers of one child and the declared predicate is neither
;; fact's functor.  A descended mark has the same three ingredients an inherited length
;; does — the two facts, the declaration and the `genl` edge — so any of the three can be
;; last, and the roster asks all of them.

(defn- standing-pairs
  "The pairs the last settle left standing — represented dilemmas and irreducible clashes
  alike.  One entry shape between them, and which reading a pair lands in is a question
  about the two sides' defeat classes rather than about the constraint that separated
  them."
  [kb]
  (concat (v/contradictions kb) (v/conflicts kb)))

(deftest a-descended-mark-weighs-the-pair-the-door-refuses-in-every-arrival-order
  (doseq [{:keys [kind mark edge held arriving strength via]}
          (tu/with-terms [parentOf fatherOf Kid A B]
            [{:kind     :functional
              :mark     (list 'functional parentOf)
              :edge     (list 'genl fatherOf parentOf)
              :via      parentOf :strength :default
              :held     (list fatherOf Kid 1980)
              :arriving (list fatherOf Kid 1990)}
             ;; known-true, because `:asymmetric` reads the opposing claim's defeat class
             ;; at **both** halves: a defeasible converse is weighed rather than refused, so
             ;; a door row written at `:default` would be comparing a refusal against a
             ;; pair that the door deliberately declines to make one
             {:kind     :asymmetric
              :mark     (list 'asymmetric parentOf)
              :edge     (list 'genl fatherOf parentOf)
              :via      parentOf :strength :monotonic
              :held     (list fatherOf A B)
              :arriving (list fatherOf B A)}])]
    (testing (name kind)
      (let [ingredient {:mark mark :edge edge}
            d (door (fn [kb]
                      (doseq [s [edge mark]] (v/assert kb s 'CxUniverse))
                      (v/assert kb held 'CxUniverse {:strength strength}))
                    arriving 'CxUniverse)]
        (is (= kind (:type d)) "the door refuses the second fact")
        (testing "and blames the predicate carrying the mark, not the fact's functor"
          (is (= via (:pred d)))
          (is (= held (:against d))))
        (doseq [last-in [:mark :edge]]
          (testing (str "with the " (name last-in) " arriving last")
            (let [c (tu/with-cleared-kb [kb arbitrating-fresh]
                      (doseq [k [:mark :edge] :when (not= k last-in)]
                        (v/assert kb (ingredient k) 'CxUniverse))
                      (doseq [s [held arriving]]
                        (v/assert kb s 'CxUniverse {:strength strength}))
                      (v/assert kb (ingredient last-in) 'CxUniverse)
                      (first (standing-pairs kb)))]
              (is (= kind (:kind c)) "the pair is weighed, and as the same kind")
              (is (= #{held arriving} (set (map :sentence (:sides c))))
                  "and it is the pair the door named")
              ;; A refusal has a newcomer and a message about it.  A nogood has two
              ;; believed sentexes and no newcomer — deciding it by which arrived last is
              ;; the arrival-order dependence the JTMS exists to refuse — so it carries the
              ;; pair and a kind, and the sides are what a caller ranks.
              (testing "where the two legitimately differ, and why"
                (is (string? (:message d)))
                (is (nil? (:message c)))
                (is (= 2 (count (:sides c))))))))))))

(deftest a-cross-context-clash-is-exposed-in-the-doors-vocabulary
  ;; The **other** retroactive reader for these two kinds, and the one that runs under
  ;; `:refuse`: two facts each admissible where written, put in one reader's sight by a
  ;; `genlCx` edge.  It re-derives through `checks/arbitrable-violations` — the door's own
  ;; check — and then writes a message of its own, which is where a wording can drift even
  ;; where the finding cannot.
  (doseq [{:keys [kind mark held arriving strength via]}
          (tu/with-terms [parentOf Kid A B]
            [{:kind :functional :mark (list 'functional parentOf) :via parentOf
              :strength :default
              :held (list parentOf Kid 1980) :arriving (list parentOf Kid 1990)}
             {:kind :asymmetric :mark (list 'asymmetric parentOf) :via parentOf
              :strength :monotonic
              :held (list parentOf A B) :arriving (list parentOf B A)}])]
    (testing (name kind)
      (tu/with-terms [CxLeft CxRight]
        (let [d (door (fn [kb]
                        (v/assert kb mark 'CxUniverse)
                        (v/assert kb held 'CxUniverse {:strength strength}))
                      arriving 'CxUniverse)
              r (tu/with-cleared-kb [kb tu/fresh]
                  (doseq [s [(list 'genlCx CxLeft 'CxUniverse)
                             (list 'genlCx CxRight 'CxUniverse)
                             mark]]
                    (v/assert kb s 'CxUniverse))
                  (v/assert kb held CxLeft {:strength strength})
                  (v/assert kb arriving CxRight {:strength strength})
                  (v/assert kb (list 'genlCx CxLeft CxRight) 'CxUniverse)
                  (:detail (first (filter #(= kind (:violation %)) (v/violations kb)))))]
          (is (= kind (:type d)) "the door refuses the second fact")
          (is (some? r)          "and the split-context order exposes the pair")
          (testing "both name the predicate the declaration is on"
            (is (= via (:pred d) (:pred r))))
          (testing "both name the two facts"
            (is (= held (:against d)))
            (is (= #{held arriving} (set (map first (:clash r))))))
          (testing "and the exposure adds the visibility only a sweep can answer"
            (is (seq (:visible-from r)))))))))

;; ---- the cells that read "nothing" --------------------------------------
;;
;; An absence belongs in the roster the way a pair does.  The argument constraints convict
;; on the *absence* of a path to the constraint type — open-world negation as failure — so
;; there is no second sentex to weigh, and a retroactive pass would have to decide whether
;; pre-existing silence is a violation.  Nobody has answered that, and answering it by
;; accident inside a sweep is what turns an open-world check into a closed-world one.  The
;; test below is what fails the day a sweep answers it.

(deftest the-argument-constraints-reach-back-over-nothing-and-refuse-what-follows
  (tu/with-terms [person_t rock_t parentOf fatherOf eats Rock Mary Pebble]
    (let [ground [(list 'genl person_t 'thing) (list 'genl rock_t 'thing)
                  (list rock_t Rock) (list person_t Mary) (list rock_t Pebble)]
          rows
          [{:row     "arg, the declaration arriving last"
            :fact    (list parentOf Rock Mary)
            :closing (list 'arg parentOf 1 person_t)
            :next    (list parentOf Pebble Mary)
            :type    :arg-type}
           {:row     "genlArg, the declaration arriving last"
            :fact    (list parentOf Rock Mary)
            :closing (list 'genlArg parentOf 1 person_t)
            :next    (list parentOf Pebble Mary)
            :type    :arg-genl}
           ;; the conditional constraint has *three* ingredients, and it is the third that
           ;; nothing reaches: the fact and the declaration are stored, and the membership
           ;; arming the trigger arrives afterwards
           {:row     "interArg, the trigger's type arriving last"
            :fact    (list eats Rock Mary)
            :extra   [(list 'interArg eats 1 person_t 2 person_t)]
            :closing (list person_t Rock)
            :next    (list eats Rock Pebble)
            :type    :inter-arg-type}
           ;; the family's non-reach, one ingredient further out: the edge is admitted, the
           ;; fact it now convicts stays stored and believed, and the next claim is refused
           {:row     "a predicate-level genl edge under an argument constraint"
            :fact    (list fatherOf Rock Mary)
            :extra   [(list 'arg parentOf 1 person_t)]
            :closing (list 'genl fatherOf parentOf)
            :next    (list fatherOf Pebble Mary)
            :type    :arg-type}]]
      (doseq [{:keys [row fact extra closing next type]} rows]
        (testing row
          (tu/with-cleared-kb [kb tu/fresh]
            (doseq [s (concat ground [fact] extra [closing])]
              (v/assert kb s 'CxUniverse))
            (is (empty? (v/violations kb))
                "nothing is filed against content admitted before the constraint existed")
            (is (empty? (v/contradictions kb))
                "and no pair is opened — the conviction rests on an absence, not a sentex")
            (is (v/ask? kb fact 'CxUniverse) "the stored fact keeps its belief")
            (is (= type (:type (first (v/check kb next 'CxUniverse))))
                "while the identical claim one line later is refused")))))))

(deftest a-stranded-declaration-is-a-census-finding-and-the-census-says-what-the-door-says
  ;; The other documented absence, and the one whose retroactive half lives somewhere else
  ;; entirely.  `(arg fatherOf 3 person)` is admitted while nothing binds `fatherOf`'s
  ;; length; when a length arrives the declaration constrains a position the predicate
  ;; provably lacks, and the door refuses the identical sentence one line later.  It is not
  ;; refused retroactively — that would make the binding's arrival order decide — and not
  ;; filed in the ledger either, because a stranded declaration is inert and reads the same
  ;; an hour later, so there is no *newly* for a settle to report.  `kb-quality` names it,
  ;; and this is the row that keeps the census reading in the door's vocabulary.
  (tu/with-terms [parentOf fatherOf a_type]
    (tu/with-cleared-kb [kb tu/fresh]
      (doseq [s [(list 'genl a_type 'thing)
                 (list 'arg fatherOf 3 a_type)
                 (list 'binaryPredicate parentOf)
                 (list 'genl fatherOf parentOf)]]
        (v/assert kb s 'CxUniverse))
      (is (empty? (v/violations kb)) "the settle files nothing")
      (let [e (first (:stranded (:declarations (v/kb-quality kb))))
            d (first (v/check kb (list 'arg fatherOf 3 a_type) 'CxUniverse))]
        (is (= :arg-position (:type d)) "the door refuses the identical sentence")
        (testing "and the census names the same predicate, position and binding"
          (is (= fatherOf (:predicate e) (:predicate d)))
          (is (= 3 (:position e) (:position d)))
          (is (= 2 (:arity e) (:arity d)))
          (is (= parentOf (:via e) (:via d))
              "the length came through the super, and both halves say so"))))))

(deftest two-declared-arities-across-one-edge-read-the-same-whichever-arrives-last
  ;; The row of the table whose two halves are **both** doors: there is no order in which
  ;; the pair means anything, so the arriving sentence is refused whichever it is.  The
  ;; message is therefore a fact about the pair rather than about the arrival, and this is
  ;; what fails if one arm ever starts describing the sentence in front of it instead.
  (tu/with-terms [parentOf fatherOf]
    (let [sentence {:edge (list 'genl fatherOf parentOf)
                    :sub  (list 'arity fatherOf 3)}
          messages (into {}
                         (for [last-in [:edge :sub]]
                           [last-in
                            (:message
                             (door (fn [kb]
                                     (v/assert kb (list 'arity parentOf 2) 'CxUniverse)
                                     (doseq [k [:edge :sub] :when (not= k last-in)]
                                       (v/assert kb (sentence k) 'CxUniverse)))
                                   (sentence last-in) 'CxUniverse))]))]
      (is (= (:edge messages) (:sub messages))
          "one pair, one description, whichever half of it arrived")
      (is (str/includes? (:edge messages) (str "3 arguments declared of " fatherOf)))
      (is (str/includes? (:edge messages) (str "2 declared of " parentOf))))))

;; ---- the wording spelled once -------------------------------------------

(deftest one-clause-words-an-arity-binding-for-every-reader-of-it
  ;; Three readers describe a binding, and the rows above pin that they agree.  This pins
  ;; *how*: `checks/arity-binding-clause` is the wording, the door and the settle's
  ;; retroactive report each carry it, and `kb-quality`'s stranded-declaration census
  ;; carries the door's own message rather than writing a second one.  A copy of a rule
  ;; that says "is declared with" of a declaration and "takes … through" of an inheritance
  ;; is a chance for one binding to acquire two descriptions, which is what this namespace
  ;; is about.
  (tu/with-terms [parentOf fatherOf A B C a_type]
    (let [inherited (checks/arity-binding-clause fatherOf parentOf 2)]
      (is (= (str "takes 2 arguments through " parentOf) inherited))
      (is (= "is declared with 2 arguments"
             (checks/arity-binding-clause parentOf parentOf 2)))
      (is (= "is declared with 1 argument"
             (checks/arity-binding-clause parentOf parentOf 1))
          "the plural agrees with the number, in one place rather than three")
      (testing "the door"
        (is (str/includes?
             (:message (door (writing (list 'binaryPredicate parentOf)
                                      (list 'genl fatherOf parentOf))
                             (list fatherOf A B C) 'CxUniverse))
             inherited)))
      (testing "the retroactive report"
        (is (str/includes?
             (:message (first (reported (writing (list fatherOf A B C)
                                                 (list 'binaryPredicate parentOf)
                                                 (list 'genl fatherOf parentOf))
                                        :arity)))
             inherited)))
      (testing "and the census, which carries the door's message unaltered"
        (tu/with-cleared-kb [kb tu/fresh]
          (doseq [s [(list 'genl a_type 'thing)
                     (list 'arg fatherOf 3 a_type)
                     (list 'binaryPredicate parentOf)
                     (list 'genl fatherOf parentOf)]]
            (v/assert kb s 'CxUniverse))
          (is (str/includes? (v/quality-report (v/kb-quality kb)) inherited)))))))

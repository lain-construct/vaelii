;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.functional-in-arg-test
  "`(functionalInArg P n)` says the other arguments of `P` determine argument `n`.

  `functional` is the arity-2 special case with `n` fixed at 2: `functional-clashes`
  destructures `(nm/args sentence)` as `[a b]` and probes `(list q a '?fv)`, so arg 1
  determines arg 2 and nothing else can be said.  `namesObject(namespace, path, object)`
  wants `(namespace, path) → object` — a composite determinant — and there is no way to
  spell it.  The generalization is a *determinant set*: every argument position except
  `n`, taken together, fixes the filler at `n`.

  Two degenerate ends bracket it, and both are tested here rather than assumed:

  - `(functionalInArg P 2)` on a binary predicate must behave exactly as `(functional P)`
    does today.  That is the regression half — the generalization is not allowed to move
    arity-2 behaviour.
  - `(functionalInArg P 1)` on a **unary** predicate has an *empty* determinant, which
    reads as \"at most one filler, full stop.\"  Every filler must reconcile with every
    other, so it is the sharpest available probe of the merge/reject rule and it is what
    Pace's matrix uses.

  The merge/reject rule itself is not new and is not ours to invent.  `CxCore.txt:259`:

      two symbols derive (equals V1 V2) and merge, so retracting either fact or the
      declaration un-merges them, while two non-symbols such as 1980 and 1990 are
      refused outright, no merge being able to make two numbers one thing

  and `mergeable-values?` (checks.clj) is the code half.  So the matrix below is one
  question asked five ways: *does the generalized determinant reach the same verdict the
  arity-2 path reaches, in every context that can see both fillers?*

  Context shape throughout, per Pace's specification:

      CxUniverse
        ├── CxLeft   (p ThingOne)
        ├── CxRight  (p ThingTwo)
        ├── CxBottom      sees CxLeft and CxRight
        ├── CxBottomOne   sees CxLeft and CxRight
        └── CxBottomTwo   sees CxLeft and CxRight

  Neither CxLeft nor CxRight sees the other, so each is individually consistent and the
  clash exists only from a context below both.  The two bottoms are not redundant: they
  pin that the verdict is a property of *what a context sees*, not of which context ran
  first or of state left behind by the first descent.

  STATUS: written before the implementation exists, deliberately.  Every test here
  should fail until `functionalInArg` lands, and should fail by *not enforcing* — a
  failure that reports an unknown predicate is a scaffold bug, not a red test."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(def ^:private U 'CxUniverse)

(defn- contexts!
  "Mint the five contexts and wire the bottoms to see both sides.

  `(genlCx c g)` puts `g` above `c` — `c` sees `g`.  The bottoms therefore name CxLeft
  and CxRight, not the other way about, and CxLeft/CxRight name only CxUniverse so they
  stay blind to each other."
  [kb {:keys [left right bottoms]}]
  (doseq [c (into [left right] bottoms)]
    (v/assert kb (list 'genlCx c U) U))
  (doseq [b bottoms, side [left right]]
    (v/assert kb (list 'genlCx b side) U)))

(defmacro ^:private check
  "`is`, with the KB kept out of the failure report.

  `clojure.test` prints the asserted form with its arguments *evaluated*, so any bare
  `(is (merged? kb x y))` dumps the entire KB record — records, index, TMS, provers — into
  the report and buries the one bit that matters.  Binding first prints `false`."
  [expr msg]
  `(let [r# ~expr] (is r# (str ~msg "  ⟵ " '~expr))))

(defn- merged?
  "Did the two fillers end up in one equality class?"
  [kb x y]
  (boolean (v/same-class? kb x y)))

(defn- equality-in?
  "Is `(equals x y)` a stored sentex visible from `ctx`?  This is the per-context
  question, and the one Pace's matrix is actually about."
  [kb x y ctx]
  (boolean (v/handle-of kb (list 'equals x y) ctx)))

(defn- clash-contexts
  "The set of contexts named by the sides of every recorded contradiction.

  `contradictions` entries carry `:sides [{:handle :sentence :context …} …]` — the
  context is on each **side**, not on the entry, which is worth stating because reading
  `:context` off the entry yields nil for every entry and a filter that is quietly
  always empty."
  [kb]
  (into #{} (mapcat #(map :context (:sides %))) (v/contradictions kb)))

(defn- any-contradiction?
  "Is there any recorded contradiction at all?"
  [kb]
  (boolean (seq (v/contradictions kb))))

(defn- ex-type
  "The `:type` of the ex-info a thunk throws, or nil.  A refusal that collapses into an
  arity or naming error is exactly the regression a bare `thrown?` stays green through."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

;; ---- the regression half: arity 2 must not move -------------------------

(tu/deftest-kb functional-in-arg-2-on-a-binary-predicate-is-todays-functional
  ;; The generalization earns nothing if it changes what already works.  Same fixture as
  ;; the existing functional tests, spelled the new way.
  (tu/with-terms [parentOf Tom]
    (let [[lo hi] (sort [(tu/tmp-ind "Mary") (tu/tmp-ind "Mary")])]
      (v/assert kb (list 'functionalInArg parentOf 2) U)
      (v/assert kb (list parentOf Tom lo) U)
      (v/assert kb (list parentOf Tom hi) U)
      (is (merged? kb lo hi)
          "arg 1 determines arg 2, two symbol fillers, merged — as (functional parentOf)")))
  (testing "and the numeric side still refuses outright"
    (tu/with-terms [birthYearOf Tom]
      (v/assert kb (list 'functionalInArg birthYearOf 2) U)
      (v/assert kb (list birthYearOf Tom 1980) U)
      (is (some? (ex-type #(v/assert kb (list birthYearOf Tom 1990) U)))
          "no merge can make 1980 and 1990 one thing"))))

;; ---- Pace's matrix, rows 1 and 2 ----------------------------------------

(tu/deftest-kb two-numbers-under-an-empty-determinant-contradict-in-the-context-below
  ;; Row 1.  `(p 1)` in CxLeft and `(p 2)` in CxRight are each fine where they stand;
  ;; CxBottom sees both and no merge can reconcile two numbers, so the clash is a
  ;; contradiction rather than knowledge.
  (tu/with-terms [p CxLeft CxRight CxBottom]
    (contexts! kb {:left CxLeft :right CxRight :bottoms [CxBottom]})
    (v/assert kb (list 'functionalInArg p 1) U)
    (v/assert kb (list p 1) CxLeft)
    (v/assert kb (list p 2) CxRight)
    (testing "the clash is reported, and it belongs to the vantage that sees it"
      (check (any-contradiction? kb)
             "two numbers, one empty-determinant slot, nothing to merge")
      (check (= #{CxBottom} (clash-contexts kb))
             "CxBottom, not the leaves the fillers were asserted in"))
    (testing "and no equality is derived anywhere, numbers being unmergeable"
      (check (not (equality-in? kb 1 2 CxBottom)) "no (equals 1 2)"))))

(tu/deftest-kb a-clash-no-context-can-see-is-not-a-clash
  ;; Pace's rule, S174, and the converse of the row above — the half that makes it a
  ;; rule rather than a labelling choice:
  ;;
  ;;   "it's silly to compute {CxLeft CxRight} if they're both leaf contexts. Who cares
  ;;    whether there's an implicit contradiction if there's no context that sees that
  ;;    contradiction. that's just wasting compute."
  ;;
  ;; Same two facts as the row above, with **no context below either side**.  Neither
  ;; leaf can see the other, so no vantage exists from which the two fillers are both
  ;; present, and there is nothing to report.  A contradiction here would mean the engine
  ;; is computing clashes eagerly across mutually blind contexts.
  (tu/with-terms [p CxLeft CxRight]
    (doseq [c [CxLeft CxRight]]
      (v/assert kb (list 'genlCx c U) U))
    (v/assert kb (list 'functionalInArg p 1) U)
    (v/assert kb (list p 1) CxLeft)
    (v/assert kb (list p 2) CxRight)
    (check (not (any-contradiction? kb))
           "no context sees both fillers, so the clash does not exist to be had")
    (check (empty? (clash-contexts kb)) "and nothing is stamped with a vantage")))

(tu/deftest-kb two-symbols-under-an-empty-determinant-merge-in-the-context-below
  ;; Row 2, and the one Pace specified the answer for: the desired behaviour is
  ;; `(equals ThingOne ThingTwo)` in CxBottom.  This is where a functional clash is
  ;; *knowledge* — two names for one thing — rather than an error.
  (tu/with-terms [p ThingOne ThingTwo CxLeft CxRight CxBottom]
    (contexts! kb {:left CxLeft :right CxRight :bottoms [CxBottom]})
    (v/assert kb (list 'functionalInArg p 1) U)
    (v/assert kb (list p ThingOne) CxLeft)
    (v/assert kb (list p ThingTwo) CxRight)
    (testing "neither side alone concludes anything about the pair"
      (is (not (merged? kb ThingOne ThingTwo))
          "CxLeft and CxRight cannot see each other"))
    (testing "and the context below both derives the equality"
      (is (some? (v/handle-of kb (list 'equals ThingOne ThingTwo) CxBottom))
          "(equals ThingOne ThingTwo) in CxBottom, which is what was asked for")
      (is (not (any-contradiction? kb))
          "a merge is knowledge, not an error"))))

;; ---- row 3: the explicit different ---------------------------------------

(tu/deftest-kb an-asserted-difference-blocks-the-merge-and-leaves-a-contradiction
  ;; Row 3, and the row most likely to expose a real defect: two resolution paths meet
  ;; here.  The functional constraint wants to derive `(equals ThingOne ThingTwo)`; the
  ;; asserted `(different ThingOne ThingTwo)` denies exactly that.  Whichever runs first
  ;; must not decide the answer, so this is asserted in both orders.
  ;; NOTE: spelled `(not (equals …))`, not `(different …)`.  `different` is **not
  ;; assertible** — it is negation as failure over the equality closure, answered by a
  ;; prover and never stored (`wff.clj` `different-problems`, `docs/equality.md:83`), and
  ;; an assertible one would be OWL's `differentFrom`, which equality.md:540 declines on
  ;; purpose.  A stored negated equality is the only way to commit to distinctness here.
  (doseq [[label difference-first?] [["difference asserted first" true]
                                     ["difference asserted last" false]]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [p ThingOne ThingTwo CxLeft CxRight CxBottom]
        (contexts! kb {:left CxLeft :right CxRight :bottoms [CxBottom]})
        (v/assert kb (list 'functionalInArg p 1) U)
        (when difference-first?
          (v/assert kb (list 'not (list 'equals ThingOne ThingTwo)) U))
        (v/assert kb (list p ThingOne) CxLeft)
        (v/assert kb (list p ThingTwo) CxRight)
        (when-not difference-first?
          (v/assert kb (list 'not (list 'equals ThingOne ThingTwo)) U))
        (testing label
          (is (not (merged? kb ThingOne ThingTwo))
              "the asserted difference denies the equality the constraint wants")
          (is (not (equality-in? kb ThingOne ThingTwo CxBottom))
              "so no equality is stored in the context that sees both")
          (is (any-contradiction? kb)
              "and the clash has nowhere to resolve to, so it stands as a contradiction"))))))

;; ---- row 4: two bottoms, same verdict ------------------------------------

(tu/deftest-kb both-contexts-below-reach-the-same-verdict
  ;; Row 4.  CxBottomOne and CxBottomTwo see exactly the same two facts and neither sees
  ;; the other.  A verdict that differs between them would mean the answer depends on
  ;; which descent ran first, or on state one left behind — which is the failure mode
  ;; the pair exists to catch, not a property anyone wants.
  (testing "the mergeable pair merges in both"
    (tu/with-terms [p ThingOne ThingTwo CxLeft CxRight CxBottomOne CxBottomTwo]
      (contexts! kb {:left CxLeft :right CxRight
                     :bottoms [CxBottomOne CxBottomTwo]})
      (v/assert kb (list 'functionalInArg p 1) U)
      (v/assert kb (list p ThingOne) CxLeft)
      (v/assert kb (list p ThingTwo) CxRight)
      (doseq [b [CxBottomOne CxBottomTwo]]
        (is (equality-in? kb ThingOne ThingTwo b)
            (str "equality derived in " b)))))
  (testing "and the unmergeable pair contradicts in both"
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [p CxLeft CxRight CxBottomOne CxBottomTwo]
        (contexts! kb {:left CxLeft :right CxRight
                       :bottoms [CxBottomOne CxBottomTwo]})
        (v/assert kb (list 'functionalInArg p 1) U)
        (v/assert kb (list p 1) CxLeft)
        (v/assert kb (list p 2) CxRight)
        (is (any-contradiction? kb) "the unmergeable clash is reported")
        (doseq [b [CxBottomOne CxBottomTwo]]
          (is (not (equality-in? kb 1 2 b))
              (str "and no equality is manufactured in " b)))))))

;; ---- the motivating case -------------------------------------------------

(tu/deftest-kb a-composite-determinant-fixes-the-filesystem-constraint
  ;; The reason this exists.  `namesObject(namespace, path, object)` needs
  ;; `(namespace, path) → object`: same namespace and same path, one object.  Arity-2
  ;; `functional` cannot say it, because the determinant is two arguments wide.
  (tu/with-terms [namesObject NsA PathA ObjOne ObjTwo]
    (v/assert kb (list 'functionalInArg namesObject 3) U)
    (v/assert kb (list namesObject NsA PathA ObjOne) U)
    (v/assert kb (list namesObject NsA PathA ObjTwo) U)
    (is (merged? kb ObjOne ObjTwo)
        "one namespace and one path name one object, so the two names merge"))
  (testing "and a different path is a different slot, so nothing merges"
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [namesObject NsA PathA PathB ObjOne ObjTwo]
        (v/assert kb (list 'functionalInArg namesObject 3) U)
        (v/assert kb (list namesObject NsA PathA ObjOne) U)
        (v/assert kb (list namesObject NsA PathB ObjTwo) U)
        (is (not (merged? kb ObjOne ObjTwo))
            "the determinant differs, so these fill two slots and neither constrains the other")))))

;; ---- the wide case: Pace's 212 ------------------------------------------

(def ^:private wide-arity
  "212, at Pace's request.  Nothing in the suite goes above 7 and the metatype names stop
  at three, so this is the first argument count anything here has been asked to carry."
  212)

(defn- wide-sentence
  "`(P a1 … a211 tail)` — the shared 211-position determinant with `tail` at position 212."
  [pred prefix tail]
  (apply list pred (conj (vec prefix) tail)))

(tu/deftest-kb a-212-arity-predicate-is-expressible-and-checked
  ;; Above three there is no metatype to reach for — `checks.clj` is literally
  ;; `'{unaryPredicate 1 binaryPredicate 2 ternaryPredicate 3}` — so the `arity` table is
  ;; the only way to state this, and no ceiling exists anywhere in the wff validation.
  ;; The point is to find an unstated assumption about argument count if one is there,
  ;; not to model anything a KB would really say.
  (tu/with-terms [wideP]
    (let [args (vec (repeatedly wide-arity #(tu/tmp-ind "W")))
          s    (apply list wideP args)]
      (v/assert kb (list 'arity wideP wide-arity) U)
      (v/assert kb s U)
      (check (v/ask? kb s U) "a 212-argument sentence asserts and answers")
      (check (= wide-arity (count (rest s))) "and reads back at its stated width")
      (testing "a sentence of the wrong width is refused against the declared arity"
        (check (some? (ex-type #(v/assert kb (apply list wideP (pop args)) U)))
               "211 arguments where 212 were declared")))))

(tu/deftest-kb functional-in-arg-at-position-212
  ;; The motivating shape at scale.  `namesObject` has a two-position determinant; this
  ;; has a **211**-position one, which is where "every position except n" stops being
  ;; notional and starts being work.  Two sentences agreeing on all 211 and differing at
  ;; the 212th are one slot with two fillers.
  (tu/with-terms [wideP]
    (let [prefix  (vec (repeatedly (dec wide-arity) #(tu/tmp-ind "W")))
          [lo hi] (sort [(tu/tmp-ind "Filler") (tu/tmp-ind "Filler")])]
      (v/assert kb (list 'arity wideP wide-arity) U)
      (v/assert kb (list 'functionalInArg wideP wide-arity) U)
      (v/assert kb (wide-sentence wideP prefix lo) U)
      (v/assert kb (wide-sentence wideP prefix hi) U)
      (check (merged? kb lo hi)
             "211 positions agree, so position 212 is determined and the fillers merge")))
  (testing "and a determinant differing anywhere in those 211 is a different slot"
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (tu/with-terms [wideP]
        (let [prefix  (vec (repeatedly (dec wide-arity) #(tu/tmp-ind "W")))
              other   (assoc prefix 4 (tu/tmp-ind "Divergent"))
              [lo hi] (sort [(tu/tmp-ind "Filler") (tu/tmp-ind "Filler")])]
          (v/assert kb (list 'arity wideP wide-arity) U)
          (v/assert kb (list 'functionalInArg wideP wide-arity) U)
          (v/assert kb (wide-sentence wideP prefix lo) U)
          (v/assert kb (wide-sentence wideP other  hi) U)
          (check (not (merged? kb lo hi))
                 "one position out of 211 differs, so these fill two slots and neither binds the other"))))))

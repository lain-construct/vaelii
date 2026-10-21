;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.temporal-capability-test
  "Temporal reasoning, one capability per test: what works, and what ought to.

  Each test is a small demonstration named for the capability it shows.  A capability
  the engine has is asserted as it works.  A capability it ought to have and lacks is
  asserted as it ought to behave, and the test carries `^:red`: it fails today, the
  `:red` selector is the only one that runs it (project.clj, CONTRIBUTING.md §5), and
  the change that makes it pass drops the mark.  A limit the engine has on purpose is an
  ordinary test asserting the limit, and says why it is one.

  This namespace fills the gaps the existing temporal tests leave.  A capability an
  existing test already demonstrates is cited there and not repeated here; the inventory
  is in the PR that added this file.

  The vocabulary is the shipped one: `time.txt` for the interval, instant and calendar
  predicates, `core.txt` for `result`, `contextArgSubrelation` and `genlCx`, and the
  `CxChange` middle theory for the event calculus, and `CxNow` and `CxRealWorldNow` for
  the present.  Nothing here declares a temporal predicate of its own.  `CxTimeFn` is
  the exception, and the first test says why: the shipped KB names it only in comments
  and docs, so a test that wants a time-sliced context declares it, the way
  docs/context-nat.md does.  The red tests also name what issue #181 asks the KB to ship
  and it does not yet: `genlMonad`, `monad_context`, `CxTimeOfFn`/`cxTimeOf` and
  `CxMonadOfFn`/`cxMonadOf`."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.test-util :as tu]))

;; A fresh KB per test, with the upper layer, the CxChange event calculus, CxRealWorld,
;; CxNow and CxRealWorldNow loaded and no prover registered.  Each test registers what it uses, so the opt-in tests can ask the
;; same question before and after.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core-with! '[[CxChange "middle"] [CxRealWorld "middle"]
                                              [CxNow "middle"] [CxRealWorldNow "middle"]]))))

(def ^:private U 'CxUniverse)

(defn- refusal-type
  "The ex-info `:type` `f` throws, or `:answered` when it returns."
  [f]
  (try (f) :answered
       (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(defn- slice
  "The time-sliced context `(CxTimeFn monad time)`."
  ([time] (slice 'CxMonad time))
  ([monad time] (list 'CxTimeFn monad time)))

(defn- declare-cxtimefn!
  "Declare what docs/context-nat.md declares for `CxTimeFn`: its applications are
  contexts, and two of them that differ only in the time argument (position 2) are
  ordered by `subintervalOf` on it.  The calendar constructors and `DatetimeFn` are
  already `unreifiable_function` in time.txt, so the time argument stays readable.

  `CxMonad`, the default monad, is placed under CxWell, so a slice along it is a slice
  of an ordinary context and not of a bare key.  Restating a declaration the KB already
  believes changes nothing, so this stays harmless once the KB ships `CxTimeFn`."
  [kb]
  (v/assert kb '(result CxTimeFn context) U)
  (v/assert kb '(contextArgSubrelation CxTimeFn 2 subintervalOf) U)
  (v/assert kb '(genlCx CxMonad CxWell) U))

(defn- cx-of
  "The `cx/` constant the context slot of the sentex at `h` reified to."
  [kb h]
  (:context (v/sentex kb h)))

(defn- verdict
  "`argue`'s verdict for `s` read from `ctx`: `:true`, `:false`, `:unknown` or
  `:contradiction`."
  [kb s ctx]
  (:verdict (v/argue kb s ctx)))

;; =========================================================================
;; Context slicing — a fact asserted into a time-keyed context
;; =========================================================================

(tu/deftest-kb ^:red cxtimefn-is-declared-in-the-shipped-kb
  ;; The shipped upper layer and CxChange name `CxTimeFn` only in comments today, so every
  ;; other test here declares it itself (declare-cxtimefn!).
  (testing "the KB believes CxTimeFn's applications are contexts, ordered by subintervalOf on the time"
    (is (true? (v/ask? kb '(result CxTimeFn context) U)))
    (is (true? (v/ask? kb '(contextArgSubrelation CxTimeFn 2 subintervalOf) U)))))

(tu/deftest-kb a-write-into-a-time-slice-stores-in-a-cx-context
  ;; (a) The write path reads no declaration.  The application in the context slot
  ;; reifies to an opaque `cx/` constant, and the time argument stays structural inside it.
  (tu/with-terms [p]
    (let [h (v/assert kb (list p) (slice '(DatetimeFn "2000")))
          k (cx-of kb h)]
      (testing "a fact written into (CxTimeFn CxMonad (DatetimeFn \"2000\")) is stored in a cx/ context"
        (is (nat-read/reified-context-symbol? k))
        (is (= [(list 'termOfUnit k (slice '(DatetimeFn "2000")))]
               (map :sentence (v/sentexes-matching kb (list 'termOfUnit k '?e) U)))))
      (testing "and a read naming the cx/ constant answers it, with no declaration"
        (is (true? (v/ask? kb (list p) k)))))))

(tu/deftest-kb a-read-naming-a-time-slice-answers-once-cxtimefn-is-declared
  ;; (b) A read that names the application, not the constant, answers while CxUniverse
  ;; believes `(result CxTimeFn context)`.  Without a declaration such a read is refused
  ;; for :shape, naming what is missing; context_nat_test.clj's
  ;; an-undeclared-context-application-is-stored-and-refused-at-the-read shows that on a
  ;; function no KB declares, so it holds whether or not the KB ships CxTimeFn.
  (tu/with-terms [p]
    (let [ctx (slice '(DatetimeFn "2000"))]
      (v/assert kb (list p) ctx)
      (v/assert kb '(result CxTimeFn context) U)
      (testing "the read naming the application answers the fact"
        (is (true? (v/ask? kb (list p) ctx)))))))

(tu/deftest-kb a-fact-in-a-year-slice-is-visible-from-its-month
  ;; (c) With the ordering declared, the producer computes (genlCx month year) from the
  ;; two terms' fields.  Nobody asserts the edge.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q]
    (let [year  (slice '(DatetimeFn "2000"))
          month (slice '(DatetimeFn "2000-01"))]
      (v/assert kb (list p) year)
      (v/assert kb (list q) month)
      (testing "a fact in (DatetimeFn \"2000\") is visible from (DatetimeFn \"2000-01\")"
        (is (true? (v/ask? kb (list p) month))))
      (testing "the month's own fact is not visible from the year"
        (is (not (v/ask? kb (list q) year)))))))

(tu/deftest-kb ^:red a-slice-nobody-wrote-into-still-inherits
  ;; Today a read resolves the slot by dedup and never mints, so a slice with no fact of
  ;; its own has no cx/ constant and the read is scoped to nothing (docs/context-nat.md,
  ;; "Write and read are symmetric").  What a slice sees ought to follow from what it
  ;; names, not from whether anybody has written into it.
  (declare-cxtimefn! kb)
  (tu/with-terms [p]
    (let [year (slice '(DatetimeFn "2000"))
          jan  (slice '(DatetimeFn "2000-01"))]
      (v/assert kb (list p) year)
      (testing "the year's fact is visible from a month slice that holds no fact of its own"
        (is (true? (v/ask? kb (list p) jan)))
        (is (= :true (verdict kb (list p) jan)))))))

(tu/deftest-kb iris-if-p-is-true-in-2000-it-is-true-in-january-and-unknown-in-2001
  ;; Iris's second example.  "Unknown" is read with `argue`: neither p nor (not p)
  ;; answers.  2001 is a sibling of 2000, so it sees nothing stated for 2000.
  (declare-cxtimefn! kb)
  (tu/with-terms [p]
    (let [y2000 (slice '(DatetimeFn "2000"))
          jan   (slice '(DatetimeFn "2000-01"))
          y2001 (slice '(DatetimeFn "2001"))]
      (v/assert kb (list p) y2000)
      ;; a fact in each of January and 2001 mints those contexts, so the reads below name
      ;; real contexts (see a-slice-nobody-wrote-into-inherits-nothing)
      (tu/with-terms [q r]
        (v/assert kb (list q) y2001)
        (v/assert kb (list r) jan)
        (testing "p stated for 2000 is true in 2000 and in January 2000"
          (is (= :true (verdict kb (list p) y2000)))
          (is (= :true (verdict kb (list p) jan))))
        (testing "and unknown in 2001: neither p nor its negation answers there"
          (is (= :unknown (verdict kb (list p) y2001)))
          (is (not (v/ask? kb (list 'not (list p)) y2001))))))))

(tu/deftest-kb ^:red iris-if-p-is-true-eternally-it-is-true-in-2000
  ;; Iris's first example.  The KB has no "eternal" or "atemporal" context: `atemporal`
  ;; is a type of thing (core.txt), not a way of stating a fact.  The nearest is a fact
  ;; stated unsliced, in CxUniverse — the root every wired context sees.  Today a cx/
  ;; slice is wired by nothing but the computed edges between slices and sees nothing
  ;; above it (docs/contexts.md, "A context outside the topology"), and the year was
  ;; reached only by a hand-asserted genlCx on its cx/ constant.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r]
    (let [y2000 (slice '(DatetimeFn "2000"))
          jan   (slice '(DatetimeFn "2000-01"))]
      (v/assert kb (list p) U)
      (let [k (cx-of kb (v/assert kb (list q) y2000))]
        (v/assert kb (list r) jan)
        (testing "the 2000 slice sees CxUniverse, and p stated there is true in 2000"
          (is (true? (v/sees? kb k U)))
          (is (true? (v/ask? kb (list p) y2000)))
          (is (= :true (verdict kb (list p) y2000))))
        (testing "and in January 2000, with nobody wiring either slice by hand"
          (is (true? (v/ask? kb (list p) jan))))))))

(tu/deftest-kb ^:red a-slice-along-a-monad-under-cxwell-sees-cxwell-and-not-the-reverse
  ;; (d) CxWell is the shipped bottom anchor, below CxChange.  CxMonad sits under it
  ;; (declare-cxtimefn!), so a slice along CxMonad ought to see CxWell through its monad.
  ;; Today there is no edge either way.  The reverse stays closed: a fact true in 2000
  ;; need not be true in general.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q]
    (let [y2000 (slice '(DatetimeFn "2000"))]
      (v/assert kb (list p) 'CxWell)
      (v/assert kb (list q) y2000)
      (testing "a CxWell fact is visible from the 2000 slice"
        (is (true? (v/ask? kb (list p) y2000))))
      (testing "a 2000-slice fact is not visible from CxWell"
        (is (not (v/ask? kb (list q) 'CxWell)))))))

(tu/deftest-kb sibling-month-slices-do-not-see-each-other
  ;; (e) January and February are siblings: neither is a subinterval of the other, so the
  ;; producer orders neither under the other, and each sees only its own facts and the
  ;; year's.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r]
    (let [year (slice '(YearFn 2000))
          jan  (slice '(MonthFn 2000 1))
          feb  (slice '(MonthFn 2000 2))]
      (v/assert kb (list r) year)
      (v/assert kb (list p) jan)
      (v/assert kb (list q) feb)
      (testing "each month sees the year"
        (is (true? (v/ask? kb (list r) jan)))
        (is (true? (v/ask? kb (list r) feb))))
      (testing "and neither month sees the other's facts"
        (is (not (v/ask? kb (list p) feb)))
        (is (not (v/ask? kb (list q) jan)))))))

(defn- two-spellings
  "Write one fact into the `first` spelling of January 2000, then one into the `second`,
  and report which sees the other's fact."
  [kb first second]
  (tu/with-terms [p q]
    (let [k1 (cx-of kb (v/assert kb (list p) first))
          k2 (cx-of kb (v/assert kb (list q) second))]
      {:distinct?           (not= k1 k2)
       :first-sees-second?  (boolean (v/ask? kb (list q) first))
       :second-sees-first?  (boolean (v/ask? kb (list p) second))})))

(tu/deftest-kb ^:red two-spellings-of-one-month-see-each-others-facts
  ;; docs/context-nat.md: (MonthFn 2000 1) and (DatetimeFn "2000-01") name the same
  ;; interval, and the comparator reads both to one field vector.  Today, as context slots,
  ;; they are two expressions and reify to two cx/ constants; each is a subinterval of the
  ;; other, the second edge would close a genlCx cycle and is refused, and the one edge
  ;; that survives is the same in either arrival order: the MonthFn slice sees the
  ;; DatetimeFn slice and not the reverse.  One month ought to see its own facts whichever
  ;; way it is spelled.  Whether the two are one context is
  ;; two-spellings-of-one-month-name-one-context.
  (declare-cxtimefn! kb)
  (testing "MonthFn written first: each spelling sees the other's fact"
    (is (= {:first-sees-second? true :second-sees-first? true}
           (dissoc (two-spellings kb (slice '(MonthFn 2000 1)) (slice '(DatetimeFn "2000-01")))
                   :distinct?))))
  (tu/with-terms [CxOther]
    (v/assert kb (list 'genlCx CxOther 'CxWell) U)
    (testing "DatetimeFn written first, along a fresh monad so both slices are new: the same"
      (is (= {:first-sees-second? true :second-sees-first? true}
             (dissoc (two-spellings kb (slice CxOther '(DatetimeFn "2000-01"))
                                    (slice CxOther '(MonthFn 2000 1)))
                     :distinct?))))))

(tu/deftest-kb ^:red a-slice-sees-its-monad-and-the-monad-does-not-see-the-slice
  ;; `CxStory` in `(CxTimeFn CxStory T)` is the dimension: "the year 2000, along the
  ;; CxStory dimension" (docs/context-nat.md).  A monad context's own time is unbounded
  ;; (issue #181), so it contains every slice's time, and a slice ought to sit under its
  ;; monad.  Today the producer orders slices by the time argument alone and the monad is
  ;; a key and nothing more.  The reverse stays closed: what holds in 2000 need not hold
  ;; in the story at large.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q CxStory]
    (let [y2000 (slice CxStory '(DatetimeFn "2000"))]
      (v/assert kb (list 'genlCx CxStory 'CxWell) U)
      (v/assert kb (list p) CxStory)
      (v/assert kb (list q) y2000)
      (testing "a fact stated in the monad is visible from the monad's 2000 slice"
        (is (true? (v/ask? kb (list p) y2000))))
      (testing "and a slice's fact is not in the monad"
        (is (not (v/ask? kb (list q) CxStory)))))))

(tu/deftest-kb slices-along-two-monads-do-not-see-each-other
  ;; Two slices that differ in the monad argument are not siblings (they differ at a
  ;; position no declaration orders), so the same year along two monads are two unrelated
  ;; contexts, and a month along one does not see the year along the other.
  (declare-cxtimefn! kb)
  (tu/with-terms [p CxNorth CxSouth]
    (v/assert kb (list p) (slice CxNorth '(DatetimeFn "2000")))
    (tu/with-terms [q r]
      (v/assert kb (list q) (slice CxSouth '(DatetimeFn "2000")))
      (v/assert kb (list r) (slice CxSouth '(DatetimeFn "2000-01")))
      (testing "the same year along another monad does not see p"
        (is (not (v/ask? kb (list p) (slice CxSouth '(DatetimeFn "2000"))))))
      (testing "nor does a month along another monad"
        (is (not (v/ask? kb (list p) (slice CxSouth '(DatetimeFn "2000-01")))))))))

(tu/deftest-kb ^:red iris-partially-overlapping-slices-and-their-intersection
  ;; Iris's third example, with the overlap and the intersection given as Allen relations
  ;; between named intervals.  The Allen network entails (subintervalOf AprJun JanJun)
  ;; and (subintervalOf AprJun AprSep) from the two facts below, and the intersection
  ;; slice ought to sit under both on that entailment.  Today the stored-fact oracle the
  ;; producer reads takes only stated subintervalOf facts, never a prover answer.  The
  ;; same question with each interval given by its bounds, and no Allen relation stated,
  ;; is two-partially-overlapping-ranges-and-their-intersection.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :allen)
  (tu/with-terms [p q r JanJun AprSep AprJun]
    (let [h1   (slice JanJun)
          h2   (slice AprSep)
          both (slice AprJun)]
      (v/assert kb (list p) h1)
      (v/assert kb (list q) h2)
      (v/assert kb (list r) both)
      (v/assert kb (list 'overlaps JanJun AprSep) U)
      (v/assert kb (list 'finishes AprJun JanJun) U)
      (v/assert kb (list 'starts AprJun AprSep) U)
      (testing "control: the Allen prover entails that the intersection is inside both"
        (is (true? (v/ask? kb (list 'subintervalOf AprJun JanJun) U)))
        (is (true? (v/ask? kb (list 'subintervalOf AprJun AprSep) U))))
      (testing "neither overlapping slice sees the other's facts"
        (is (not (v/ask? kb (list q) h1)))
        (is (not (v/ask? kb (list p) h2))))
      (testing "the intersection slice sees both, on the entailed subintervalOf alone"
        (is (true? (v/ask? kb (list p) both)))
        (is (true? (v/ask? kb (list q) both))))
      (testing "and neither overlapping slice sees the intersection's own fact"
        (is (not (v/ask? kb (list r) h1)))
        (is (not (v/ask? kb (list r) h2)))))))

(tu/deftest-kb ^:red a-narrative-in-a-time-slice-gets-the-event-calculus
  ;; CxChange is wired under CxUniverse and above CxWell, and CxMonad sits under CxWell,
  ;; so a slice along CxMonad ought to read CxChange's inertia rules through its monad.
  ;; Today a slice sees neither, and the rules do not run over a narrative written into
  ;; one.
  (declare-cxtimefn! kb)
  (tu/with-terms [StateFn Thing Start T1 T2]
    (let [ctx (slice '(DatetimeFn "2000"))
          f   (list StateFn Thing)]
      (v/assert kb (list 'result StateFn 'fluent) U)
      (doseq [s [(list 'time_point T1) (list 'time_point T2) (list 'instantBefore T1 T2)
                 (list 'causal_event Start) (list 'happens Start T1)
                 (list 'initiates Start f T1)]]
        (v/assert kb s ctx))
      (testing "CxChange inertia runs over the narrative: the started state holds at T2"
        (is (true? (v/query? kb (list 'holdsAt f T2) ctx {:max-depth 3})))))))

;; =========================================================================
;; The monad dimension — issue #181, and the isomorphism with time
;; =========================================================================
;; A context has two parts: its monad (which world, story or theory) and its time.
;; `genlMonad` orders monads alone, the way `subintervalOf` orders times alone, and
;; `genlCx` between two contexts is the product: one sees another exactly when its monad
;; is genlMonad-below the other's and its time is inside the other's.  `CxMonadOfFn` and
;; `CxTimeOfFn` take a context apart, and `monad_context` is a context with no temporal
;; part, the type of CxTimeFn's first argument.  Each test below is the monad-side twin
;; of a time-side test above, named in its comment.

(defn- monads!
  "Place each of `ms` under CxWell, so each is an ordinary context and a monad."
  [kb & ms]
  (doseq [m ms] (v/assert kb (list 'genlCx m 'CxWell) U)))

(tu/deftest-kb ^:red the-monad-vocabulary-is-declared-in-the-shipped-kb
  ;; Twin of cxtimefn-is-declared-in-the-shipped-kb.  Issue #181 asks for each of these.
  (testing "genlMonad, a binary relation ordering monads alone"
    (is (true? (v/query? kb '(arity genlMonad 2) U {:max-depth 3}))))
  (testing "monad_context, a context with no temporal part, types CxTimeFn's first argument"
    (is (true? (v/ask? kb '(genl monad_context context) U)))
    (is (true? (v/ask? kb '(arg CxTimeFn 1 monad_context) U))))
  (testing "CxTimeOfFn and cxTimeOf, a context's temporal part, which is a time"
    (is (true? (v/ask? kb '(functionCorrespondingPredicate CxTimeOfFn cxTimeOf) U)))
    (is (true? (v/ask? kb '(result CxTimeOfFn time) U))))
  (testing "CxMonadOfFn and cxMonadOf, a context's monadic part, which is a monad_context"
    (is (true? (v/ask? kb '(functionCorrespondingPredicate CxMonadOfFn cxMonadOf) U)))
    (is (true? (v/ask? kb '(result CxMonadOfFn monad_context) U)))))

(tu/deftest-kb ^:red a-slice-along-a-sub-monad-sees-the-same-time-along-its-super-monad
  ;; Twin of a-fact-in-a-year-slice-is-visible-from-its-month: the same time, with the
  ;; monad narrowing instead of the time.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q CxSuper CxSub]
    (monads! kb CxSuper CxSub)
    (v/assert kb (list 'genlMonad CxSub CxSuper) U)
    (let [sup (slice CxSuper '(YearFn 2000))
          sub (slice CxSub '(YearFn 2000))]
      (v/assert kb (list p) sup)
      (v/assert kb (list q) sub)
      (testing "2000 along the sub-monad sees 2000 along the super-monad"
        (is (true? (v/ask? kb (list p) sub))))
      (testing "and not the reverse"
        (is (not (v/ask? kb (list q) sup)))))))

(tu/deftest-kb ^:red a-slice-sees-a-monad-two-genlmonad-steps-up
  ;; Twin of the entailed-containment half of
  ;; iris-partially-overlapping-slices-and-their-intersection: the ordering is entailed
  ;; (genlMonad is transitive), not stated between the two monads the slices name.
  (declare-cxtimefn! kb)
  (tu/with-terms [p CxTop CxMid CxLow]
    (monads! kb CxTop CxMid CxLow)
    (v/assert kb (list 'genlMonad CxLow CxMid) U)
    (v/assert kb (list 'genlMonad CxMid CxTop) U)
    (tu/with-terms [q]
      (v/assert kb (list p) (slice CxTop '(YearFn 2000)))
      (v/assert kb (list q) (slice CxLow '(YearFn 2000)))
      (testing "2000 along CxLow sees 2000 along CxTop through CxMid"
        (is (true? (v/ask? kb (list 'genlMonad CxLow CxTop) U)))
        (is (true? (v/ask? kb (list p) (slice CxLow '(YearFn 2000)))))))))

(tu/deftest-kb ^:red genlcx-between-slices-is-genlmonad-times-time-containment
  ;; The product rule, over the four slices two monads and two times make.  A slice sees
  ;; another exactly when both its monad and its time are at or below the other's, so of
  ;; the twelve ordered pairs of distinct slices three see and nine do not.  The two
  ;; diagonal pairs are the ones a one-dimensional ordering gets wrong: (sub, 2000) and
  ;; (super, January) each narrow one dimension and widen the other.
  (declare-cxtimefn! kb)
  (tu/with-terms [CxSuper CxSub]
    (monads! kb CxSuper CxSub)
    (v/assert kb (list 'genlMonad CxSub CxSuper) U)
    (let [slices {[:sub :jan]    (slice CxSub '(MonthFn 2000 1))
                  [:sub :year]   (slice CxSub '(YearFn 2000))
                  [:super :jan]  (slice CxSuper '(MonthFn 2000 1))
                  [:super :year] (slice CxSuper '(YearFn 2000))}
          fact   (into {} (for [k (keys slices)]
                            [k (list (tu/tmp-pred (str "fact" (name (first k)) (name (second k)))))]))
          below? (fn [[m t] [m2 t2]] (and (or (= m m2) (= [m m2] [:sub :super]))
                                          (or (= t t2) (= [t t2] [:jan :year]))))]
      (doseq [[k ctx] slices] (v/assert kb (fact k) ctx))
      (doseq [x (keys slices) y (keys slices) :when (not= x y)]
        (testing (str x " sees " y "'s fact exactly when it is below it in both dimensions")
          (is (= (below? x y) (boolean (v/ask? kb (fact y) (slices x))))))))))

(tu/deftest-kb ^:red sibling-sub-monads-each-see-their-super-monad-and-not-each-other
  ;; Twin of sibling-month-slices-do-not-see-each-other.
  ;; slices-along-two-monads-do-not-see-each-other has no common super-monad.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r CxSuper CxNorth CxSouth]
    (monads! kb CxSuper CxNorth CxSouth)
    (v/assert kb (list 'genlMonad CxNorth CxSuper) U)
    (v/assert kb (list 'genlMonad CxSouth CxSuper) U)
    (let [sup   (slice CxSuper '(YearFn 2000))
          north (slice CxNorth '(YearFn 2000))
          south (slice CxSouth '(YearFn 2000))]
      (v/assert kb (list r) sup)
      (v/assert kb (list p) north)
      (v/assert kb (list q) south)
      (testing "each sub-monad's slice sees the super-monad's"
        (is (true? (v/ask? kb (list r) north)))
        (is (true? (v/ask? kb (list r) south))))
      (testing "and neither sees the other's facts"
        (is (not (v/ask? kb (list p) south)))
        (is (not (v/ask? kb (list q) north)))))))

(tu/deftest-kb ^:red a-monad-below-two-monads-sees-both-at-the-same-time
  ;; Twin of iris-partially-overlapping-slices-and-their-intersection: the intersection
  ;; of two monads is a monad genlMonad-below both.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r CxLeft CxRight CxBoth]
    (monads! kb CxLeft CxRight CxBoth)
    (v/assert kb (list 'genlMonad CxBoth CxLeft) U)
    (v/assert kb (list 'genlMonad CxBoth CxRight) U)
    (let [left  (slice CxLeft '(YearFn 2000))
          right (slice CxRight '(YearFn 2000))
          both  (slice CxBoth '(YearFn 2000))]
      (v/assert kb (list p) left)
      (v/assert kb (list q) right)
      (v/assert kb (list r) both)
      (testing "the slice along the monad below both sees both"
        (is (true? (v/ask? kb (list p) both)))
        (is (true? (v/ask? kb (list q) both))))
      (testing "neither of the other two sees the other's fact or the intersection's"
        (is (not (v/ask? kb (list q) left)))
        (is (not (v/ask? kb (list p) right)))
        (is (not (v/ask? kb (list r) left)))
        (is (not (v/ask? kb (list r) right)))))))

(tu/deftest-kb ^:red genlmonad-between-two-monad-contexts-is-their-genlcx
  ;; A monad context's time is unbounded, so between two of them the time half of the
  ;; product always holds and genlCx and genlMonad coincide, each way.
  (tu/with-terms [p CxSuper CxSub CxA CxB]
    (monads! kb CxSuper CxSub CxA CxB)
    (v/assert kb (list 'genlMonad CxSub CxSuper) U)
    (v/assert kb (list p) CxSuper)
    (testing "a stated genlMonad makes the sub-monad see the super-monad"
      (is (true? (v/sees? kb CxSub CxSuper)))
      (is (true? (v/ask? kb (list p) CxSub))))
    (v/assert kb (list 'genlCx CxA CxB) U)
    (testing "a stated genlCx between two monad contexts is a genlMonad"
      (is (true? (v/ask? kb (list 'genlMonad CxA CxB) U))))))

(tu/deftest-kb ^:red cxtimeof-and-cxmonadof-take-a-slice-apart-and-cxtimefn-puts-it-back
  ;; The round trip: (CxTimeFn (CxMonadOfFn S) (CxTimeOfFn S)) names S itself.
  (declare-cxtimefn! kb)
  (tu/with-terms [p CxStory]
    (monads! kb CxStory)
    (let [k (cx-of kb (v/assert kb (list p) (slice CxStory '(YearFn 2000))))]
      (testing "cxTimeOf answers the slice's time and cxMonadOf its monad"
        (is (= [{'?t '(YearFn 2000)}] (v/ask kb (list 'cxTimeOf k '?t) U)))
        (is (= [{'?m CxStory}] (v/ask kb (list 'cxMonadOf k '?m) U))))
      (testing "and the slice rebuilt from its two parts is the same context"
        (is (true? (v/ask? kb (list p) (list 'CxTimeFn (list 'CxMonadOfFn k) (list 'CxTimeOfFn k)))))))))

(tu/deftest-kb ^:red a-monad-context-is-its-own-monad-and-its-time-is-unbounded
  ;; Issue #181: a monadic context's temporal part is unbounded, so every time is inside
  ;; it, and its monadic part is itself.
  (tu/with-terms [CxStory]
    (monads! kb CxStory)
    (testing "a context under CxWell with no temporal part is a monad_context"
      (is (true? (v/ask? kb (list 'monad_context CxStory) U))))
    (testing "its monad is itself"
      (is (= [{'?m CxStory}] (v/ask kb (list 'cxMonadOf CxStory '?m) U))))
    (testing "and the year 1 and the year 9000 are both inside its time"
      (is (true? (v/ask? kb (list 'subintervalOf '(YearFn 1) (list 'CxTimeOfFn CxStory)) U)))
      (is (true? (v/ask? kb (list 'subintervalOf '(YearFn 9000) (list 'CxTimeOfFn CxStory)) U))))))

(tu/deftest-kb ^:red monad-context-types-cxtimefns-first-argument
  ;; Issue #181: CxTimeFn's first argument is untyped today, so a write into a slice of
  ;; CxNow, or of another slice, is stored like any other.  CxNow has a temporal part
  ;; (it moves), and so does a slice, so neither is a monad_context.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r CxStory]
    (monads! kb CxStory)
    (testing "control: a write into a slice along a monad context is stored"
      (is (= :answered (refusal-type #(v/assert kb (list p) (slice CxStory '(YearFn 2000)))))))
    (testing "CxNow and a slice are not monad contexts"
      (is (not (v/ask? kb '(monad_context CxNow) U)))
      (is (not (v/ask? kb (list 'monad_context (cx-of kb (v/assert kb (list r) (slice CxStory '(YearFn 2001))))) U))))
    (testing "a write into (CxTimeFn CxNow …) is refused for its argument type"
      (is (= :arg-type (refusal-type #(v/assert kb (list q) (slice 'CxNow '(YearFn 2000)))))))
    (testing "and so is a write into a slice of a slice spelled with CxTimeFn twice"
      (is (= :arg-type (refusal-type #(v/assert kb (list q)
                                                (slice (slice CxStory '(YearFn 2000))
                                                       '(MonthFn 2000 1)))))))))

(tu/deftest-kb ^:red a-slice-of-a-slice-is-the-slice-of-its-monad-at-the-narrower-time
  ;; Issue #181 defines a slice of a slice through the two parts: January of the slice
  ;; (CxStory, 2000) is (CxTimeFn (CxMonadOfFn S) (MonthFn 2000 1)), which is the slice
  ;; (CxStory, January 2000), and it sees what S holds.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q CxStory]
    (monads! kb CxStory)
    (let [s  (cx-of kb (v/assert kb (list p) (slice CxStory '(YearFn 2000))))
          ss (list 'CxTimeFn (list 'CxMonadOfFn s) '(MonthFn 2000 1))]
      (testing "a write into the slice of S at January lands in (CxStory, January 2000)"
        (is (= (cx-of kb (v/assert kb (list q) ss))
               (cx-of kb (v/assert kb (list q) (slice CxStory '(MonthFn 2000 1)))))))
      (testing "and that slice sees S's fact"
        (is (true? (v/ask? kb (list p) ss)))))))

;; =========================================================================
;; CxNow, the moving present, and temporal projection
;; =========================================================================
;; CxNow is what is true now: a moving, indexical present of no particular world
;; (resources/kb/middle/CxNow.txt).  CxRealWorldNow is the real world's present and sees
;; CxRealWorld and CxNow.  `(CxTimeOfFn CxNow)` names the present, so a sentence about
;; "now" names the time the KB is asked at.  The present is reached through LOWER
;; BOUNDS: a clock reading states `(instantNotBefore now T)`, which stays true for ever
;; after, and what is derived from readings is derived as a bound.  With no upper bound
;; nothing fixes an exact present, so an exact reading ("it is 3:41") and a dated
;; present-tense fact ("today is Saturday") are not stated in CxNow at all.
;;
;; Projection is CxChange's inertia carried across contexts: a fluent started at a
;; moment in one slice still holds at a later moment, until something ends it.  "Later"
;; than a past moment is reached from a reading.  A plain fact of a past slice is not
;; projected: it was true in 2000 and is unknown in 2001.

(def ^:private now '(CxTimeOfFn CxNow))

(defn- reading!
  "A clock reading: in CxNow, now is no earlier than the InstantFn moment `fields`."
  [kb fields]
  (v/assert kb (list 'instantNotBefore now (cons 'InstantFn fields)) 'CxNow))

(defn- real-slice
  "The slice of the real world at `time`."
  [time]
  (slice 'CxRealWorld time))

(defn- fluent!
  "Declare `state-fn` a fluent constructor and return the fluent `(state-fn thing)`."
  [kb state-fn thing]
  (v/assert kb (list 'result state-fn 'fluent) U)
  (list state-fn thing))

(defn- happened!
  "In `ctx`, state that `event` happened at `instant` and `effect` (initiates or
  terminates) `fluent` there."
  [kb ctx event effect fluent instant]
  (doseq [s [(list 'causal_event event) (list 'happens event instant)
             (list effect event fluent instant)]]
    (v/assert kb s ctx)))

(tu/deftest-kb a-fact-true-now-is-true-in-the-real-worlds-present-and-not-timelessly
  ;; CxNow sees CxUniverse; CxRealWorldNow sees CxRealWorld and CxNow; nothing above
  ;; CxNow sees what it states.
  (tu/with-terms [p q]
    (v/assert kb (list p) 'CxNow)
    (v/assert kb (list q) 'CxRealWorld)
    (testing "the real world's present sees both the present and the real world"
      (is (true? (v/sees? kb 'CxRealWorldNow 'CxNow)))
      (is (true? (v/sees? kb 'CxRealWorldNow 'CxRealWorld)))
      (is (true? (v/ask? kb (list p) 'CxRealWorldNow)))
      (is (true? (v/ask? kb (list q) 'CxRealWorldNow))))
    (testing "the present is of no world: CxNow does not see the real world"
      (is (not (v/ask? kb (list q) 'CxNow))))
    (testing "a fact true now is not true timelessly, in general, or in the real world at large"
      (is (not (v/ask? kb (list p) U)))
      (is (not (v/ask? kb (list p) 'CxWell)))
      (is (not (v/ask? kb (list p) 'CxRealWorld))))))

(tu/deftest-kb ^:red cxrealworldnow-is-the-real-world-at-the-present
  ;; The product read back through #181's two functions: its monad is CxRealWorld and its
  ;; time is CxNow's.
  (testing "CxRealWorldNow's monad is CxRealWorld"
    (is (= [{'?m 'CxRealWorld}] (v/ask kb '(cxMonadOf CxRealWorldNow ?m) U))))
  (testing "and its time is the present"
    (is (true? (v/ask? kb (list 'cxTimeOf 'CxRealWorldNow now) U)))))

(tu/deftest-kb ^:red a-later-clock-reading-supersedes-an-earlier-one
  ;; Iris's acceptance test: a reading on Saturday 17 October 2026, then a later one on
  ;; Sunday the 18th.  Both bounds stay true, and the tightest, the earliest the present
  ;; can be, is Sunday's alone.
  (v/add-reasoner kb :point :calendar)
  (reading! kb [2026 10 17 9 0 0])
  (testing "after Saturday's reading: now is no earlier than Saturday, and Sunday is unknown"
    (is (true? (v/ask? kb (list 'instantNotBefore now '(InstantFn 2026 10 17 0 0 0)) 'CxNow)))
    (is (= :unknown (verdict kb (list 'instantNotBefore now '(InstantFn 2026 10 18 0 0 0)) 'CxNow))))
  (reading! kb [2026 10 18 9 0 0])
  (testing "after Sunday's: now is no earlier than Sunday"
    (is (true? (v/ask? kb (list 'instantNotBefore now '(InstantFn 2026 10 18 0 0 0)) 'CxNow))))
  (testing "and the earliest the present can be is Sunday's reading, not Saturday's"
    (is (= [{'?t '(InstantFn 2026 10 18 9 0 0)}]
           (v/ask kb (list 'earliestStartOf now '?t) 'CxNow)))))

(tu/deftest-kb with-no-clock-reading-the-present-is-unknown
  ;; Iris's acceptance test: with no reading nothing places the present, not even after
  ;; the year 1.  Correct by design, and passing today; it stays a test so a change
  ;; that reads the host's clock into the KB breaks it.
  (v/add-reasoner kb :point :calendar)
  (testing "now is neither known to be after nor before the start of the year 1"
    (is (= :unknown (verdict kb (list 'instantNotBefore now '(InstantFn 1 1 1 0 0 0)) 'CxNow))))
  (testing "and no earliest present is answered"
    (is (empty? (v/ask kb (list 'earliestStartOf now '?t) 'CxNow)))))

(tu/deftest-kb ^:red an-exact-present-and-a-dated-present-tense-fact-are-refused-in-cxnow
  ;; Iris's ruling: CxNow holds bounds, never an exact present and never a dated
  ;; present-tense fact; the day and an age are derived from readings, as bounds.  The
  ;; control is a reading, which is stored.
  (testing "control: a lower-bound reading is stored"
    (is (= :answered (refusal-type #(reading! kb [2026 10 21 3 41 0])))))
  (testing "\"it is 3:41\" is refused"
    (is (not= :answered
              (refusal-type #(v/assert kb (list 'instantEqual now '(InstantFn 2026 10 21 3 41 0))
                                       'CxNow)))))
  (testing "\"today is Saturday 17 October 2026\" is refused"
    (is (not= :answered
              (refusal-type #(v/assert kb (list 'includesInstant '(DayFn 2026 10 17) now)
                                       'CxNow))))))

(tu/deftest-kb ^:red age-is-derived-as-a-lower-bound-and-never-as-an-exact-value
  ;; Iris's acceptance test.  Born in 1977, read at no earlier than 17 October 2026: at
  ;; least 48 (a December 1977 birthday is still to come), and not known to be 49 or any
  ;; exact age, because nothing bounds the present from above.  A later reading on
  ;; 1 January 2027 makes it at least 49.  `ageAtLeast` (an organism, an integer number
  ;; of whole years) is a placeholder name: the KB has no age relation, and birthYearOf
  ;; (life.txt) is the only birth fact it has.
  (v/add-reasoner kb :point :calendar)
  (tu/with-terms [Ann]
    (v/assert kb (list 'person Ann) U)
    (v/assert kb (list 'birthYearOf Ann 1977) 'CxRealWorld)
    (reading! kb [2026 10 17 9 0 0])
    (testing "at least 48, and 49 unknown"
      (is (true? (v/query? kb (list 'ageAtLeast Ann 48) 'CxRealWorldNow {:max-depth 3})))
      (is (= :unknown (verdict kb (list 'ageAtLeast Ann 49) 'CxRealWorldNow))))
    (testing "no exact age is answered"
      (is (empty? (v/query kb (list 'ageOf Ann '?n) 'CxRealWorldNow {:max-depth 3}))))
    (reading! kb [2027 1 1 0 0 0])
    (testing "a later reading raises the bound to 49"
      (is (true? (v/query? kb (list 'ageAtLeast Ann 49) 'CxRealWorldNow {:max-depth 3}))))))

(tu/deftest-kb ^:red a-reading-places-now-after-a-past-year-and-inside-no-year
  ;; A reading of 17 October 2026 places the present after all of 2000, and, with no
  ;; upper bound, inside no year: not even 2026.  So the real world's present sits under
  ;; no year slice, and a fact of the real world's 2026 slice is not known to hold now.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :point :calendar)
  (reading! kb [2026 10 17 9 0 0])
  (testing "now is after the end of 2000"
    (is (true? (v/ask? kb (list 'instantNotBefore now '(InstantFn 2001 1 1 0 0 0)) 'CxNow))))
  (testing "and whether 2026 includes now is unknown"
    (is (= :unknown (verdict kb (list 'includesInstant '(YearFn 2026) now) 'CxNow))))
  (tu/with-terms [p]
    (v/assert kb (list p) (real-slice '(YearFn 2026)))
    (testing "so a fact of the real world's 2026 slice is not known now"
      (is (not (v/ask? kb (list p) 'CxRealWorldNow))))))

(tu/deftest-kb ^:red a-past-slice-of-the-real-world-sees-the-real-world-and-not-what-holds-now
  ;; The real world's slice of 2000 sits under its monad CxRealWorld, as any slice sits
  ;; under its monad, and beside CxRealWorldNow rather than under it: what holds now need
  ;; not have held in 2000.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r]
    (let [y2000 (real-slice '(YearFn 2000))]
      (v/assert kb (list p) 'CxRealWorld)
      (v/assert kb (list q) 'CxRealWorldNow)
      (v/assert kb (list r) y2000)
      (testing "the 2000 slice sees a fact of the real world at large"
        (is (true? (v/ask? kb (list p) y2000))))
      (testing "and not a fact true now"
        (is (not (v/ask? kb (list q) y2000)))
        (is (= :unknown (verdict kb (list q) y2000)))))))

(tu/deftest-kb ^:red an-eternal-fact-is-visible-from-now-and-from-every-slice
  ;; Iris's eternal example from every vantage, not one year: a fact stated unsliced in
  ;; CxUniverse holds now, in the past and the future, along the real world and along a
  ;; story, at a year and at a day.
  (declare-cxtimefn! kb)
  (tu/with-terms [p CxStory]
    (v/assert kb (list 'genlCx CxStory 'CxWell) U)
    (v/assert kb (list p) U)
    (testing "control: from CxNow and the real world's present"
      (is (true? (v/ask? kb (list p) 'CxNow)))
      (is (true? (v/ask? kb (list p) 'CxRealWorldNow))))
    (doseq [ctx [(real-slice '(YearFn 2000)) (real-slice '(YearFn 2100))
                 (real-slice '(DayFn 2000 2 29)) (slice CxStory '(YearFn 2000))
                 (slice CxStory '(MonthFn 1066 10))]]
      (testing (str "from " (pr-str ctx))
        (is (true? (v/ask? kb (list p) ctx)))))))

(tu/deftest-kb ^:red a-fluent-started-in-a-past-slice-holds-now
  ;; Projection to the present: a state started in June 2000, stated in the real world's
  ;; 2000 slice, that nothing has ended since, holds now, and the reading is what puts
  ;; now after June 2000.  The question is asked in CxRealWorldNow, which does not see the
  ;; slice: only the fluent crosses, by inertia, and a plain fact of 2000 does not.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar :point)
  (reading! kb [2026 10 17 9 0 0])
  (tu/with-terms [StateFn Thing Start p]
    (let [f   (fluent! kb StateFn Thing)
          y2k (real-slice '(YearFn 2000))]
      (happened! kb y2k Start 'initiates f '(InstantFn 2000 6 1 12 0 0))
      (v/assert kb (list p) y2k)
      (testing "the state holds now"
        (is (true? (v/query? kb (list 'holdsAt f now) 'CxRealWorldNow {:max-depth 3}))))
      (testing "and a plain fact of 2000 is not projected"
        (is (not (v/ask? kb (list p) 'CxRealWorldNow)))))))

(tu/deftest-kb ^:red a-fluent-ended-after-the-past-slice-does-not-hold-now
  ;; No projection past a terminating event: two states start in 2000, one is ended in
  ;; 2005 (stated in the 2005 slice), and only the other holds now.  The first half is the
  ;; positive control, so the second is not answered by projection being absent.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar :point)
  (reading! kb [2026 10 17 9 0 0])
  (tu/with-terms [StateFn Kept Ended Start Stop]
    (let [kept  (fluent! kb StateFn Kept)
          ended (list StateFn Ended)
          y2k   (real-slice '(YearFn 2000))]
      (happened! kb y2k Start 'initiates kept '(InstantFn 2000 6 1 12 0 0))
      (v/assert kb (list 'initiates Start ended '(InstantFn 2000 6 1 12 0 0)) y2k)
      (happened! kb (real-slice '(YearFn 2005)) Stop 'terminates ended '(InstantFn 2005 3 1 12 0 0))
      (testing "the state nothing ended holds now"
        (is (true? (v/query? kb (list 'holdsAt kept now) 'CxRealWorldNow {:max-depth 3}))))
      (testing "the state ended in 2005 does not"
        (is (not (v/query? kb (list 'holdsAt ended now) 'CxRealWorldNow {:max-depth 3})))))))

(tu/deftest-kb ^:red a-fluent-ended-after-the-reading-is-not-known-to-hold-now
  ;; The bound cuts both ways: a state started in 2000 and ended on 1 March 2030 held at
  ;; the reading of 17 October 2026, but now may be past 2030, so whether it holds now is
  ;; unknown, where a state nothing ended holds.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar :point)
  (reading! kb [2026 10 17 9 0 0])
  (tu/with-terms [StateFn Kept Ended Start Stop]
    (let [kept  (fluent! kb StateFn Kept)
          ended (list StateFn Ended)
          y2k   (real-slice '(YearFn 2000))]
      (happened! kb y2k Start 'initiates kept '(InstantFn 2000 6 1 12 0 0))
      (v/assert kb (list 'initiates Start ended '(InstantFn 2000 6 1 12 0 0)) y2k)
      (happened! kb (real-slice '(YearFn 2030)) Stop 'terminates ended '(InstantFn 2030 3 1 12 0 0))
      (testing "the state nothing ended still holds now"
        (is (true? (v/query? kb (list 'holdsAt kept now) 'CxRealWorldNow {:max-depth 3}))))
      (testing "the state ended in 2030 is unknown now, neither held nor ended"
        (is (= :unknown (verdict kb (list 'holdsAt ended now) 'CxRealWorldNow)))
        (is (not (v/query? kb (list 'holdsAt ended now) 'CxRealWorldNow {:max-depth 3})))))))

(tu/deftest-kb projection-from-now-into-a-dated-future-slice-is-unknown-with-only-lower-bounds
  ;; Projection forward, under the lower-bound ruling.  The present has no upper bound,
  ;; so no dated slice is known to lie after now: with a reading of 17 October 2026, now
  ;; may already be past the start of 2027, and a state observed now is neither held nor
  ;; refuted there.  Correct by design under the ruling, and passing today because no
  ;; slice sees anything.  Projection forward from now to a dated future needs an upper
  ;; bound on now, which the ruling does not provide: a question for the spec, not a
  ;; red test.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar :point)
  (reading! kb [2026 10 17 9 0 0])
  (tu/with-terms [StateFn Kept]
    (let [kept (fluent! kb StateFn Kept)
          t27  '(InstantFn 2027 1 1 0 0 0)
          y27  (real-slice '(YearFn 2027))]
      (v/assert kb (list 'holdsAt kept now) 'CxRealWorldNow)
      (testing "control: it holds now, as stated"
        (is (true? (v/ask? kb (list 'holdsAt kept now) 'CxRealWorldNow))))
      (testing "it is unknown at the start of 2027, which now may be past"
        (is (= :unknown (verdict kb (list 'holdsAt kept t27) y27)))))))

;; =========================================================================
;; Slices keyed by other kinds of time
;; =========================================================================
;; Every slice above is keyed by a calendar term or by a named interval ordered by
;; stated or Allen-entailed relations.  These key a slice by a moment, by a time with
;; gaps, and by the same month spelled two ways.

(tu/deftest-kb ^:red two-spellings-of-one-month-name-one-context
  ;; Stronger than two-spellings-of-one-month-see-each-others-facts: the two spellings
  ;; denote one interval, so they are one context, and a write through either lands in
  ;; the same cx/ constant.
  (declare-cxtimefn! kb)
  (testing "MonthFn and DatetimeFn for January 2000 reify to one cx/ context"
    (is (false? (:distinct? (two-spellings kb (slice '(MonthFn 2000 1))
                                           (slice '(DatetimeFn "2000-01"))))))))

(tu/deftest-kb ^:red a-fact-in-a-year-slice-holds-in-a-slice-keyed-by-an-instant-inside-it
  ;; Homogeneity, downward: a fact true throughout 2000 is true at each moment of 2000.
  ;; A slice keyed by an InstantFn moment is ordered under a slice keyed by an interval
  ;; that includes the moment (includesInstant), which is not subintervalOf: a time_point
  ;; is not a time_interval.  Upward it does not hold, by design: a fact stated at one
  ;; moment of 2000 is not thereby true throughout 2000.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q]
    (let [y2000    (slice '(YearFn 2000))
          noon     (slice '(InstantFn 2000 6 1 12 0 0))
          noon2001 (slice '(InstantFn 2001 6 1 12 0 0))]
      (v/assert kb (list p) y2000)
      (v/assert kb (list q) noon)
      (testing "the year's fact holds in the slice keyed by a moment inside the year"
        (is (true? (v/ask? kb (list p) noon))))
      (testing "and not in the slice keyed by a moment of 2001"
        (is (not (v/ask? kb (list p) noon2001))))
      (testing "the moment's own fact is not lifted to the year"
        (is (not (v/ask? kb (list q) y2000)))))))

(tu/deftest-kb ^:red a-slice-keyed-by-an-intermittent-time-sits-between-its-pieces-and-its-whole
  ;; An intermittent_time has gaps, so it is not a time_interval and subintervalOf, the
  ;; ordering CxTimeFn is declared over, does not apply to it.  The weekends of 2000 are
  ;; part of 2000, and 1 January 2000, a Saturday, is part of the weekends.  A slice keyed
  ;; by the weekends ought to see the year, and the Saturday's slice ought to see the
  ;; weekends'; 3 January 2000, a Monday, is in a gap and sees nothing of the weekends.
  (declare-cxtimefn! kb)
  (tu/with-terms [p q r Weekends2000]
    (v/assert kb (list 'intermittent_time Weekends2000) U)
    (v/assert kb (list 'partOf Weekends2000 '(YearFn 2000)) U)
    (v/assert kb (list 'partOf '(DayFn 2000 1 1) Weekends2000) U)
    (v/assert kb (list 'temporallyDisjoint '(DayFn 2000 1 3) Weekends2000) U)
    (let [year     (slice '(YearFn 2000))
          weekends (slice Weekends2000)
          saturday (slice '(DayFn 2000 1 1))
          monday   (slice '(DayFn 2000 1 3))]
      (v/assert kb (list p) year)
      (v/assert kb (list q) weekends)
      (v/assert kb (list r) monday)
      (testing "the weekends' slice sees the year's fact"
        (is (true? (v/ask? kb (list p) weekends))))
      (testing "a Saturday's slice sees the weekends' fact, and the year's"
        (is (true? (v/ask? kb (list q) saturday)))
        (is (true? (v/ask? kb (list p) saturday))))
      (testing "a Monday's slice sees the year's fact and not the weekends'"
        (is (true? (v/ask? kb (list p) monday)))
        (is (not (v/ask? kb (list q) monday)))))))

;; =========================================================================
;; CxChange — two transitions in a row
;; =========================================================================

(defn- narrative!
  "A fresh context below CxChange holding `facts`, returned."
  [kb facts]
  (let [ctx (tu/tmp-ctx "Story")]
    (v/assert kb (list 'genlCx ctx 'CxChange) 'CxChange)
    (run! #(v/assert kb % ctx) facts)
    ctx))

(defn- holds-at? [kb ctx f t]
  (v/query? kb (list 'holdsAt f t) ctx {:max-depth 3}))

(tu/deftest-kb a-state-that-goes-draft-ready-draft-follows-both-transitions
  ;; A document starts as a draft, is promoted to ready at T1, and demoted back to draft
  ;; at T2.  Each event initiates one state and terminates the other.  Draft holds before
  ;; T1 from `initially`, and after T2 from the demotion's initiation, so the second draft
  ;; is a second stretch of the same fluent.
  (tu/with-terms [DraftFn ReadyFn Doc Promote Demote T0 T1 T15 T2 T3]
    (let [draft (list DraftFn Doc)
          ready (list ReadyFn Doc)
          ctx   (narrative! kb
                            (concat
                             [(list 'result DraftFn 'fluent) (list 'result ReadyFn 'fluent)]
                             (for [t [T0 T1 T15 T2 T3]] (list 'time_point t))
                             [(list 'instantBefore T0 T1) (list 'instantBefore T1 T15)
                              (list 'instantBefore T15 T2) (list 'instantBefore T2 T3)
                              (list 'initially draft)
                              (list 'causal_event Promote) (list 'causal_event Demote)
                              (list 'happens Promote T1)
                              (list 'initiates Promote ready T1)
                              (list 'terminates Promote draft T1)
                              (list 'happens Demote T2)
                              (list 'initiates Demote draft T2)
                              (list 'terminates Demote ready T2)]))]
      (testing "draft before the promotion, ready between the two events"
        (is (holds-at? kb ctx draft T0))
        (is (not (holds-at? kb ctx ready T0)))
        (is (holds-at? kb ctx ready T15))
        (is (not (holds-at? kb ctx draft T15))))
      (testing "draft again after the demotion, and no longer ready"
        (is (holds-at? kb ctx draft T3))
        (is (not (holds-at? kb ctx ready T3))))
      (testing "at the instant of an event the old state still holds and the new one does not"
        (is (holds-at? kb ctx draft T1))
        (is (not (holds-at? kb ctx ready T1)))
        (is (holds-at? kb ctx ready T2))
        (is (not (holds-at? kb ctx draft T2))))
      (testing "the derived reasons are stored: ready was clipped between T1 and T3"
        (is (seq (v/sentexes-matching kb (list 'clipped T1 ready T3) ctx)))
        (is (seq (v/sentexes-matching kb (list 'clippedBefore draft T15) ctx)))))))

(defn- equality-narrative
  "A fluent started at T1 and stopped at T2, where T2 is ordered before T3 only through
  an `instantEqual`: T1 < T2, T2 = T2b, T2b < T3.  Returns `[ctx fluent T1 T3]`."
  [kb StateFn Thing Start Stop T1 T2 T2b T3]
  (let [f (list StateFn Thing)]
    [(narrative! kb
                 (concat
                  [(list 'result StateFn 'fluent)]
                  (for [t [T1 T2 T2b T3]] (list 'time_point t))
                  [(list 'instantBefore T1 T2) (list 'instantEqual T2 T2b)
                   (list 'instantBefore T2b T3)
                   (list 'causal_event Start) (list 'causal_event Stop)
                   (list 'happens Start T1) (list 'initiates Start f T1)
                   (list 'happens Stop T2) (list 'terminates Stop f T2)]))
     f T1 T3]))

(tu/deftest-kb clipped-reads-an-order-the-point-prover-entails-once-it-is-registered
  ;; docs/time.md ("What clipped can see") and CxChange.txt say an ordering only the
  ;; point calculus entails is not an edge and is not read by clipped.  With :point
  ;; registered it is: the forward join's instantBefore antecedent is answered by the
  ;; point prover, which carries support, so clipped fires through an instantEqual.
  (tu/with-terms [StateFn Thing Start Stop T1 T2 T2b T3]
    (let [[ctx f t1 t3] (equality-narrative kb StateFn Thing Start Stop T1 T2 T2b T3)]
      (testing "without :point, T1 is not ordered before T3, so neither clipped nor inertia reaches T3"
        (is (not (v/ask? kb (list 'instantBefore t1 t3) ctx)))
        (is (empty? (v/sentexes-matching kb (list 'clipped '?a f '?b) ctx)))
        (is (not (holds-at? kb ctx f t3))))))
  (v/add-reasoner kb :point)
  (tu/with-terms [StateFn Thing Start Stop T1 T2 T2b T3]
    (let [[ctx f t1 t3] (equality-narrative kb StateFn Thing Start Stop T1 T2 T2b T3)]
      (testing "with :point, T1 is before T3 through the equality, clipped fires, and inertia stops"
        (is (true? (v/ask? kb (list 'instantBefore t1 t3) ctx)))
        (is (seq (v/sentexes-matching kb (list 'clipped t1 f t3) ctx)))
        (is (not (holds-at? kb ctx f t3)))))))

;; =========================================================================
;; Opt-in provers — the calendar clock and the instant-inclusion reader
;; =========================================================================
;; The interval, point, metric and duration provers each already have a test asking the
;; same question through the default registry and the registered prover; see the matrix.
;; The calendar clock and includesInstant did not.

(tu/deftest-kb the-calendar-clock-is-opt-in
  (testing "without :calendar a year has no computed start and 1999 does not meet 2000"
    (is (empty? (v/ask kb '(startOf (YearFn 2000) ?i) U)))
    (is (not (v/ask? kb '(meets (YearFn 1999) (YearFn 2000)) U))))
  (v/add-reasoner kb :calendar)
  (testing "with it, the same goals answer from the fields"
    (is (= [{'?i '(InstantFn 2000 1 1 0 0 0)}] (v/ask kb '(startOf (YearFn 2000) ?i) U)))
    (is (true? (v/ask? kb '(meets (YearFn 1999) (YearFn 2000)) U)))))

(tu/deftest-kb the-instant-inclusion-reader-is-opt-in
  (tu/with-terms [Party Noon Dusk]
    (doseq [s [(list 'instantBefore (list 'StartFn Party) Noon)
               (list 'instantBefore Noon (list 'EndFn Party))
               (list 'instantBefore (list 'EndFn Party) Dusk)]]
      (v/assert kb s U))
    (v/add-reasoner kb :point)
    (testing "with only :point, a moment inside a party's bounds is unknown"
      (is (= :unknown (verdict kb (list 'includesInstant Party Noon) U))))
    (v/add-reasoner kb :includes-instant)
    (testing "with :includes-instant, it is inside, and a moment after the end is not"
      (is (= :true (verdict kb (list 'includesInstant Party Noon) U)))
      (is (= :false (verdict kb (list 'includesInstant Party Dusk) U))))))

;; =========================================================================
;; What the docs list as not reached, and ought to be
;; =========================================================================

(tu/deftest-kb ^:red a-stated-allen-relation-constrains-the-points
  ;; docs/time.md, "What it does not do": today the narrowing runs from points to
  ;; intervals only.  (before A B) means A ends before B starts.
  (v/add-reasoner kb :allen :point)
  (tu/with-terms [A B]
    (v/assert kb (list 'before A B) U)
    (is (true? (v/ask? kb (list 'before A B) U)))
    (testing "A's end is before B's start, from (before A B)"
      (is (true? (v/ask? kb (list 'instantBefore (list 'EndFn A) (list 'StartFn B)) U))))))

(tu/deftest-kb ^:red a-calendar-term-is-a-node-of-the-allen-network
  ;; docs/time.md: today the clock answers a pair and does not fold its relations into
  ;; the interval network, so a stated relation to one month does not compose with the
  ;; clock's relation between two months.
  (v/add-reasoner kb :allen :calendar)
  (tu/with-terms [Breakfast]
    (v/assert kb (list 'before Breakfast '(MonthFn 2000 1)) U)
    (testing "control: the clock orders the two months"
      (is (true? (v/ask? kb '(before (MonthFn 2000 1) (MonthFn 2000 3)) U))))
    (testing "a stated relation composes with a clock relation"
      (is (true? (v/ask? kb (list 'before Breakfast '(MonthFn 2000 3)) U))))))

(tu/deftest-kb ^:red a-conjunction-that-binds-the-calendar-term-elsewhere-answers
  ;; docs/time.md: today the planner costs the `during` literal by stored facts, finds
  ;; none, runs it first with ?m open, and the clock refuses an open end.  The clock
  ;; refusing an open end is right (calendar_test.clj's
  ;; an-open-end-answers-nothing-rather-than-enumerating-the-calendar); running it first
  ;; is not.
  (v/add-reasoner kb :calendar)
  (tu/with-terms [holiday]
    (v/assert kb (list holiday '(MonthFn 2000 3)) U)
    (testing "control: the ground question answers"
      (is (true? (v/ask? kb '(during (MonthFn 2000 3) (YearFn 2000)) U))))
    (testing "the conjunction binds ?m from the stored fact and the clock answers the rest"
      (is (= [{'?m '(MonthFn 2000 3)}]
             (v/query kb [(list holiday '?m) '(during ?m (YearFn 2000))] U {:max-depth 1}))))))

(tu/deftest-kb ^:red a-forward-rule-fires-on-a-clock-answer
  ;; docs/time.md: today a forward antecedent is answered through solve-computed, which
  ;; drops an answer with empty support, and the clock's support is empty by construction.
  (v/add-reasoner kb :calendar)
  (tu/with-terms [CxCal holiday holidayIn2000]
    (v/assert kb (list 'genlCx CxCal U) U)
    (v/assert kb (list holiday '(MonthFn 2000 3)) CxCal)
    (v/assert-rule kb [(list holiday '?m) '(subintervalOf ?m (YearFn 2000))]
                   (list holidayIn2000 '?m) CxCal {:direction :forward})
    (testing "a forward rule whose antecedent only the clock answers fires"
      (is (= [(list holidayIn2000 '(MonthFn 2000 3))]
             (map :sentence (v/sentexes-matching kb (list holidayIn2000 '?m) CxCal)))))))

(tu/deftest-kb ^:red metric-gap-and-length-for-calendar-terms
  ;; docs/time.md: today the metric prover's nodes are atomic terms, so an InstantFn moment
  ;; is not one, and nothing converts a field vector to a magnitude.  2000 is a leap year:
  ;; 366 days of 86400 seconds.
  (v/add-reasoner kb :calendar :metric-time :duration)
  (doseq [s ['(dimensionOf Second Duration) '(dimensionOf Hour Duration)
             '(conversionFactor Second Second 1) '(conversionFactor Hour Second 3600)]]
    (v/assert kb s U))
  (tu/with-terms [P Q R]
    (v/assert kb (list 'temporalDistance P Q '(QuantityFn 1 Hour)) U)
    (v/assert kb (list 'temporalDistance Q R '(QuantityFn 1 Hour)) U)
    (testing "control: two stated gaps between named moments compose"
      (is (= [{'?d '(QuantityFn 7200 Second)}]
             (v/ask kb (list 'temporalDistance P R '?d) U)))))
  (testing "the gap between two computed moments an hour apart"
    (is (= [{'?d '(QuantityFn 3600 Second)}]
           (v/ask kb '(temporalDistance (InstantFn 2000 1 1 0 0 0)
                                        (InstantFn 2000 1 1 1 0 0) ?d) U))))
  (testing "the length of a calendar year"
    (is (= [{'?d '(QuantityFn 31622400 Second)}]
           (v/ask kb '(totalDuration (list (YearFn 2000)) ?d) U)))))

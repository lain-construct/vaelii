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
  `CxChange` middle theory for the event calculus.  Nothing here declares a temporal
  predicate of its own.  `CxTimeFn` is the exception, and the first test says why: the
  shipped KB names it only in comments and docs, so a test that wants a time-sliced
  context declares it, the way docs/context-nat.md does."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.nat-read :as nat-read]
            [vaelii.test-util :as tu]))

;; A fresh KB per test, with the upper layer and the CxChange event calculus loaded and
;; no prover registered.  Each test registers what it uses, so the opt-in tests can ask the
;; same question before and after.
(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core-with! '[[CxChange "middle"]]))))

(def ^:private U 'CxUniverse)

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

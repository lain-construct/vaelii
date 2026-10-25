;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.pr-status-true-when-test
  "A pull request's status, end to end, in the TRUE-WHEN design: a notifier pushes the
  status transitions, each status is true over the time it held, a watermark says how
  far the record is complete, and the status as of the watermark is read with the time
  region that supports it.  No temporal projection: Iris ruled on 2026-10-24 to start
  with true-when and leave projection for later, so every answer is read from what was
  written (level 1), never carried forward past it.

  The watermark is written as Iris ruled it:

    (ist (CxTimeFn <monad> (IntervalBeforeFn W)) (closed_extent_predicate prStatus))

  — up to and including W, along the PR's monad, the status record is complete, so a
  status not recorded there is false there rather than unknown.

  `IntervalBeforeFn` is not in the shipped KB: time.txt has no function naming the time
  before a moment.  It is used here only inside `^:red` tests, as Iris's ruling spells it.
  `prStatus` and the request bookkeeping are the test's own domain terms, temporaries in
  the way temporal_capability_test.clj's `StateFn` is.  `CxTimeFn` is declared here as
  that namespace declares it.

  W itself is inside (IntervalBeforeFn W): the non-strict form includes its boundary, and
  IntervalStrictlyBeforeFn is the form that excludes it (Iris, 2026-10-24).  Completeness
  through W is therefore inclusive, unlike a status's own [start, end) stretch, and the
  status \"as of W\" is read at W."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh
                     #(doto (tu/fresh)
                        (tu/load-core-with! '[[CxChange "middle"] [CxRealWorld "middle"]
                                              [CxNow "middle"] [CxRealWorldNow "middle"]]))))

(def ^:private U 'CxUniverse)

(defn- slice
  "The time-sliced context `(CxTimeFn monad time)`."
  [monad time]
  (list 'CxTimeFn monad time))

(defn- declare-cxtimefn!
  "What docs/context-nat.md declares for `CxTimeFn`, as temporal_capability_test.clj
  declares it."
  [kb]
  (v/assert kb '(result CxTimeFn context) U)
  (v/assert kb '(contextArgSubrelation CxTimeFn 2 subintervalOf) U))

(defn- at
  "The InstantFn moment of October 2026 on `day` at `h`:`m`:`s`."
  ([day] (at day 0 0 0))
  ([day h m s] (list 'InstantFn 2026 10 day h m s)))

(defn- mint!
  "Write a fresh fact into each of `ctxs`, so a read naming one names a real context
  (temporal_capability_test.clj, a-slice-nobody-wrote-into-still-inherits)."
  [kb & ctxs]
  (doseq [c ctxs] (v/assert kb (list (tu/tmp-pred "mint")) c)))

(defn- spelled
  "The context term the `cx/` constant `k` was minted from, or `k` itself."
  [kb k]
  (or (some #(get % '?e) (v/ask kb (list 'natFormula k '?e) U)) k))

(defn- true-in
  "In which contexts is the ground sentence `s` true: the witnesses a variable-context
  read unifies into `?where`, each spelled as a context term.  vaelii.true-in-contexts-test
  states the inverse query and the choice of a symbolic region."
  [kb s]
  (into #{} (map #(spelled kb (get % '?where))) (v/ask kb s '?where)))

(defn- verdict [kb s ctx] (:verdict (v/argue kb s ctx)))

;; ---- the notifier --------------------------------------------------------------

(defn- transition!
  "The notifier's push of one transition: `status` holds from the moment `from` along
  `monad`, true over the stretch `stretch` (a named time_interval that starts at `from`),
  and `previous`, the stretch of the status before it when there is one, ends at `from`.
  A stretch's end is stated only when the next transition arrives, so the current
  status's stretch has a known start and an unknown end."
  [kb {:keys [prStatus monad pr]} status stretch from previous]
  (v/assert kb (list 'time_interval stretch) U)
  (v/assert kb (list 'startOf stretch from) U)
  (when previous (v/assert kb (list 'endOf previous from) U))
  (v/assert kb (list prStatus pr status) (slice monad stretch)))

(defn- watermark!
  "The notifier's push of a watermark `w`: the status record along `monad` is complete
  before `w`, and the current status's stretch `current` has not ended before `w`.  The
  push is `push`, and when it answers an on-demand request, `request` names it."
  [kb {:keys [prStatus monad answersRequest pushWatermark]} push w current request]
  (v/assert kb (list 'ist (slice monad (list 'IntervalBeforeFn w))
                     (list 'closed_extent_predicate prStatus))
            U)
  (v/assert kb (list 'instantNotBefore (list 'EndFn current) w) U)
  (v/assert kb (list pushWatermark push w) monad)
  (when request (v/assert kb (list answersRequest push request) monad)))

(defn- refresh-watermarks
  "The watermarks of the pushes that answer the on-demand request `request`."
  [kb {:keys [monad answersRequest pushWatermark]} request]
  (set (map #(get % '?w)
            (v/query kb [(list answersRequest '?push request) (list pushWatermark '?push '?w)]
                     monad {}))))

(tu/deftest-kb ^:red pr-status-as-of-the-watermark-is-read-with-its-supported-region-and-a-stale-watermark-is-refreshed-on-demand
  ;; One pull request along its own monad, CxGitHub.  The notifier pushes Draft on 1
  ;; October, Open on 3 October and Merged on 5 October, then a watermark at midnight
  ;; starting 6 October.  Read in level 1, with no projection:
  ;;
  ;; - as of the watermark, the status is Merged, and Draft and Open are false there, by
  ;;   the closed extent the watermark grants and not by any stored negation;
  ;; - Merged's supported region is its stretch: it starts on 5 October, that start is
  ;;   inside it, no end is answered (none was guessed), and the end is known to be no
  ;;   earlier than the watermark;
  ;; - on 10 October, after the watermark, nothing is known: neither Merged nor its
  ;;   absence.
  ;;
  ;; Then the asker requests a refresh with id R1.  A notification queued before the
  ;; request arrives first: it carries the earlier request id R0 and a watermark of 8
  ;; October.  It is not the refresh — it answers no R1, and 10 October is still past its
  ;; watermark, so the re-ask is still unknown.  The push answering R1 carries a
  ;; watermark of 11 October, and the re-ask on 10 October answers from it.
  ;;
  ;; Today nothing ships IntervalBeforeFn, and no slice keyed by an instant is ordered
  ;; under the interval holding it, so no read at a moment sees the stretches or the
  ;; watermark's grant.
  (declare-cxtimefn! kb)
  (v/add-reasoner kb :calendar :point :includes-instant)
  (tu/with-terms [prStatus answersRequest pushWatermark CxGitHub PR219
                  Draft Open Merged DraftStretch OpenStretch MergedStretch
                  FirstPush QueuedPush RefreshPush R0 R1]
    (v/assert kb (list 'genlCx CxGitHub 'CxWell) U)
    (let [env      {:prStatus prStatus :monad CxGitHub :pr PR219
                    :answersRequest answersRequest :pushWatermark pushWatermark}
          status   (fn [s] (list prStatus PR219 s))
          w1       (at 6)
          as-of-w1 (slice CxGitHub w1)
          later    (slice CxGitHub (at 10 12 0 0))]
      (transition! kb env Draft DraftStretch (at 1) nil)
      (transition! kb env Open OpenStretch (at 3) DraftStretch)
      (transition! kb env Merged MergedStretch (at 5) OpenStretch)
      (watermark! kb env FirstPush w1 MergedStretch nil)
      (mint! kb as-of-w1 later)

      (testing "control: the stretches are ordered, and Merged's end is not before the watermark"
        (is (true? (v/ask? kb (list 'instantBefore (at 1) (at 3)) U)))
        (is (true? (v/ask? kb (list 'instantNotBefore (list 'EndFn MergedStretch) w1) U))))

      (testing "as of the watermark the status is Merged, and only Merged"
        (is (= [{'?s Merged}] (v/ask kb (list prStatus PR219 '?s) as-of-w1)))
        (is (= :true (verdict kb (status Merged) as-of-w1))))
      (testing "and Draft and Open are false there, by the watermark's closed extent"
        (is (true? (v/ask? kb (list 'not (status Draft)) as-of-w1)))
        (is (true? (v/ask? kb (list 'not (status Open)) as-of-w1)))
        (is (= :false (verdict kb (status Open) as-of-w1))))

      (testing "Merged's supported region is its stretch along CxGitHub"
        (is (= #{(slice CxGitHub MergedStretch)} (true-in kb (status Merged)))))
      (testing "which starts on 5 October, inclusively"
        (is (= [{'?i (at 5)}] (v/ask kb (list 'startOf MergedStretch '?i) U)))
        (is (true? (v/ask? kb (list 'includesInstant MergedStretch (at 5)) U))))
      (testing "and has no end answered, only an end no earlier than the watermark"
        (is (empty? (v/ask kb (list 'endOf MergedStretch '?i) U)))
        (is (true? (v/ask? kb (list 'instantNotBefore (list 'EndFn MergedStretch) w1) U))))

      (testing "after the watermark nothing is projected: on 10 October the status is unknown"
        (is (= :unknown (verdict kb (status Merged) later)))
        (is (= :unknown (verdict kb (status Open) later))))

      ;; the refresh: request R1, an older queued notification first, then the answer
      (watermark! kb env QueuedPush (at 8) MergedStretch R0)
      (testing "the queued notification is not the refresh: it answers R0, not R1"
        (is (= #{} (refresh-watermarks kb env R1)))
        (is (= #{(at 8)} (refresh-watermarks kb env R0))))
      (testing "and 10 October is past its watermark, so the re-ask is still unknown"
        (is (= :unknown (verdict kb (status Merged) later)))
        (is (= :unknown (verdict kb (status Open) later))))

      (watermark! kb env RefreshPush (at 11) MergedStretch R1)
      (testing "the push answering R1 refreshes the watermark to 11 October"
        (is (= #{(at 11)} (refresh-watermarks kb env R1))))
      (testing "and the re-ask on 10 October answers from it: Merged, and Open false"
        (is (= [{'?s Merged}] (v/ask kb (list prStatus PR219 '?s) later)))
        (is (= :true (verdict kb (status Merged) later)))
        (is (= :false (verdict kb (status Open) later))))
      (testing "Merged's supported region is still its stretch, now known to last to 11 October"
        (is (= #{(slice CxGitHub MergedStretch)} (true-in kb (status Merged))))
        (is (true? (v/ask? kb (list 'instantNotBefore (list 'EndFn MergedStretch) (at 11)) U)))
        (is (empty? (v/ask kb (list 'endOf MergedStretch '?i) U)))))))

;; ---- the interval quartet: Allen relations that need w's closed bound -----------
;;
;; Iris proposed four readings of "before/after a moment w" for the watermark style
;; above: `IntervalStrictlyBeforeFn`/`IntervalBeforeFn` and their after-facing mirrors
;; `IntervalStrictlyAfterFn`/`IntervalAfterFn` (2026-10-24). None of the four is in the
;; shipped KB. `time.txt`'s `startOf`/`endOf` are half-open — [start, end) — so
;; `IntervalStrictlyBeforeFn w` (no start, excludes w) and `IntervalAfterFn w` (no end,
;; includes w) are statable today with the ordinary convention: an ordinary `endOf` or
;; `startOf` fact at `w` says exactly what each means. `IntervalBeforeFn w` (no start,
;; INCLUDES w) and `IntervalStrictlyAfterFn w` (no end, EXCLUDES w) are not: an ordinary
;; `endOf`/`startOf` fact at `w` would say the half-open opposite of what each means, so
;; the only thing today's vocabulary can truthfully say of either is an `includesInstant`
;; membership fact — option 🇦 of the two the PR weighed for them. No bound, so no Allen
;; relation reading `startOf`/`endOf` can place either one against anything. A closed/open
;; bound marker (an `endOfInclusive`-style predicate nobody has written, option 🇨) would
;; let the same queries succeed by handing the algebra the missing endpoint.
;;
;; `interval-quartet!` below states exactly what today's vocabulary can truthfully state —
;; the 🇦 shape, for `before-w` and `strictly-after-w` — and every `is` in the red group
;; names the 🇨 answer: the one a closed/open marker would make true, that membership alone
;; cannot derive.
;;
;; A prior gap, found by running this group: the shipped `:allen`/`:point` reasoners do
;; not, today, turn an ORDINARY stored `startOf`/`endOf` pair into a derivable Allen
;; relation for a non-calendar individual at all — `registering-allen-makes-an-entailed-
;; relation-derivable` (public_api_test.clj) composes `before` from two *stated* `before`
;; facts, never from endpoints, and `a-calendar-term-stops-a-calculus-running-alone`
;; (calendar_test.clj) gets its endpoint-to-relation derivation from the `:calendar`
;; channel reading calendar-constructor fields structurally, a channel `IntervalBeforeFn`
;; and friends do not have. So `strictly-before-w-meets-after-w` below — which needs
;; nothing but the quartet's two ordinary, already-statable bounds — is red for this
;; reason alone, before the closed/open-marker question ever comes up; every row in the
;; red group after it is red for this reason too, and the rows that single out
;; `before-w`/`strictly-after-w` would need the marker *as well*, once this one is fixed.
(defn- interval-quartet!
  "Stands up the quartet of `w`-relative intervals in `kb`, plus two ordinary dated
  intervals to compare them against. `strictly-before-w` gets an ordinary `endOf` at `w`
  (excludes it); `after-w` gets an ordinary `startOf` at `w` (includes it) — both
  statable with today's half-open vocabulary alone. `before-w` gets only the
  `includesInstant` membership fact at `w`, all today's vocabulary can truthfully say of
  a closed bound; `strictly-after-w` gets nothing stated at all, for the mirror reason.
  `dated-ending-at-w` is the ordinary interval `[2000-01-01, w)`; `dated-starting-at-w` is
  `[w, 2027-01-01)`."
  [kb {:keys [w strictly-before-w before-w after-w strictly-after-w
              dated-ending-at-w dated-starting-at-w]}]
  (doseq [i [strictly-before-w before-w after-w strictly-after-w
             dated-ending-at-w dated-starting-at-w]]
    (v/assert kb (list 'time_interval i) U))
  (v/assert kb (list 'endOf strictly-before-w w) U)
  (v/assert kb (list 'startOf after-w w) U)
  (v/assert kb (list 'includesInstant before-w w) U)
  (v/assert kb (list 'startOf dated-ending-at-w (list 'InstantFn 2000 1 1 0 0 0)) U)
  (v/assert kb (list 'endOf dated-ending-at-w w) U)
  (v/assert kb (list 'startOf dated-starting-at-w w) U)
  (v/assert kb (list 'endOf dated-starting-at-w (list 'InstantFn 2027 1 1 0 0 0)) U))

(defn- quartet-at
  "The quartet's four `IntervalBeforeFn`-family terms at the instant `w`, keyed the way
  `interval-quartet!` wants, plus `w` and the caller's two dated-interval individuals."
  [w dated-ending-at-w dated-starting-at-w]
  {:w w
   :strictly-before-w (list 'IntervalStrictlyBeforeFn w)
   :before-w          (list 'IntervalBeforeFn w)
   :after-w           (list 'IntervalAfterFn w)
   :strictly-after-w  (list 'IntervalStrictlyAfterFn w)
   :dated-ending-at-w dated-ending-at-w
   :dated-starting-at-w dated-starting-at-w})

(defn- run-allen-table!
  "Runs `table` — each row `[desc goal expected reason]` — as one `is` per row inside a
  `testing` named `desc`, read against `kb` at `ctx`. `reason` is not asserted: it is here
  so a failing row's red reason reads next to the row that fails."
  [kb ctx table]
  (doseq [[desc goal expected _reason] table]
    (testing desc
      (is (= expected (verdict kb goal ctx))))))

(tu/deftest-kb ^:red strictly-before-w-meets-after-w
  ;; Meant as the control: this needs only the quartet's two ordinary-bound members, not
  ;; the closed/open marker the red group below depends on — `meets` reads only
  ;; `(endOf strictly-before-w)` and `(startOf after-w)`, both statable today with the
  ;; ordinary half-open convention, no marker involved. It is red anyway, confirmed by
  ;; running it: `:allen`/`:point`, registered, do not derive a relation from a stored
  ;; `startOf`/`endOf` pair on a non-calendar individual today (see the comment above) —
  ;; only compose one from other *stated* relations, or read one off a calendar term's
  ;; fields. So this is red for that prior reason, and would still need fixing even
  ;; though it names no closed/open bound at all.
  (v/add-reasoner kb :allen :point :calendar :includes-instant)
  (tu/with-terms [DatedEndingAtW DatedStartingAtW]
    (let [w (at 6)
          {:keys [strictly-before-w after-w] :as terms}
          (quartet-at w DatedEndingAtW DatedStartingAtW)]
      (interval-quartet! kb terms)
      (is (= :true (verdict kb (list 'meets strictly-before-w after-w) U))))))

(tu/deftest-kb ^:red interval-quartet-allen-relations-need-ws-closed-bound-marker
  ;; Every row names the 🇨 answer — the one before-w's closed bound or strictly-after-w's
  ;; open bound would settle — which today's vocabulary cannot state (interval-quartet!'s
  ;; docstring says why). Confirmed red today, like the control above, and for the same
  ;; prior reason first: `:allen`/`:point` do not yet turn a stored endpoint pair into an
  ;; Allen relation for a non-calendar individual at all, so every row is unknown before
  ;; the closed/open-marker question is even reached.
  (v/add-reasoner kb :allen :point :calendar :includes-instant)
  (tu/with-terms [DatedEndingAtW DatedStartingAtW]
    (let [w (at 6)
          {:keys [strictly-before-w before-w after-w strictly-after-w
                  dated-ending-at-w dated-starting-at-w] :as terms}
          (quartet-at w DatedEndingAtW DatedStartingAtW)]
      (interval-quartet! kb terms)
      (run-allen-table!
       kb U
       [["before-w meets strictly-after-w: the two halves still partition the line at w"
         (list 'meets before-w strictly-after-w) :true
         "needs before-w's closed marker and strictly-after-w's open marker; today neither has a stated bound for :allen to place"]

        ["before-w does not meet after-w: they overlap at exactly the instant w"
         (list 'meets before-w after-w) :false
         "before-w's bound is membership-only; :allen has no endOf to refute meets with"]

        ["before-w is not temporally disjoint from after-w: their shared time is exactly w"
         (list 'temporallyDisjoint before-w after-w) :false
         "same dependency as the row above, at the derived predicate"]

        ["adding Strict to the after side empties the intersection: before-w and strictly-after-w share no time"
         (list 'temporallyDisjoint before-w strictly-after-w) :true
         "needs both markers; neither bound is stated today"]

        ["adding Strict to the before side empties the intersection: strictly-before-w and after-w share no time"
         (list 'temporallyDisjoint strictly-before-w after-w) :true
         "strictly-before-w and after-w have only ordinary bounds stated, so this is the same 🇦-vocabulary question as the control test's meets, asked of the derived predicate instead — not folded into the control because meets and temporallyDisjoint are different relations"]

        ["adding Strict to both sides empties the intersection: a gap of exactly w"
         (list 'temporallyDisjoint strictly-before-w strictly-after-w) :true
         "strictly-before-w's bound is ordinary and stated; strictly-after-w's open-start bound is not statable without the marker"]

        ["w does not belong to strictly-after-w, even though its coordinate is w"
         (list 'includesInstant strictly-after-w w) :false
         "nothing today states w is excluded; strictly-after-w's open-start marker is what would let includesInstant answer false instead of unknown"]

        ["a dated interval ending at w nests properly inside before-w (during-style)"
         (list 'during dated-ending-at-w before-w) :true
         "before-w's end is membership-only; during needs a comparable endOf to place against"]

        ["strictly-before-w is a proper subinterval of before-w, though they share no stated start (both unbounded below)"
         (list 'properSubintervalOf strictly-before-w before-w) :true
         "before-w's end is membership-only, so the during comparison inside properSubintervalOf has nothing to place against; neither side states a start at all"]

        ["a dated interval starting at w starts after-w: they share the ordinary stated start at w"
         (list 'starts dated-starting-at-w after-w) :true
         "needs after-w declared as having no end, not merely no endOf fact stated; :allen cannot entail a-end < b-end against a wholly unconstrained b-end"]

        ["a dated interval starting at w does not start strictly-after-w, though its start shares the coordinate w"
         (list 'starts dated-starting-at-w strictly-after-w) :false
         "needs strictly-after-w's open-start marker to see w is excluded, not merely unknown"]]))))

;; ---- open-ended stretches: a status still current, and the same status capped ---
;;
;; prStatus's own prose for a status still current reads "Draft from Oct 1 until Now" and
;; "Open from Oct 3 until Now": a stretch with a stated start and no stated end at all,
;; exactly what `transition!` above writes for whichever status is current — no
;; `IntervalBeforeFn`, no watermark, no closed/open bound marker, just an ordinary
;; `startOf` with nothing said about where the stretch ends.  Once a later transition
;; caps it, the same stretch reads "Draft from Oct 1 until Oct 3": the ordinary half-open
;; `[Oct 1, Oct 3)` the rest of this namespace already uses.
;;
;; Every row below is red for the prior reason `interval-quartet!`'s comment documents,
;; not the closed/open-bound question that comment goes on to: `:allen`/`:point`,
;; registered, do not turn a stored `startOf`/`endOf` pair into a derivable Allen relation
;; for a non-calendar individual at all, so a relation between two named stretches
;; answers `:unknown` today whatever it asks — including every row here, where both ends
;; in question (the open stretches' missing end, the capped stretches' ordinary stated
;; one) are each exactly the half-open shape the quartet's `strictly-before-w`/`after-w`
;; members already use without needing any marker at all.
(defn- open-ended-stretches!
  "Stands up `draft-open` and `open-open` in `kb`, each with only a stated `startOf` and no
  `endOf` — the \"until Now\" shape for whichever status is current — `draft-capped`, the
  same Draft narrowed to end where Open began, and `wider`, an ordinary dated interval
  from 30 September to 4 October to compare `draft-capped` against for containment."
  [kb {:keys [draft-open open-open draft-capped wider]}]
  (doseq [i [draft-open open-open draft-capped wider]]
    (v/assert kb (list 'time_interval i) U))
  (v/assert kb (list 'startOf draft-open (at 1)) U)
  (v/assert kb (list 'startOf open-open (at 3)) U)
  (v/assert kb (list 'startOf draft-capped (at 1)) U)
  (v/assert kb (list 'endOf draft-capped (at 3)) U)
  (v/assert kb (list 'startOf wider (list 'InstantFn 2026 9 30 0 0 0)) U)
  (v/assert kb (list 'endOf wider (at 4)) U))

(tu/deftest-kb ^:red open-ended-stretches-overlap-until-a-later-transition-caps-them
  ;; See the comment above open-ended-stretches! for the one reason every row here is red.
  (v/add-reasoner kb :allen :point :calendar :includes-instant)
  (tu/with-terms [DraftOpen OpenOpen DraftCapped Wider]
    (open-ended-stretches! kb {:draft-open DraftOpen :open-open OpenOpen
                               :draft-capped DraftCapped :wider Wider})
    (run-allen-table!
     kb U
     [["uncapped Draft and uncapped Open overlap: neither stretch has a stated end, so they are not temporally disjoint"
       (list 'temporallyDisjoint DraftOpen OpenOpen) :false]

      ["capped Draft meets Open: Draft's stated end is exactly Open's stated start"
       (list 'meets DraftCapped OpenOpen) :true]

      ["capped Draft and Open are temporally disjoint: meets is one of the relations the complement counts"
       (list 'temporallyDisjoint DraftCapped OpenOpen) :true]

      ["capped Draft sits properly inside the wider 30 September-4 October stretch"
       (list 'during DraftCapped Wider) :true]])))

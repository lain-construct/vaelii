;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.budget
  "Resource-bounded / anytime realization of an answer stream.

  The engine's query paths are **lazy** — `ask`, `query`, and the level stack
  all yield one solution at a time, paying per result consumed.  Resource-bounding
  is therefore the *consumer-side* discipline of realizing that stream under a
  bound and reporting whether it ran dry or was cut short — and resumption falls
  out of laziness for free, because the unrealized tail **is** the continuation.

  A **budget** is a map of optional bounds (any subset; nil / {} means unbounded):

    :max-ms       wall-clock milliseconds — a soft deadline, checked *between*
                  yielded results (a single blocking pull is not interrupted, so
                  the granularity is one solution — the honest limit, matching a
                  closure that has no partial answer)
    :max-results  stop after this many solutions
    :max-cost     a qualitative prover-cost ceiling — a tier keyword (see
                  `vaelii.impl.provers/cost-tiers`).  Honored by `ask-within`,
                  which drops provers above the tier before the stream is built;
                  ignored *here*, since it selects *which* work runs, not how much
                  of a stream to realize.
    :max-depth    transformation (rule-expansion) depth — honored by `prove-within`
    :max-term-growth
                  how many levels of compound nesting a subgoal may add over what its
                  own derivation path has already met (`res/default-max-term-growth`,
                  8) — the DFS prover's other termination guard, honored by
                  `prove-within` through `prove-bounds`

  A key outside those five is refused (`:unknown-option`, `check-budget!`): every
  bound is optional, so a misspelt one is not missing — the run is simply unbounded,
  in silence.

  A **partial result** — the anytime contract returned by `collect` / `from-batch`
  / `resume`:

    :results      the solutions realized in *this* step (a vector)
    :status       :complete  the source ran dry — the answer is exhaustive
                  :timeout   :max-ms elapsed with work remaining
                  :capped    :max-results reached with work remaining
    :count        (count :results)
    :elapsed-ms   wall-clock spent in this step
    :resume       nil when :complete; otherwise a 1-arg fn (budget -> partial
                  result) that continues exactly where this step stopped

  `:results` are per-step, **not cumulative**: concatenate across steps for the
  whole answer.  The resume continuation captures an in-memory lazy tail (or, for
  `prove-within`, the DFS goal stack), so resumption is **in-process only** — it
  does not survive a restart, and holding one pins its captured state in the heap
  (see the single-writer contract in docs/storage.md)."
  (:require [vaelii.impl.opts :as opts]))

(def ask-budget-keys
  "Every bound `ask-within` reads: the wall clock, the result cap, and the qualitative
  prover-cost ceiling.  **Not `:max-depth` / `:max-term-growth`**, which bound rule
  expansion `ask` does not do — the same split `vaelii.core/ask-opt-keys` makes for `ask`."
  #{:max-ms :max-results :max-cost})

(def prove-budget-keys
  "Every bound `prove-within` reads: the wall clock, the result cap, and the two guards on
  rule expansion.  **Not `:max-cost`**, an `ask` concept `prove` ignores — the same split
  `vaelii.core/prove-opt-keys` makes for `prove`."
  #{:max-ms :max-results :max-depth :max-term-growth})

(def budget-keys
  "Every bound a budget may carry — the **union** of what `ask-within` and `prove-within`
  each read.  `resume` continues either, so it holds a partial to this union rather than to
  one entry point's half; `check-budget!` defaults to it, and the two entry points pass
  their own narrower roster instead.  Public for the reason `vaelii.core/assert-opt-keys`
  is: it is the answer to \"is this a real bound?\"."
  (into ask-budget-keys prove-budget-keys))

(defn check-budget!
  "Refuse a budget key nothing reads, a value outside a bound's domain, and a non-nil
  non-map budget (`:unknown-option` all three).  A budget is a map of *optional* bounds,
  so a misspelt key is not missing — the run is simply unbounded: `{:max-mss 100}`
  realizes the whole stream, which on an infinite source never returns, and is in any case
  the opposite of what was asked.  And a bound holding a value it cannot mean — a string
  `:max-ms`, a zero `:max-results` — reaches arithmetic and throws bare, where every
  sibling refusal is typed; `check-values!` catches it here (`opts/bound-domains`).
  (A `:max-cost` value outside the tiers is checked separately, `:unknown-option` at
  `vaelii.impl.provers/cost-capped-provers`, which `ask-capped` reads the registry
  through — it is not a numeric bound, so it has no row in `bound-domains`.)

  `opt-keys` defaults to the union `budget-keys` — what `resume`, `collect` and the two
  drivers hold a budget to, since a `resume` continues either entry point.  `ask-within`
  and `prove-within` pass their own narrower roster and subject, so a caller who names
  `:max-depth` at `ask-within` is told it is not a bound `ask` reads."
  ([budget] (check-budget! budget budget-keys "budget"))
  ([budget opt-keys subject]
   (opts/check! budget opt-keys subject
                "A bound nothing reads is an unbounded run in silence.")
   (opts/check-values! budget subject)
   budget))

(defn deadline
  "Absolute `System/nanoTime` instant `:max-ms` from now, or nil when unbounded."
  [budget]
  (when-let [ms (:max-ms budget)]
    (+ (System/nanoTime) (long (* ms 1e6)))))

(defn prove-bounds
  "A budget as the DFS prover's `bounds` map (`res/prove-from`) — the deadline the
  wall-clock bound resolves to, plus the caps it reads under their own names.

  One translation, and it lives beside `budget-keys` on purpose: the roster and the
  map that honours it are two halves of one claim, and a bound rostered there but not
  built here is accepted and then ignored — precisely what `check-budget!` refuses a
  misspelt key to prevent.  `:max-cost` is absent because it is an `ask` concept
  (`prove` runs facts and rules, and no prover registry), and the node-engine arm of
  `prove-within` takes the budget itself rather than this map.

  A bound the caller did not name reads nil, which `prove-from` takes as unbounded —
  except `:max-term-growth`, whose absence is `res/default-max-term-growth` rather than
  no ceiling, since it is a termination guard and not a budget the caller may drop."
  [budget]
  {:deadline        (deadline budget)
   :max-results     (:max-results budget)
   :max-depth       (:max-depth budget)
   :max-term-growth (:max-term-growth budget)})

(defn ms-since
  "Milliseconds elapsed since a `System/nanoTime` instant, as a double."
  [start-nanos]
  (/ (double (- (System/nanoTime) start-nanos)) 1e6))

(defn from-batch
  "Assemble the partial-result contract from a completed step.  `resume-fn` is a
  1-arg (budget -> partial result) continuation; it is dropped when `status` is
  `:complete` (nothing remains to continue).  Both engines — the lazy `collect`
  and the eager `prove-within` — build their answer through here, so the two
  return the identical shape."
  [results status start-nanos resume-fn]
  {:results    results
   :status     status
   :count      (count results)
   :elapsed-ms (ms-since start-nanos)
   :resume     (when (not= status :complete) resume-fn)})

(defn collect
  "Realize the lazy seq `xs` under `budget`, returning the partial-result contract.

  Both bounds are checked *before* pulling the next element, so `:max-results` n pulls
  the source n times and a passed deadline stops without over-reading; the element
  under the cursor is never lost — it stays the head of the captured tail, so
  `resume` re-pulls it.  A `nil` / `{}` budget realizes the whole seq (`:complete`).

  `rest`, not `next`: `next` realizes one element *ahead* to decide whether a tail
  exists, so a cap of n would pull n+1 from the source.  `rest` defers that, and the
  cap check sits above the `empty?` that would force it — so an unbounded source is
  bounded without reading past the cap.

  **How many elements that realizes is the source's business, not this loop's.**  n pulls
  realize exactly n elements of an **unchunked** seq, which is what every seq the engine
  hands here is — a `lazy-seq`/`cons` chain out of the solvers and the index, pinned by
  `laziness_test/a-capped-ask-pays-for-the-cap-and-not-for-a-chunk`.  A *chunked* source —
  anything built by `map`/`filter` over a vector or a range — realizes its whole 32-element
  chunk on the first pull whatever the cap says, and no cap check above it can prevent
  that.  So the promise a caller may rely on is the one about the source: n pulls, and
  the tail resumable from where they stopped."
  [xs budget]
  (check-budget! budget)
  (let [max-results (:max-results budget)
        dl          (deadline budget)
        start       (System/nanoTime)]
    (loop [xs xs, n 0, acc (transient [])]
      (cond
        (and max-results (>= n max-results))
        (from-batch (persistent! acc) :capped start (fn [b] (collect xs b)))

        (and dl (>= (System/nanoTime) dl))
        (from-batch (persistent! acc) :timeout start (fn [b] (collect xs b)))

        (empty? xs)
        (from-batch (persistent! acc) :complete start nil)

        :else
        (recur (rest xs) (inc n) (conj! acc (first xs)))))))

(defn resume
  "Continue a `:timeout` / `:capped` partial result under a fresh `budget`.  A
  `:complete` result has no continuation, so `resume` returns it unchanged —
  making a `while (:resume …) (recur (resume …))` loop terminate cleanly."
  [partial budget]
  (if-let [f (:resume partial)]
    (f budget)
    partial))

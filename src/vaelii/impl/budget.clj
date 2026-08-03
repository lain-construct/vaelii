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
  (see the single-writer contract in docs/storage.md).")

(defn deadline
  "Absolute `System/nanoTime` instant `:max-ms` from now, or nil when unbounded."
  [budget]
  (when-let [ms (:max-ms budget)]
    (+ (System/nanoTime) (long (* ms 1e6)))))

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

  Both bounds are checked *before* pulling the next element, so `:max-results` n
  realizes exactly n and a passed deadline stops without over-reading; the element
  under the cursor is never lost — it stays the head of the captured tail, so
  `resume` re-pulls it.  A `nil` / `{}` budget realizes the whole seq (`:complete`).

  `rest`, not `next`: `next` realizes one element *ahead* to decide whether a tail
  exists, so a cap of n would pull n+1 from the source.  `rest` defers that, and the
  cap check sits above the `empty?` that would force it — so exactly n elements are
  realized (an unbounded source is bounded without reading past the cap)."
  [xs budget]
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

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.profile
  "What a KB is **asked**, and what each answer costs the index — four tallies behind
  one switch.

  The index has six families and several access paths into them (`docs/indexing.md`),
  and which of them earns its keep is a question about a *workload*, not about the code:
  a KB whose every pattern leads with a ground first argument pays for three secondary
  root families it never reads, and a KB that asks `(?type Muffet)` a thousand times a
  second lives or dies on the argument-slot roster.  Nothing in the engine answers that
  from the outside, so this is the instrument that does.

  Seven tallies, one per question:

  * **`:goals`** — every retrieval decision the matchers took, keyed by the literal's
    *shape* and by the access path that shape chose.  This is the distribution an index
    policy would have to serve.  Two matchers decide: `res/candidate-handles` (the trie
    against the roots) and `res/matches-hierarchical` (the set-algebra path).  It counts
    **retrievals rather than questions** — a matcher that fans over a predicate's spec
    closure records one entry per sub-predicate — so a total here is index traffic, not
    a count of what a caller asked.
  * **`:reads`** — every `IndexStore` read, by family.  This is the one that answers
    whether a family earns its keep: a KB that never reads the argument roots is a KB
    paying three write taxes for an access path nothing takes.  The trie counts as two
    families here, `:trie-lookup` and `:trie-counts`, because retrieval and the cost
    model read the same structure for unrelated reasons and a run can be dominated by
    either.
  * **`:fan`** — every trie walk `KvIndexStore.lookup` performed, keyed by the path's
    first token, with the node probes it cost.  A walk that narrows visits one node per
    level; a walk that fans out visits the whole child set at the level it got stuck, and
    this is where that shows up as a number rather than as an anecdote.
  * **`:sift`** — the three widths of one set-algebra retrieval: how many candidates the
    argument-root probe returned, how many reached `unify`, how many matched.  Keyed like
    `:goals`, and the read-efficiency reading a layout change is judged on.
  * **`:fetches`** — every `RecordStore` fetch, by kind.  **The other index**: a `:reads`
    figure prices what the trie and the roots were asked, and says nothing at all about
    the records those handles then name.  The two come apart exactly where it hurts — a
    probe that narrows to one index read and then fetches a record per candidate handle
    reads *well* by `:reads` and badly by this — and on the durable store a fetch is a
    positional slot read, a positional frame read and a nippy thaw past the LRU, which is
    orders above what any index read costs.  `record_fetch_cost_test` is the gate set from
    it.
  * **`:writes`** — what one `index-sentex` wrote, per family, keyed by functor.  Every
    family is a tax on every assert, so a policy that *adds* one is priced here.
  * **`:retracts`** — the same for `unindex-sentex!`, and a separate tally rather than a
    sign on the one above, because the two do not have the same shape.  An assert's cost
    is a constant per family; a retraction's is not, since a trie node is deleted only
    when the last sentex under it goes and how often that happens is a property of how
    much prefix the corpus shares.  `:dead` is that number — trie nodes this retraction
    emptied — and it is the one quantity here a corpus can move without changing what it
    holds.  Merged into `:writes`, the per-assert constant a gate is set from would stop
    being readable.

  ## The shape key

  A goal's key is `[functor truth adornment path]`, where the adornment is one character
  per argument, in position order:

      b  a ground atom the roots key      (a symbol: an individual, a type, a context)
      B  a ground compound                (keyed whole by the argument roots)
      n  a ground token the roots do NOT key   (a number, a string)
      f  an open atom                     (a variable)
      F  an open compound                 (a compound holding a variable)

  So `(parentOf ?x Tom)` is `[parentOf :true \"fb\" :arg-roots]` and
  `(mass ?o (QuantityFn ?n Kilogram))` is `[mass :true \"fF\" :structural]`.  `functor` is
  `:open` when the functor is itself a variable, which is the shape that puts every
  argument behind it.  Arity is the adornment's length, so the key carries it too.

  The alphabet is what the *index* distinguishes rather than what a reader would: `b` and
  `B` are one family's keys and `n` is no key at all, which is why a ground number after a
  variable keeps the trie while a ground symbol there does not.

  ## Off by default, and free when off

  The switch and the store are one atom: nil when off, so every seam is a deref and a
  `nil?` check, which is what the observer seam costs the reference chainer
  (`vaelii.impl.observe`).  Anything heavier on a retrieval path would show up in `lein
  perf` as a constant, and a ratio cannot see a constant.

  On, it is one `swap!` per event over a persistent map.  That is not free and is not
  meant to be: a profiling run measures *shape*, and every quantity here is a count, so a
  run under the instrument answers the same as a run without it, more slowly.

  ## What it does not see

  * **`:fan` is the one tally that is not index-independent.**  It is `KvIndexStore`'s,
    which covers every backend the `KvBackend` adapters reach — the flat map, the dense
    one, the on-disk WAL, an overlay.  `vaelii.impl.columnar` walks its own native trie
    and counts no node probes, so a columnar run reports **no fan at all** rather than a
    fabricated one, and `profile_test` pins that silence.  Every other tally holds on
    both: that store keeps the goal, read, write and retract tallies itself, because it
    writes and walks the index rather than going through `KvIndexStore` to do it.
  * A retrieval that reaches the index without going through either matcher has no
    shape here: the direct `p/lookup` callers (`find-sentex-handle`, the level-0 raw
    read) appear in `:fan` and `:reads` and not in `:goals`.
  * **`:fetches` counts the protocol call, not the work behind it.**  A store's own
    internal reads are its own business — the durable store re-reads a record inside
    `mark-premise` where the RAM one reaches into its state map — so counting those would
    make the tally a reading of which backend is running.  What is counted is
    `p/get-sentex` / `p/get-justification` / `p/get-provenance`, which is the number a
    caller controls: an overlay fetch that consults the base and then the fork counts
    twice, which is what a fork costs.  A fetch answering **nil** counts, because the
    caller paid for it.

  ## Reading it

  `snapshot` is plain data and `stop` returns the last one.  Nothing here formats: what a
  reading *means* is the caller's business, and `vaelii.bench.profile` is the caller that
  has an opinion."
  (:require [vaelii.impl.sentex :as sx]))

;; nil when off; otherwise `{:t0 <nanos> :goals {} :reads {} :fan {} :sift {} :fetches {}
;; :writes {} :retracts {}}`.  One atom rather than a flag beside a store, so a seam
;; cannot read the flag on and the store as nil.
(defonce ^:private tally (atom nil))

(defn profiling?
  "Is the instrument collecting?"
  []
  (some? @tally))

(defn start
  "Begin collecting, dropping whatever a previous run left.  Bare, not `!`: a tally is
  derived from a workload nobody stored, so nothing it holds is knowledge and re-running
  the workload recomputes it."
  []
  (reset! tally {:t0 (System/nanoTime) :goals {} :reads {} :fan {} :sift {} :fetches {}
                 :writes {} :retracts {}})
  nil)

(defn- read-out [t]
  (when t
    (-> (dissoc t :t0)
        (assoc :elapsed-ms (/ (- (System/nanoTime) (long (:t0 t))) 1e6)))))

(defn snapshot
  "The tallies so far as plain data, or nil when the instrument is off:

      {:elapsed-ms  how long this run has been collecting
       :goals   {[functor truth adornment path] count}
       :reads   {family count}
       :fan     {first-token {:calls :visits :widest :handles :decades {n count}}}
       :sift    {[functor truth adornment path] {:calls :returned :unified :matched}}
       :fetches {kind count}
       :writes  {functor {:asserts :levels :terms :roots :roster :slots}}
       :retracts {functor {:retracts :levels :terms :roots :roster :slots :dead}}}"
  []
  (read-out @tally))

(defn stop
  "Stop collecting and return the final snapshot (nil when it was not running)."
  []
  (let [t @tally]
    (reset! tally nil)
    (read-out t)))

;; ---- the goal tally -----------------------------------------------------

(defn- arg-class
  "One character for one argument position — see the alphabet in the namespace docstring."
  [a]
  (if (sequential? a)
    (if (sx/ground-term? a) \B \F)
    (cond
      (sx/variable? a)       \f
      (sx/indexable-term? a) \b
      :else                  \n)))

(defn shape-of
  "One literal's tally key, `[functor truth adornment path]`.  Public because the oracle
  asks for a shape directly rather than inferring it from a count."
  [body truth path]
  (if (or (not (sequential? body)) (empty? body))
    [:none truth "" path]
    (let [f (first body)]
      [(if (and (symbol? f) (sx/variable? f)) :open f)
       truth
       (apply str (map arg-class (rest body)))
       path])))

(defn record-goal
  "Tally one `candidate-handles` decision: the pattern sentex it was asked for and the
  access path it chose.  A deref and a `nil?` check when the instrument is off."
  [pat path]
  (when @tally
    (swap! tally update-in [:goals (shape-of (sx/body pat) (:truth pat) path)] (fnil inc 0))))

(defn record-literal
  "Tally one retrieval decision taken over a bare sentence rather than a pattern sentex —
  the set-algebra matcher's, which is handed the literal and admits only positive ones."
  [sentence path]
  (when @tally
    (swap! tally update-in [:goals (shape-of sentence :true path)] (fnil inc 0))))

;; ---- the read tally -----------------------------------------------------

(defn record-read
  "Tally one `IndexStore` read against the family that answered it.  This is the tally
  that says whether a family earns its keep, so the names are the families and not the
  method names: several methods read the argument roots, and what a policy would drop is
  the family."
  [family]
  (when @tally
    (swap! tally update-in [:reads family] (fnil inc 0))))

;; ---- the record-fetch tally ---------------------------------------------

(defn record-fetch
  "Tally one `RecordStore` fetch against the kind that answered it — `:sentex`,
  `:justification` or `:provenance`.  The record-store twin of `record-read`, and it
  exists because the two quantities move independently: `find-sentex-handle` narrowed
  from a wildcard `lookup` to the exact `leaf-at` moved **no** `:reads` figure and took
  a fetch per candidate handle off the dedup path (2,779 µs against 13 µs per call at
  800 candidates).  A read tally could not see that and nothing else counted it.

  Keyed by kind rather than by handle or by functor: what a policy would change is
  whether a *kind* is paged at all — the record for a candidate, the justification for
  a support walk, the provenance nothing but the browser reads — and a per-handle key
  would hold the whole workload.

  A deref and a `nil?` check when the instrument is off, like every seam here."
  [kind]
  (when @tally
    (swap! tally update-in [:fetches kind] (fnil inc 0))))

;; ---- the sift tally -----------------------------------------------------

(defn- bump-sift [row ^long returned ^long matched ^long unified]
  (-> row
      (update :calls    (fnil inc 0))
      (update :returned (fnil + 0) returned)
      (update :matched  (fnil + 0) matched)
      (update :unified  (fnil + 0) unified)))

(defn record-sift
  "Tally one hierarchical retrieval's three widths: how many candidate handles the
  argument-root probe (`lead-candidates`) handed the matcher (`returned`), how many of
  those reached `unify` after the cheap liveness/predicate/context filters (`unified` —
  the **unify-attempt** count), and how many survived to become actual matches
  (`matched`).  Keyed by the literal's shape and the retrieval path, like `:goals`.

  `returned` is the read-efficiency number an index-layout change is judged on: a probe
  that returns a wide superset the filter then discards is doing work a tighter key would
  not.  `unified` is what **multi-column narrowing** moves directly — intersecting the
  ground columns at the probe hands `unify` a smaller set, so a wide column the second
  bound argument would have rejected never reaches it.

  A deref and a `nil?` check when the instrument is off — and the call site realizes the
  full candidate seq only while collecting, so a timing run (instrument off) keeps the
  lazy short-circuit an existence check relies on.

  Unhinted args: a fn taking primitive `long`s is capped at four, and this takes five —
  the counts box, which costs nothing off the timing path (this is only reached while
  collecting)."
  [sentence path returned matched unified]
  (when @tally
    (swap! tally update-in [:sift (shape-of sentence :true path)]
           bump-sift (long returned) (long matched) (long unified))))

;; ---- the fan tally ------------------------------------------------------

(defn- decade
  "The power of ten `n` sits at — 1, 10, 100 — so a fan histogram has a bounded number of
  buckets whatever the corpus size."
  ^long [^long n]
  (if (< n 1)
    0
    (loop [d 1] (if (< n (* 10 d)) d (recur (* 10 d))))))

(defn- bump-fan [row ^long visits ^long widest ^long handles]
  (let [{:keys [calls] :or {calls 0}} row]
    (-> row
        (assoc :calls (inc (long calls)))
        (update :visits (fnil + 0) visits)
        (update :widest (fnil max 0) widest)
        (update :handles (fnil + 0) handles)
        (update-in [:decades (decade visits)] (fnil inc 0)))))

(defn record-fan
  "Tally one trie walk: `visits` node probes, a frontier that reached `widest`, and
  `handles` handles at the terminus.  Keyed by the path's first token, which is the
  functor for a positive fact and `:false` for a negative."
  [pattern ^long visits ^long widest ^long handles]
  (when @tally
    (swap! tally update-in [:fan (first pattern)] bump-fan visits widest handles)))

;; ---- the write tally ----------------------------------------------------

(defn- write-key [sentex]
  (if (some? (:antecedent sentex))
    :rule
    (let [b (sx/body sentex)]
      (if (and (sequential? b) (seq b) (symbol? (first b))) (first b) :other))))

(defn- bump-write [row {:keys [levels terms roots roster slots]}]
  (-> row
      (update :asserts (fnil inc 0))
      (update :levels  (fnil + 0) (long levels))
      (update :terms   (fnil + 0) (long terms))
      (update :roots   (fnil + 0) (long roots))
      (update :roster  (fnil + 0) (long roster))
      (update :slots   (fnil + 0) (long slots))))

(defn record-index-write
  "Tally one `index-sentex`: how many trie levels it touched and how many keys each of
  the flat families took.  Call sites guard on `profiling?` so the counts map is built
  only while collecting."
  [sentex counts]
  (when @tally
    (swap! tally update-in [:writes (write-key sentex)] bump-write counts)))

(defn- bump-retract [row {:keys [levels terms roots roster slots dead]}]
  (-> row
      (update :retracts (fnil inc 0))
      (update :levels   (fnil + 0) (long levels))
      (update :terms    (fnil + 0) (long terms))
      (update :roots    (fnil + 0) (long roots))
      (update :roster   (fnil + 0) (long roster))
      (update :slots    (fnil + 0) (long slots))
      (update :dead     (fnil + 0) (long dead))))

(defn record-index-retract
  "Tally one `unindex-sentex!`, the same families as `record-index-write` plus `:dead`,
  the trie nodes this retraction emptied and deleted.

  `:dead` is why this is a tally of its own.  Every other quantity here is decided by
  the sentex — its arity, its terms, its indexable arguments — so it reads the same
  whenever the retraction happens.  How many nodes die is decided by what *else* is
  still stored under the same prefix, so the same sentex retracted from a dense corpus
  and from a sparse one costs differently, and a family's retraction cost cannot be
  quoted as a constant the way its assert cost can."
  [sentex counts]
  (when @tally
    (swap! tally update-in [:retracts (write-key sentex)] bump-retract counts)))

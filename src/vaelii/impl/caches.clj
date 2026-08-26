;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.caches
  "What this process is holding beside the stores — one register every derived,
  droppable structure declares itself in, and one read over the lot.

  The stores are measured elsewhere: `catalog/heap` reports the JVM's own figure and
  `catalog/footprint` estimates what a loaded KB costs.  Neither says anything about the
  **caches** — the atoms and plain maps holding answers the engine would otherwise
  recompute — and a hit rate is the only evidence a cost model has.  \"The
  second query was fast\" is a demo; \"the second query was fast because it was served
  from a cache, and here is the rate\" is a measurement.

  **A register rather than a dozen accessors.**  This namespace requires nothing, which
  is the whole design: every namespace holding a cache requires *this* one and declares
  itself at load, so there is no require edge from the reader down to the caches and no
  list here that a new cache has to be added to twice.  A cache in a namespace this
  process never loaded — a qualitative calculus nobody registered, the metric-time
  reasoner — is absent from the read because it is absent from the process, which is the
  honest answer rather than a row of zeroes.

  **Two scopes, and never one wearing the other's clothes.**  `:scope` says what a row's
  `:entries` counts: `:kb` for a cache hanging off a KB record, `:process` for a static
  one every KB in the JVM shares.  `:counters` says the same about `:hits` / `:misses`,
  separately, because the literal cache is exactly the awkward case — its entries are
  per-KB and its counters are global `AtomicLong`s, \"since they measure the mechanism
  rather than a store\" (`literal-cache/stats`).  Rendering that as one per-KB row would
  attribute another KB's hits to this one.  The closure neighbours are awkward the other
  way round — process counters over entries only a live search step can count — which is
  the same argument for keeping the two fields apart.

  **`:unit` is not decoration.**  One cache counts literals, another counts networks, a
  third counts symbols, and a column of bare integers compares none of them.

  A row whose `:entries` is nil is one that cannot be counted from outside — the
  scope-bound caches, bound for the length of one chaining run or one search step and
  garbage when it returns.  They are registered all the same, with the reason in
  `:note`, so the list is complete rather than merely finite.

  **A row answers for itself, and fails for itself.**  The register is open, so a read
  here runs code this namespace has never seen; one that throws is reported as a row
  carrying `:error` rather than allowed to take the answer down with it.  A diagnostic
  is worth most while something is already wrong, which is exactly when it must not be
  the next thing to break.")

;; ---- the bound every registered cache takes ------------------------------

(defn assoc-bounded
  "Store `v` at `k` in map `m`, **clearing `m` wholesale** when it already holds `limit`
  entries.

  The bound policy, in one place rather than spelled out at each cache.  Wholesale
  clearing rather than eviction is `literal-cache/cache-limit`'s argument and
  `observe/resident-limit`'s before it: evicting exactly the right entry costs more
  bookkeeping than the entry saved, and a cache that has grown past its bound is one
  whose queries have moved on.  That is a judgement about every cache here at once, so
  it is worth being able to revisit in one edit rather than six."
  [m limit k v]
  (assoc (if (>= (count m) limit) {} m) k v))

(defn read-through
  "The value at `k` in the map held by atom `cache`, else `(compute)` — stored under
  `assoc-bounded`'s bound, and returned.

  `find` rather than `get`, so a computed `nil` is a hit rather than a miss recomputed
  forever.  `compute` runs outside the `swap!` because it is the expensive half and a
  `swap!` retry must not run it twice: two callers racing one key both compute and both
  store, and the second store is a no-op — the trade a memo of derived values wants over
  holding a lock across the computation."
  [cache limit k compute]
  (if-let [hit (find @cache k)]
    (val hit)
    (let [v (compute)]
      (swap! cache assoc-bounded limit k v)
      v)))

;; `{cache-id descriptor}`.  A `defonce` because registration happens at namespace load
;; and reloading *this* namespace must not empty what the namespaces already loaded put
;; here; keyed by id, so reloading one of *them* replaces its own entry rather than
;; doubling it.
(defonce ^:private registry (atom {}))

(defn register-cache
  "Declare that this namespace holds a cache.  Called at namespace load, once per cache.
  Bare, not `!`: it installs a descriptor the next load replaces, the way `set-solver`
  installs a setting.

  The descriptor:

    :cache     a keyword naming it, unique across the process
    :label     what to call it on screen
    :scope     :kb or :process — what `:entries` counts
    :unit      what one entry *is*, since entries mix units across caches
    :limit     entries held before it is cleared wholesale, or nil for a cache
               bounded by something other than a count (say what, in `:note`).
               **A thunk where the bound is a dynamic var** — see below
    :counters  :kb, :process, or nil when nothing counts hits and misses
    :note      one line: what it holds, and what retires an entry
    :read      (fn [kb]) -> {:entries n :hits h :misses m}, any key absent where
               there is no number.  **O(1)** — this runs on a page that polls.
               A nil `:entries` says the cache cannot be counted from here.
    :clear     (fn [kb]) -> entries dropped, or absent when nothing drops it by hand.
               **Scoped to `kb`.**  A clear that reached past its argument would make
               `clear-caches` a process-wide control wearing a per-KB signature
    :reset-counters (fn [kb]) -> the counters as they stood, or absent.  Only a cache
               whose `:counters` are `:process` has one, and it is separate from `:clear`
               precisely because it is wider than `kb`

  `:read`, `:clear` and `:reset-counters` all take the KB even when the cache is
  process-wide, so a caller needs no second calling convention for the static ones; they
  ignore it.

  **`:limit` takes a thunk for the same reason `:read` is a function.**  A descriptor is
  built once, at namespace load, so a constant captured into it is that constant forever
  — which is right for a `def` and wrong for a `^:dynamic` var, since being rebindable is
  the only reason such a var is dynamic.  Reporting the root bound while the engine
  enforces a bound somebody rebound would misreport the one field a reader uses to judge
  whether a cache is about to flush.  Write `:limit (fn [] *the-var*)` and the row reads
  it where it is read."
  [{:keys [cache] :as descriptor}]
  (swap! registry assoc cache descriptor)
  cache)

(defn- hit-rate
  "Hits over lookups, or nil when nothing has been counted.  Nil rather than zero for an
  untouched cache: a rate of 0.0 reads as a cache that is missing everything."
  [hits misses]
  (when (and hits misses)
    (let [total (+ (long hits) (long misses))]
      (when (pos? total) (/ (double hits) (double total))))))

(defn- bound
  "A descriptor's `:limit`, called where it is a thunk over a dynamic var."
  [limit]
  (if (fn? limit) (limit) limit))

(defn- failed
  "What a row says when its own read threw.  A cache that cannot answer is reported as
  one that cannot answer, and never as a cache that is empty: this register is open —
  any namespace may put a descriptor in it — and a page whose worth is highest while
  something is already wrong must not be the thing that fails."
  [^Throwable t]
  (let [m (.getMessage t)]
    (str (.getSimpleName (class t)) (when (seq m) (str ": " m)))))

(defn rows
  "Every registered cache, read against `kb`, ranked by entries.

  A row is the descriptor's static half — `:cache :label :scope :unit :limit :counters
  :note` — plus whatever its `:read` answered, plus `:hit-rate` and `:clearable?`.  No
  row walks the KB: each is a count off a map the engine is already holding, which is
  what makes this pollable.

  **A row is data all the way down.**  The descriptor's three function slots — `:read`,
  `:clear`, `:reset-counters` — are dropped, and what a caller needs of the last two is
  the `:clearable?` flag and the `:counters` scope beside it.  This is a public read
  (`vaelii.core/caches`), served over RPC and rendered on a page, so a function left in a
  row is a value neither can carry.

  **A read that throws costs its own row and no other**, and the row carries `:error`
  saying what went wrong.  One broken descriptor taking the whole answer down would fail
  the read exactly when the process is in the state it exists to describe.

  Ranked by entries **descending, ties broken on the cache's own name**, so the order is
  a function of the content and two processes holding the same caches list them the
  same way.  A row that cannot be counted sorts last, since a nil is not a small number."
  [kb]
  (->> (vals @registry)
       (mapv (fn [{:keys [read clear] :as d}]
               (let [{:keys [entries hits misses error]}
                     (try (read kb) (catch Throwable t {:error (failed t)}))]
                 (-> (dissoc d :read :clear :reset-counters)
                     (assoc :entries    entries
                            :hits       hits
                            :misses     misses
                            :hit-rate   (hit-rate hits misses)
                            :clearable? (some? clear)
                            :limit      (try (bound (:limit d))
                                             (catch Throwable _ nil)))
                     (cond-> error (assoc :error error))))))
       (sort-by (juxt #(- (long (or (:entries %) -1))) #(name (:cache %))))
       vec))

(defn clear-caches
  "Drop every cache that offers a clear, and say what went: `{:cleared [{:cache :label
  :entries} …] :entries total}`, ranked like `rows`.

  Not `!`, and the reason is the whole point of the control: every entry is derived, the
  next read recomputes it, and no belief moves.  That makes a clear a measuring
  instrument rather than an edit — clear, ask the same question again, and watch the
  miss the second ask no longer gets to skip.

  **Scoped to `kb`, because the argument says so.**  Every `:clear` drops that cache's
  entries *for this KB* and nothing else.  The hit and miss counters some caches keep are
  process-wide — they measure the mechanism rather than a store — and zeroing one would
  reset a rate every other KB in the JVM is reporting, mid-measurement.  So it is not
  done here: `{:counters? true}` asks for it, in a call that says out loud it is reaching
  past its argument, and the answer then carries `:counters-reset` naming the caches it
  touched.  A function whose signature names one KB must not quietly be a per-process
  control; `caches`' `:counters` column is how a caller knows which rows the option is
  about.

  A cache with no `:clear` is left alone and is not in the answer.  Those are the
  structural ones — the symbol pool, the compiled relation algebras — where dropping the
  entries costs the sharing they exist for and buys no measurement.

  A clear that throws costs its own entry and no other, the way a read does: its row
  carries `:error` and an entry count of zero."
  ([kb] (clear-caches kb nil))
  ([kb {:keys [counters?]}]
   (let [cleared (->> (vals @registry)
                      (filter :clear)
                      (mapv (fn [{:keys [cache label clear]}]
                              (try {:cache cache :label label
                                    :entries (long (or (clear kb) 0))}
                                   (catch Throwable t
                                     {:cache cache :label label :entries 0
                                      :error (failed t)}))))
                      (sort-by (juxt #(- (long (:entries %))) #(name (:cache %))))
                      vec)
         reset   (when counters?
                   (->> (vals @registry)
                        (filter :reset-counters)
                        (mapv (fn [{:keys [cache label reset-counters]}]
                                (try (merge {:cache cache :label label}
                                            (reset-counters kb))
                                     (catch Throwable t
                                       {:cache cache :label label :error (failed t)}))))
                        (sort-by #(name (:cache %)))
                        vec))]
     (cond-> {:cleared cleared
              :entries (reduce + 0 (map :entries cleared))}
       counters? (assoc :counters-reset reset)))))

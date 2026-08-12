;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.memory
  "The default in-memory backends for the two storage protocols, selected at KB
  construction.  The engine above the protocols never touches a concrete store, so a
  KB built on these runs the whole engine with no external dependency; the on-disk
  backend (`vaelii.impl.disk`) is the durable alternative.

  The record store implements `RecordStore` directly over maps.  The index reuses
  `vaelii.impl.kv/KvIndexStore` — the one trie/roots/index implementation — over a
  `MemoryKvBackend`: one map keyed by the structured key vectors (equal vectors are
  equal keys), holding a `Long` at each counter key and a set at each set key.
  `kv-intersect` is a `clojure.set/intersection`; `kv-members` returns the stored set
  by reference (no serialization, no copy).

  **Durable-within-the-JVM semantics by space number.**  Two KBs constructed over the
  same `:space` number must share state, or the persistence/recovery tests (a second KB
  restarted over the same databases) would find an empty store.  A process-global
  registry keyed by space number provides that: `(memory-record-store {:space 15})` twice
  returns records backed by *one* state atom, and by one handle counter beside it.
  `clear-records!` / `clear-index!` empty a space.  (State lives only for the life of
  the JVM; the on-disk backend is what survives a process restart.)

  **Single-writer.**  Pure runs one writer (docs/storage.md, \"The single-writer
  contract\"), so a store's state is one atom mutated by `swap!`; reads deref a snapshot
  and are lock-free.  Interleaved *writers* would not be serializable."
  (:require [clojure.set :as set]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.protocols :as p]))

;; ---- per-space registries --------------------------------------------------
;; defonce so the registry survives REPL reloads and is shared across a JVM's test
;; namespaces — one shared store per space number, for the life of the JVM.

(defonce ^:private record-spaces   (atom {}))
(defonce ^:private record-counters (atom {}))
(defonce ^:private index-spaces    (atom {}))

(defn- space-atom
  "The state atom for `space` in `registry`, created once on first use so two stores
  over the same space number share one atom — space sharing, in RAM."
  [registry space init]
  (or (@registry space)
      (-> (swap! registry (fn [m] (if (m space) m (assoc m space (atom init)))))
          (get space))))

;; ---- record store --------------------------------------------------------

(def ^:private empty-record-state
  {:sentexes {} :justifications {} :provenance {} :premises #{}})

(defn- store-record
  "Write `rec` at handle `id` under `kind`, keeping `counter` — the highest handle
  issued — at or above it.  That second half is what makes the handle an identity:
  `put-sentex` and `put-justification` both honour an explicit `:id` (an import lands
  records at the handles its dump gave them), and a counter left behind one would hand
  the same number out again on the very next write, overwriting a record with no error
  and no warning.  O(1), and a no-op when the id came from `next-id`, which is already
  ahead of it.

  The counter is its **own** atom rather than a key in the state map, so allocating a
  handle is a compare-and-set on a `Long` and not on the whole store — one is minted per
  stored sentex and per justification, and forward chaining takes one per firing
  (docs/inference.md).  The disk store holds its counter the same way, so both backends
  allocate alike."
  [state counter kind id rec]
  (swap! state assoc-in [kind id] rec)
  (when (> (long id) (long @counter)) (swap! counter max (long id)))
  id)

(defrecord MemoryRecordStore [state counter]
  p/RecordStore
  (next-id [_] (long (swap! counter inc)))
  (put-sentex [this sentex]
    (let [id (or (:id sentex) (p/next-id this))]
      (store-record state counter :sentexes id (assoc sentex :id id))))
  (get-sentex [_ id] (get-in @state [:sentexes id]))
  (delete-sentex! [_ id]
    (swap! state (fn [st] (-> st
                              (update :sentexes dissoc id)
                              (update :premises disj id)
                              (update :provenance dissoc id))))
    nil)
  (put-justification [this justification]
    (let [id (or (:id justification) (p/next-id this))]
      (store-record state counter :justifications id (assoc justification :id id))))
  (get-justification [_ id] (get-in @state [:justifications id]))
  (delete-justification! [_ id]
    (swap! state (fn [st] (-> st
                              (update :justifications dissoc id)
                              (update :provenance dissoc id))))
    nil)
  (put-provenance    [_ id prov] (swap! state assoc-in [:provenance id] prov) prov)
  (get-provenance    [_ id]      (get-in @state [:provenance id]))
  (delete-provenance! [_ id]     (swap! state update :provenance dissoc id) nil)
  (sentex-ids    [_] (set (keys (:sentexes @state))))
  (justification-ids [_] (set (keys (:justifications @state))))
  (mark-premise [_ id strength]
    ;; the assumption strength lives on the sentex record itself; premises are also
    ;; tracked in a set.  Guard both on the record existing — a handle with no sentex
    ;; must not conjure a phantom map entry, nor a phantom premise (the durable store
    ;; guards the same way, and `premise-ids` must agree across the two).
    ;;
    ;; A record already carrying this strength is left alone, which is the ordinary
    ;; assert: `kb/create-sentex` writes the strength into the record it stores, so the
    ;; mark that follows asks for the strength it already has.  Re-`assoc`ing it copies
    ;; a path through a map holding every sentex in the KB, once per fact of a bulk
    ;; load, to arrive at the value already there.  The durable store pays more for the
    ;; same guard (`vaelii.impl.disk.record-store`: a second whole frame).
    (swap! state (fn [st]
                   (let [want (or strength :default)
                         sx   (get-in st [:sentexes id])]
                     (if-not sx
                       st
                       (cond-> (update st :premises (fnil conj #{}) id)
                         (not= want (:strength sx))
                         (assoc-in [:sentexes id :strength] want))))))
    nil)
  (unmark-premise! [_ id]
    (swap! state (fn [st]
                   (cond-> st
                     (get-in st [:sentexes id]) (assoc-in [:sentexes id :strength] nil)
                     :always                    (update :premises disj id))))
    nil)
  (premise-ids [_] (set (:premises @state)))
  (premise-strength [_ id] (or (:strength (get-in @state [:sentexes id])) :default))
  (clear-records! [_] (reset! state empty-record-state) (reset! counter 0) nil))

(defn memory-record-store
  "An in-memory `RecordStore`.  Only `:space` in `opts` matters: it selects the shared
  state atom **and** the shared handle counter, which have to be the same pair for two
  stores over one space or the second would re-issue handles the first had already
  written."
  [{:keys [space] :or {space 0}}]
  (->MemoryRecordStore (space-atom record-spaces space empty-record-state)
                       (space-atom record-counters space 0)))

;; ---- index KV backend ----------------------------------------------------
;; One map keyed by the structured key vectors, holding a Long at each counter key
;; and a set at each set key.  `KvIndexStore` (vaelii.impl.kv) supplies all the trie
;; and index logic; this only says how a scalar, a counter, and a set live in a map.

(def ^:dynamic *bulk-txn*
  "During a bulk load, a `volatile!` holding a **transient** of one MemoryKvBackend's
  state map.  While bound, this backend's *writes* land on that transient (`assoc!` —
  no per-op HAMT path copy) and the whole load is one `persistent!` at the end, instead
  of a `swap!` per fact.  nil (the default) leaves every op on the persistent atom
  exactly as before, so nothing outside a bulk load pays for it — and *reads* are left
  untouched in both modes (they read the backing atom), so the query hot path is
  unchanged.  The backing atom is therefore stale for the life of the load: correct only
  because the sole mid-load reader (`note-opposed`'s `[:false b]` probe) reads the always
  -empty negative side, and every real read happens after the closing `persistent!`.  Use
  `with-bulk-writes` for a positive/monotonic, distinct load; a corpus with `(not …)`
  facts must `rebuild-opposed!` after it (the atom the opposed set is derived from was
  stale during the load)."
  nil)

(defn- mem-op
  "Apply one `kv-batch` write op to map `m`, returning `[m' reply]`.  Only :increment/:decrement
  carry a meaningful reply (the post-op counter value); the rest reply nil.  :remove-from-set
  drops the key when the set empties, so an absent key and an empty set are
  indistinguishable — a set with no members does not exist."
  [m [op k a]]
  (case op
    :put  [(assoc m k a) nil]
    :delete  [(dissoc m k) nil]
    :increment (let [v (inc (long (get m k 0)))] [(assoc m k v) v])
    :decrement (let [v (dec (long (get m k 0)))] [(assoc m k v) v])
    :add-to-set [(update m k (fnil conj #{}) a) nil]
    :remove-from-set (let [s (disj (get m k) a)]
                       [(if (empty? s) (dissoc m k) (assoc m k s)) nil])))

(defn- mem-op!
  "The transient twin of `mem-op`: apply one write op to transient map `t`, returning
  the new transient (a transient op's return must be captured).  No reply is computed —
  the only bulk caller (`index-sentex`) ignores them.  The set *values* stay persistent
  (small, cheap `conj`/`disj`); it is the millions-of-keys map that is transient."
  [t [op k a]]
  (case op
    :put  (assoc! t k a)
    :delete  (dissoc! t k)
    :increment (assoc! t k (inc (long (get t k 0))))
    :decrement (assoc! t k (dec (long (get t k 0))))
    :add-to-set (assoc! t k (conj (get t k #{}) a))
    :remove-from-set (let [s (disj (get t k #{}) a)]
                       (if (empty? s) (dissoc! t k) (assoc! t k s)))))

;; Writes consult `*bulk-txn*`: bound (a bulk load), they land on the transient; nil
;; (everything else), the persistent atom, byte-for-byte the unbatched path.  Reads are
;; NOT bulk-aware — they read the atom in both modes, so the query hot path is untouched;
;; the atom is stale only for the life of a bulk load, and `with-bulk-writes` documents
;; why that is sound (positive load; every real read is post-load).
(defrecord MemoryKvBackend [state]
  kv/KvBackend
  (kv-get  [_ k]   (get @state k))
  (kv-put  [_ k v] (if-let [tv *bulk-txn*] (vswap! tv assoc! k v) (swap! state assoc k v)) nil)
  (kv-delete  [_ k]   (if-let [tv *bulk-txn*] (vswap! tv dissoc! k) (swap! state dissoc k)) nil)
  (kv-increment [_ k]   (if-let [tv *bulk-txn*]
                          (let [v (inc (long (get @tv k 0)))] (vswap! tv assoc! k v) v)
                          (long (get (swap! state update k (fnil inc 0)) k))))
  (kv-decrement [_ k]   (if-let [tv *bulk-txn*]
                          (let [v (dec (long (get @tv k 0)))] (vswap! tv assoc! k v) v)
                          (long (get (swap! state update k (fnil dec 0)) k))))
  (kv-add-to-set [_ k m] (if-let [tv *bulk-txn*]
                           (vswap! tv assoc! k (conj (get @tv k #{}) m))
                           (swap! state update k (fnil conj #{}) m))
    nil)
  (kv-remove-from-set [_ k m]
    (if-let [tv *bulk-txn*]
      (vswap! tv (fn [t] (let [s (disj (get t k #{}) m)]
                           (if (empty? s) (dissoc! t k) (assoc! t k s)))))
      (swap! state (fn [st]
                     (let [s (disj (get st k) m)]
                       (if (empty? s) (dissoc st k) (assoc st k s))))))
    nil)
  ;; the stored set by reference — the O(1) return the in-memory backend is for
  (kv-members [_ k] (get @state k #{}))
  ;; a hash lookup into the stored set, the same read `kv-members` hands back — bulk-blind
  ;; like every other read here, so it agrees with `kv-members` in both modes
  (kv-member? [_ k m] (contains? (get @state k) m))
  (kv-count    [_ k] (count (get @state k)))
  (kv-intersect [_ ks]
    (if (empty? ks)
      #{}
      (let [st @state] (apply set/intersection (map #(get st % #{}) ks)))))
  (kv-batch [_ ops]
    (if-let [tv *bulk-txn*]
      ;; bulk load: fold every op into the transient (no per-op path copy, no swap!);
      ;; index-sentex ignores the replies, so return the aligned nil placeholders.
      (do (vswap! tv (fn [t] (reduce mem-op! t ops))) (mapv (fn [_#] nil) ops))
      ;; apply every op in one swap!, capturing the per-op replies; the capture is
      ;; recomputed each swap attempt, so a retry (never, under single-writer) cannot
      ;; double-count.
      (let [replies (atom nil)]
        (swap! state
               (fn [m]
                 (let [[m' rs] (reduce (fn [[m rs] op]
                                         (let [[m2 r] (mem-op m op)]
                                           [m2 (conj rs r)]))
                                       [m []] ops)]
                   (reset! replies rs)
                   m')))
        @replies)))
  ;; this backend's resident shape already *is* the portable one — structured vector
  ;; keys, Clojure sets and Longs — so both directions are the map itself.
  (kv-entries [_] (seq @state))
  (kv-load [_ entries] (swap! state into entries) nil)

  (kv-clear! [_] (reset! state {}) nil))

(defmacro with-bulk-writes
  "Run `body` with `backend`'s index writes accumulated on one TRANSIENT of its state
  map, persisted back in a single step at the end — the write-side fast path for a bulk
  load (millions of trie `assoc!`s with no per-op HAMT path copy, one `persistent!`
  instead of a `swap!` per fact).  A no-op wrapper unless `backend` is a MemoryKvBackend,
  so a non-memory store (disk) just runs `body` on its own batched path.  See `*bulk-txn*`
  for the read-staleness contract: a positive/monotonic, distinct load only; a corpus
  with `(not …)` facts must `rebuild-opposed!` after."
  [backend & body]
  `(let [bk# ~backend]
     (if (instance? vaelii.impl.memory.MemoryKvBackend bk#)
       (binding [*bulk-txn* (volatile! (transient @(:state bk#)))]
         (try ~@body (finally (reset! (:state bk#) (persistent! @*bulk-txn*)))))
       (do ~@body))))

(defn memory-kv-backend
  "An in-memory `KvBackend`.  Only `:space` in `opts` matters (it selects the shared
  state atom, so two index stores over the same space number share one map)."
  [{:keys [space] :or {space 0}}]
  (->MemoryKvBackend (space-atom index-spaces space {})))

(defn memory-index-store
  "An in-memory `IndexStore` — `KvIndexStore` over a `MemoryKvBackend`."
  [opts]
  (kv/->KvIndexStore (memory-kv-backend opts)))

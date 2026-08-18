;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.disk.record-store
  "The record store on disk — an implementation of `RecordStore` over per-kind
  log/idx pairs (`vaelii.impl.disk.files`).

  Three int-keyed kinds — sentexes, justifications, provenance — each a `.log` of
  length-prefixed nippy frames plus a `.idx` of fixed 24-byte slots mapping handle →
  log offset.  A frame holds its record's fields **positionally**
  (`vaelii.impl.disk.codec`), so the type tag and field names are not rewritten into
  every one of them; a frame written before that codec still reads, as its own shape.  A record is **paged** from disk on `get`: read the slot, read the frame
  it points at, thaw it — two positional reads, no seek, and the records do not sit in
  RAM.  What does sit in RAM per kind is the small set of live handles (so enumeration
  is O(1)), rebuilt from the idx on open, and a **bounded LRU of hot records** in front
  of the read (`vaelii.disk.cache`, 0 to disable).

  `next-id` is a monotonic counter recovered as `max(the counters blob, 1 + the
  highest slot id across the record kinds)` — the highest slot id is stable across
  deletes (a tombstone keeps its slot) and across compaction (slot ids are preserved),
  so a handle is never reused even if the counters blob is stale after a crash.  Within
  a session every write holds the same bound (`clear-counter!`), because a record can
  arrive carrying its own `:id` and nothing re-reads the slots until the next open.

  A premise is exactly a sentex whose `:strength` is non-nil (the strength lives on
  the record, as on every backend), so the premise set is derived from the durable
  records — rebuilt on open, maintained in lockstep by mark/unmark — rather than
  stored separately.  Rebuilding it does not mean *reading* them: every write records
  the answer in its idx slot's flags, so the open reads the set off the slot walk it
  already makes.  A slot that does not carry the bit sends that one handle to its
  record, and the record is authoritative wherever both speak (`rebuild-premises!`).

  The premise's **strength rank** rides the same slot flags (bits 2..3), so
  `premise-strength` — read once per premise on every `recover` — answers off the 24-byte
  slot instead of paging the whole record for one keyword.  A slot carrying no rank (a
  non-premise, or one older than the bits) falls back to the record, the same
  no-format-bump story as the premise bit itself (`f/slot-strength`).

  Recovery on open: finish any interrupted compaction, truncate a torn log tail, then
  tombstone any slot whose frame now extends past the log (`validate-idx-tail!`).
  Crash-safety rests on the write ordering (append the frame, then point the slot at it)
  and on `files`' crash-safe compaction.  Where it stops is the slot itself: 24 bytes do
  not divide a page, so a crash can leave one spliced from two writes, and a splice still
  pointing inside the log reads as a thaw failure on that handle rather than being caught
  here (`f/validate-idx-tail!` says what it does and does not cover).

  The tail is located from the frame *lengths*
  (`files/log-tail-offset`) and nothing is decoded to find it — and a clean `close!`
  records each log's length, so an open whose log is still that long skips even the walk.
  The marker is consumed here, so it never describes a store in use; every disagreement
  falls back to the walk.

  Every RAF touch holds the owning kind's lock.  A write or `force!` must, because the
  file pointer is shared (see `files`' shared-pointer invariant); a read no longer has
  to — the read primitives are positional — but still does, because that is what
  serializes it against a concurrent append and its slot write."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.caches :as caches]
            [vaelii.impl.config :as config]
            [vaelii.impl.disk.codec :as codec]
            [vaelii.impl.disk.files :as f]
            [vaelii.impl.disk.tokens :as dtok]
            [vaelii.impl.io.fingerprint :as fp]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.strength :as strength]))

(def ^:private kind-names ["sentexes" "justifications" "provenance"])

;; `vaelii.disk.tokens` and `vaelii.disk.cache` are read at the store's **open**
;; (`open-record-store`), not here.  A `def` reading a property is a read at namespace
;; load, and a load-time refusal of `vaelii.disk.cache=64k` reports as a namespace that
;; will not load — the typo delivered as a broken build.  `config` owns both domains.

;; ---- the hot-record cache ----------------------------------------------
;; A record fetch is two positional reads plus a nippy thaw (~3 µs warm), and a real
;; query stream is skewed — the same predicates and individuals are fetched over and
;; over.  A bounded LRU in front of the read serves 64% of a zipfian stream at 1k
;; entries and 79% at 10k (`lein bench-records`), and a hit costs a map lookup.
;;
;; Correct because a record is an immutable value: the only ways the record at an id can
;; change are `store!` (which replaces the cached value), `kill!` (which drops it), and
;; `clear-records!` (which empties the cache).  Compaction rewrites frames but preserves
;; every id's content, so it needs no invalidation.
;;
;; A bulk sweep — `export!`, `reindex`, the `recover` a fork runs over a live base —
;; fetches every record through here and so rewrites the recency order.  It promotes like
;; any other read, because what that costs is bounded by the capacity: refilling the
;; working set is capped at `cap` misses while the sweep pays one read per record, so the
;; next queries lose at most `cap / records` of the sweep's own cost.  Measured at 22 ms
;; against a 2.6 s sweep of 800k records (`docs/storage.md`, "A bulk sweep claims
;; recency").

(defn- lru
  "A bounded access-ordered LRU map, synchronized: an access-ordered `LinkedHashMap`
  reorders itself on `get`, so a read is a structural modification and readers must
  synchronize with each other as well as with writers."
  ^java.util.Map [^long cap]
  (java.util.Collections/synchronizedMap
   (proxy [java.util.LinkedHashMap] [16 0.75 true]
     (removeEldestEntry [_] (> (.size ^java.util.LinkedHashMap this) cap)))))

;; `compacting` boxes the copy-on-write compactor's state while a compaction is in
;; flight, else nil.  `store!`/`kill!` fold the ids they touch into `:touched`, and
;; `clear-records!` sets `:aborted` — both under the kind lock, so the compactor's
;; delta reconcile sees a consistent view.  See `compact-kind!`.
(defrecord Kind [log idx lock live-ids log-path idx-path compacting cache enc dec])

(defn- track-touched
  "Record `id` in an in-flight compaction's touched set (a no-op when none is running).
  Called under the kind lock, so it races nothing."
  [k id]
  (swap! (:compacting k) (fn [c] (if c (update c :touched conj id) c))))

(defn- open-kind
  "Open (recovering) the log/idx pair `dir/<name>.{log,idx}` and build its live-id set.

  `clean-length` is what the last clean close recorded for this log, if anything; a log
  still that length has no torn tail and skips the walk.  `validate-idx-tail!` runs
  either way — a skipped scan is not a skipped validation.

  `slot-tap` (optional) is called with `[id flags]` for every live slot, so a caller
  that wants what the slots say rides this walk rather than making a second one."
  [dir name cache-cap codecs clean-length slot-tap]
  (let [log-path (str dir "/" name ".log")
        idx-path (str dir "/" name ".idx")]
    (f/recover-compaction! log-path idx-path)
    (let [log (f/open-log log-path)
          ;; from here to the return every step can throw — a torn tail, a truncation on
          ;; a full disk, an unreadable slot — and a `Kind` that never gets built is one
          ;; nothing will ever close.  So the recovery runs under a guard that gives the
          ;; two handles back before the failure travels.
          idx (try (f/open-idx idx-path)
                   (catch Throwable t (f/close! log) (throw t)))]
      (try
        (f/truncate-log! log (first (f/log-tail-offset-from log clean-length)))
        (f/validate-idx-tail! idx log (f/slot-count idx))     ; tombstone slots past EOF
        (let [live  (java.util.HashSet.)
              {:keys [enc dec]} (codecs name)]
          (f/scan-idx! idx (fn [id _ _ flags]
                             (.add live id)
                             (when slot-tap (slot-tap id flags))))
          (->Kind log idx (Object.) (atom (set live)) log-path idx-path (atom nil)
                  (when (pos? cache-cap) (lru cache-cap)) enc dec))
        (catch Throwable t
          (f/close! log)
          (f/close! idx)
          (throw t))))))

(defn- counters-path [dir] (str dir "/counters.nippy"))

(defn- store!
  "Append `rec` to kind `k`, point slot `id` at the new frame, and mark `id` live.
  Returns `id`.  Holds the kind lock.

  `premise?` is written into the slot's flags so the next open can read the premise set
  off the idx walk instead of decoding every record (`f/premise-flags`).  Only the
  sentexes kind has premises; the other two say so, which is true of them."
  ([k id rec] (store! k id rec false))
  ([k id rec premise?]
   (locking (:lock k)
     (let [off  (f/append-record! (:log k) ((:enc k) rec))
           plen (- (f/log-length (:log k)) off 4)]  ; payload length (frame minus prefix)
       ;; the premise's strength rides the slot too (bits 2..3), so `premise-strength`
       ;; reads it off the idx the open walk already makes rather than paging the record
       (f/write-slot! (:idx k) id off plen
                      (f/premise-flags premise? (strength/rank-of (:strength rec))) 0))
     (track-touched k id))
   (swap! (:live-ids k) conj id)
   ;; a just-written record is hot, and this is also what keeps the cache honest when a
   ;; re-store (mark-premise) replaces an id's record with a different value
   (when-let [^java.util.Map c (:cache k)] (.put c id rec))
   id))

(defn- fetch
  "The record at handle `id` in kind `k`, or nil — from the hot cache, else paged from
  disk (one positional slot read, one positional frame read).  Anything that is not a
  handle this store could have issued reads as nil: a non-integer (callers pass an
  informant keyword/symbol to `get-sentex`) and a negative one (which would otherwise
  reach `read-slot` as a negative file position and throw).  Both are the nil the memory
  store returns for a key it does not hold — a lookup must not depend on the backend."
  [k id]
  (when (and (integer? id) (not (neg? (long id))))
    (let [^java.util.Map c (:cache k)]
      (or (when c (.get c id))
          ;; the lock is kept even though both reads are now positional (they neither use
          ;; nor move the shared pointer): it is what serializes a read against a
          ;; concurrent append + slot write, and an uncontended monitor is noise beside
          ;; the two reads.
          (let [rec (locking (:lock k)
                      (when-let [slot (f/read-slot (:idx k) id)]
                        (when-not (:tombstone? slot)
                          (some-> (f/read-record-sized (:log k) (:offset slot) (:length slot))
                                  ((:dec k))))))]
            (when (and c rec) (.put c id rec))
            rec)))))

(defn- kill!
  "Tombstone handle `id` in kind `k` and drop it from the live set (a no-op when it
  was never live)."
  [k id]
  (when (contains? @(:live-ids k) id)
    (locking (:lock k)
      (f/tombstone-slot! (:idx k) id)
      (track-touched k id))
    (swap! (:live-ids k) disj id)
    (when-let [^java.util.Map c (:cache k)] (.remove c id))))

(defn- clear-counter!
  "Keep `counter` — the next handle to issue — above `id`, and return `id`.  Called on
  every record write, because `put-sentex` / `put-justification` both honour an explicit
  `:id` (an import lands records at the handles its dump gave them) and a counter left
  behind one would reissue it, overwriting a record silently.  Recovery derives the same
  bound from the idx slots on open; this is what holds it *within* a session, where
  nothing re-reads them.  A no-op when the id came from `next-id`."
  [counter id]
  (swap! counter max (inc (long id)))
  id)

(defrecord DiskRecordStore [dir kinds counter premises dict]
  p/RecordStore
  (next-id [_] (long (dec (swap! counter inc))))

  (put-sentex [this sentex]
    (let [id  (clear-counter! counter (or (:id sentex) (p/next-id this)))
          rec (assoc sentex :id id)]
      (store! (:sentexes kinds) id rec (some? (:strength rec)))
      (when (:strength rec) (swap! premises conj id))
      id))
  (get-sentex [_ id] (fetch (:sentexes kinds) id))
  (delete-sentex! [_ id]
    (kill! (:sentexes kinds) id)
    (swap! premises disj id)
    (kill! (:provenance kinds) id)          ; provenance dies with its record
    nil)

  (put-justification [this justification]
    (let [id (clear-counter! counter (or (:id justification) (p/next-id this)))]
      (store! (:justifications kinds) id (assoc justification :id id))
      id))
  (get-justification [_ id] (fetch (:justifications kinds) id))
  (delete-justification! [_ id]
    (kill! (:justifications kinds) id)
    (kill! (:provenance kinds) id)
    nil)

  (put-provenance    [_ id prov] (store! (:provenance kinds) id prov) prov)
  (get-provenance    [_ id]      (fetch (:provenance kinds) id))
  (delete-provenance! [_ id]     (kill! (:provenance kinds) id) nil)

  (sentex-ids    [_] (set @(:live-ids (:sentexes kinds))))
  (justification-ids [_] (set @(:live-ids (:justifications kinds))))

  (mark-premise [_ id strength]
    ;; the strength lives on the sentex record: re-store it with :strength set (a new
    ;; frame; the old one becomes dead and compaction reclaims it), and track the
    ;; premise in the derived set.  Guard on existence — a handle with no sentex must
    ;; not be marked.
    ;;
    ;; A record already carrying this strength is left alone, which is the ordinary
    ;; assert: `kb/create-sentex` writes the strength into the first frame, and a
    ;; re-assert of a stored premise asks for the strength it already has.  Storing it
    ;; again would append a whole second frame and kill the first — half the log dead on
    ;; arrival, and the compaction threshold tripped by the writer's own bookkeeping.
    (let [k    (:sentexes kinds)
          want (or strength :default)]
      (when-let [sx (fetch k id)]
        (when-not (= want (:strength sx))
          (store! k id (assoc sx :strength want) true))
        (swap! premises conj id)))
    nil)
  (unmark-premise! [_ id]
    ;; the same guard as mark-premise, pointing the other way: a derived record's
    ;; :strength is already nil, and re-storing it would append a frame whose only
    ;; fate is the tombstone the retraction writes right after
    (let [k (:sentexes kinds)]
      (when-let [sx (fetch k id)]
        (when (some? (:strength sx))
          (store! k id (assoc sx :strength nil) false))))
    (swap! premises disj id)
    nil)
  (premise-ids      [_] (set @premises))
  (premise-strength [_ id]
    ;; read the rank off the slot (bits 2..3) — one positional 24-byte read, no frame and
    ;; no thaw.  A rank-0 slot carries no strength (a non-premise, or a slot older than the
    ;; strength bits), so it falls back to the record, exactly as the premise bit does for a
    ;; slot that predates it; any write upgrades the slot and the fetch never runs again.
    ;;
    ;; The rank is a cache over the record like the premise bit beside it (`rebuild-premises!`),
    ;; and it shares that bit's flags-word residual: a torn flags page across a crash can leave a
    ;; stale rank on a non-tokenized store until the handle's next write (a tokenized open reads
    ;; every record; a `reindex`/re-mark repairs it).  The record stays the durable truth.
    ;;
    ;; Guard the id as `fetch` does — a non-integer informant or a negative id is the nil the
    ;; memory store answers, not a `read-slot` coercion throw; `premise-strength` must not
    ;; depend on the backend for a key it does not hold.
    (let [k (:sentexes kinds)]
      (if (and (integer? id) (not (neg? (long id))))
        (if-let [slot (locking (:lock k) (f/read-slot (:idx k) id))]
          (let [rank (f/slot-strength (:flags slot))]
            (if (pos? rank)
              (strength/class-of-rank rank)
              (or (:strength (fetch k id)) :default)))
          :default)
        :default)))

  (clear-records! [_]
    (doseq [k (vals kinds)]
      (locking (:lock k)
        (f/truncate! (:log k))
        (f/truncate! (:idx k))
        (reset! (:live-ids k) #{})
        (when-let [^java.util.Map c (:cache k)] (.clear c))
        ;; an in-flight compaction snapshotted the pre-wipe state — tell it to abort
        ;; (discard its temps) rather than replay them over the now-empty files.
        (swap! (:compacting k) (fn [c] (when c (assoc c :aborted true))))))
    (reset! premises #{})
    (reset! counter 1)
    ;; the dictionary goes with them: no frame survives to hold an id, and keeping the
    ;; ids would leave a wiped store carrying its predecessor's whole vocabulary
    (when dict (dtok/clear! dict))
    (f/write-nippy-atomic! (counters-path dir) {:seq 1})
    nil))

(defn slot-fingerprint
  "What the sentexes idx currently says, as `{:count :max-handle :digest}` — the stamp a
  derived-index snapshot is validated against (`vaelii.impl.disk.index-snapshot`).

  It is read off the **slots**, so it costs one sequential pass over a 24-byte-per-record
  file and decodes nothing.  That is the whole point: an image exists so an open reads
  bytes rather than records, and validating it against a content digest (walking every
  record through `fingerprint/accumulator`) would put
  all of them back on the open path.  What it detects is every way the record set can
  change under a snapshot — a record added, deleted, or re-stored (a re-store appends a
  new frame, so the handle's offset moves)."
  [{:keys [kinds]}]
  (let [k   (:sentexes kinds)
        acc (fp/slot-accumulator)]
    (locking (:lock k)
      (f/scan-idx! (:idx k) (fn [id offset length _flags] (acc id offset length))))
    (acc)))

(defn fsync
  "fsync every kind's log + idx and persist the counter.  `fsync?` false drains
  writes to the page cache without the fsync (the durability daemon's non-durable tick).

  The token dictionary is fsynced **first, under the sentexes kind lock** — that lock is
  what stops a record being appended between the two fsyncs, and so is what makes every
  record durable after this tick one whose tokens are durable too."
  [{:keys [dir kinds counter dict]} fsync?]
  (locking (:lock (:sentexes kinds))
    (when dict (dtok/fsync dict fsync?))
    (when fsync?
      (f/force! (:log (:sentexes kinds)) false)
      (f/force! (:idx (:sentexes kinds)) true)))
  (doseq [[kind k] kinds :when (not= kind :sentexes)]
    (locking (:lock k)
      (when fsync?
        (f/force! (:log k) false)
        (f/force! (:idx k) true))))
  (f/write-nippy-atomic! (counters-path dir) {:seq @counter}))

(defn- close-quietly!
  "Run one close step, logging rather than throwing.  A single file that will not close
  must not leave the rest of the store's handles open: `backend/close-dir!` releases
  the directory's OS lock whether this store closed cleanly or not, so a handle still
  open here is open for the life of the JVM over a directory another process may
  already have taken."
  [what thunk]
  (try (thunk)
       (catch Throwable t
         (trove/log! {:level :error
                      :msg (str "disk record store: closing " what " failed: "
                                (.getMessage t))}))))

(defn close!
  "Flush durably, record the log lengths this session closed at, close every RAF, then
  remove the dirty marker (a clean shutdown).

  The lengths are read **after** the fsync and written before anything closes, so the
  marker names exactly what is durable; the next open skips a log's tail walk while its
  length still agrees ([`f/log-tail-offset-from`](files.clj)).

  **Every handle is released whatever the flush did.**  The flush can fail — a full disk
  — and the caller above releases the directory's lock on a failed close as deliberately
  as on a clean one, so a throw that skipped the closes would hand the directory over
  with every `RandomAccessFile` still held.  The dirty marker is the one step that stays
  conditional: it says the store closed cleanly, and an unclean close is what it exists
  to record."
  [{:keys [dir kinds dict] :as store}]
  (try
    (fsync store true)
    (f/write-clean-marker! dir (into {} (map (fn [[kind k]]
                                               [(clojure.core/name kind)
                                                (locking (:lock k) (f/log-length (:log k)))]))
                                     kinds))
    (finally
      (doseq [[kind k] kinds]
        (locking (:lock k)
          (close-quietly! (str (clojure.core/name kind) ".log") #(f/close! (:log k)))
          (close-quietly! (str (clojure.core/name kind) ".idx") #(f/close! (:idx k)))))
      (when dict (close-quietly! "the token dictionary" #(dtok/close! dict)))))
  (f/remove-dirty-marker! dir))

(defn- recover-next-id
  "The counter to start `next-id` from: the max of the persisted blob and one past the
  highest slot id across the sentex + justification kinds (provenance shares their ids)."
  [dir kinds]
  (let [blob (long (:seq (f/read-nippy-file (counters-path dir) {:seq 1})))
        hi   (long (max (f/max-slot-id (:idx (:sentexes kinds)))
                        (f/max-slot-id (:idx (:justifications kinds)))))]
    (max blob (inc hi) 1)))

(defn- rebuild-premises!
  "The premise set on open: the ids whose slot says premise, plus whatever the records
  say for the ids that have to be read.

  Which ids those are is the point of the flags.  A slot written before the premise bit
  existed says nothing about it, so its record is read — once, and never again after any
  write upgrades that slot.  A **tokenized** store reads every live record regardless,
  because that walk is also the token-damage check: a frame naming a token the
  dictionary does not hold is the record log's tail having outrun the dictionary's
  across a machine crash — the same cross-file skew `validate-idx-tail!` repairs between
  the log and its idx, and repaired the same way, by tombstoning the record rather than
  keeping an undecodable one.

  Wherever both speak the **record wins**, which is what makes the bit safe to trust:
  it is derived state over a durable record, exactly like the live-id set beside it.

  On a **dirty** open the walk covers every live record — as a tokenized open already
  does — and the slot flags are reconciled against them (`f/reconcile-slot-flags!`): the
  flags word is a cache and is not crash-atomic, so a torn flags page can leave a slot
  speaking a stale premise bit or strength rank, and the in-memory set the walk rebuilds
  fixes belief for this session but not the slot a later *clean* open would trust.  A slot
  that disagrees with its record is rewritten here, once, on the rare unclean open —
  self-healing, so the next open is fast again."
  [k root dict marked unsaid dirty?]
  (let [prem    (java.util.HashSet. ^java.util.Collection marked)
        walk    (if (or dict dirty?) @(:live-ids k) unsaid)
        damaged (volatile! 0)
        fixed   (volatile! 0)]
    (doseq [id walk]
      ;; only crash damage is repaired by tombstoning: a token the dictionary does not
      ;; hold or a body the codec cannot parse is the log's tail having outrun its
      ;; neighbours.  `:unknown-frame` is the opposite case — a build that cannot
      ;; decode a *valid* record — and rethrows, because a build that cannot read a
      ;; log must not delete it.
      (let [sx (try (fetch k id)
                    (catch clojure.lang.ExceptionInfo t
                      (when-not (#{:damaged-dictionary :malformed-record}
                                 (:type (ex-data t)))
                        (throw t))
                      (vswap! damaged inc)
                      (kill! k id)
                      nil))]
        (if (:strength sx) (.add prem id) (.remove prem id))
        ;; a torn flags page across a crash may have left this slot's bit or rank stale;
        ;; the record is the truth, so rewrite the slot to it wherever they disagree
        (when (and dirty? sx)
          (let [premise? (some? (:strength sx))
                rank     (if premise? (strength/rank-of (:strength sx)) 0)]
            (when (f/reconcile-slot-flags! (:idx k) id premise? rank)
              (vswap! fixed inc))))))
    (when (pos? @damaged)
      (trove/log! {:level :warn
                   :msg (str "disk records: " @damaged " record(s) at " root
                             " cite tokens the dictionary does not hold — tombstoned")}))
    (when (pos? @fixed)
      (trove/log! {:level :warn :id ::flags-reconciled
                   :msg (str "disk records: reconciled " @fixed " slot flag(s) at " root
                             " against their records after an unclean shutdown"
                             " (torn flags page)")}))
    (trove/log! {:level :debug :id ::premise-set
                 :msg (str "disk records: premise set from " (count marked)
                           " annotated slot(s), " (count walk) " record(s) decoded")})
    (set prem)))

(defn open-record-store
  "Open a `DiskRecordStore` rooted at `dir/records`.  Recovers each kind, rebuilds the
  live-id sets, the premise set (sentexes with a non-nil :strength), and the id
  counter, and drops a dirty marker (removed on a clean `close!`).

  `:cache-capacity` sizes the per-kind hot-record LRU, defaulting to the
  `vaelii.disk.cache` property; 0 runs with no cache (what the fetch benchmark measures
  against, and the honest per-fetch cost).  `:tokenize?` writes sentex bodies as ids from
  a durable token dictionary rather than in full, defaulting to the `vaelii.disk.tokens`
  property; it is a *write* choice only — frames written either way always read."
  ([dir] (open-record-store dir nil))
  ([dir {:keys [cache-capacity tokenize?]
         :or   {cache-capacity (config/disk-cache-capacity)
                tokenize?      (config/disk-tokens?)}}]
   (let [root (str dir "/records")]
     (f/ensure-dir! root)
     (f/assert-format! root)
     ;; the dictionary is opened whenever the store *has* one, even with tokenized
     ;; writes off, because frames already written need it to decode
     (let [;; the marker says the last close was unclean; capture it once — it gates the
           ;; flags-word reconcile in `rebuild-premises!`, and is consumed (removed) below
           ;; before the open writes anything
           dirty?  (f/dirty-marker-present? root)
           _       (when dirty?
                     (trove/log! {:level :warn
                                  :msg (str "disk records: unclean shutdown at " root
                                            " — verifying on open")}))
           ;; read before the open writes anything, and drop it: the marker describes a
           ;; store nobody holds, so it can never survive into a session that grows a log
           clean   (when-not dirty? (f/read-clean-marker root))
           _       (f/remove-clean-marker! root)
           ;; Every open below takes file handles, and a throw part-way leaves the ones
           ;; already taken with nothing to close them: the caller gets an exception
           ;; rather than a store, so there is no value to close it *through*, and
           ;; `backend/store-for` releases the directory's lock on its way out — which
           ;; would hand the directory to another process with these logs still held.
           ;; So each open registers its own undo, and a failure runs them.
           closers (java.util.ArrayList.)]
       (try
         (let [dict   (when (or tokenize? (f/token-log-present? root))
                        (let [d (dtok/open-token-log root)]
                          (.add closers #(dtok/close! d))
                          d))
               codecs (codec/by-kind dict tokenize?)
               ;; a premise is a sentex whose :strength is non-nil, and its slot says so —
               ;; so the set rides the idx walk `open-kind` is already making, and only a
               ;; slot that does not say costs a record read (`rebuild-premises!`)
               marked (java.util.HashSet.)
               unsaid (java.util.ArrayList.)
               tap    (fn [id flags]
                        (if-some [premise? (f/slot-premise flags)]
                          (when premise? (.add marked id))
                          (.add unsaid id)))
               kinds  (into {} (map (fn [n]
                                      (let [k (open-kind root n cache-capacity codecs
                                                         (get clean n)
                                                         (when (= n "sentexes") tap))]
                                        (.add closers #(f/close! (:log k)))
                                        (.add closers #(f/close! (:idx k)))
                                        [(keyword n) k])))
                            kind-names)
               counter (atom (recover-next-id root kinds))
               prem    (atom (rebuild-premises! (:sentexes kinds) root dict marked unsaid dirty?))]
           (f/create-dirty-marker! root)
           (->DiskRecordStore root kinds counter prem dict))
         (catch Throwable t
           (doseq [c closers] (close-quietly! "a half-opened record store" c))
           (throw t)))))))

;; ---- compaction ---------------------------------------------------------

(defn- kind-dead-ratio
  "Dead-byte fraction of kind `k`: 1 - live-frame-bytes / log-length.  Live-frame
  bytes are summed from the live slots (offset + 4 + length)."
  ^double [k]
  (locking (:lock k)
    (let [total (f/log-length (:log k))
          live  (volatile! 0)]
      (f/scan-idx! (:idx k) (fn [_ _ length _] (vswap! live + (+ 4 (long length)))))
      (if (pos? total) (- 1.0 (/ (double @live) (double total))) 0.0))))

(defn dead-ratio
  "Max dead-byte ratio across the kinds — the durability daemon's compaction trigger."
  ^double [{:keys [kinds]}]
  (reduce max 0.0 (map kind-dead-ratio (vals kinds))))

(defn- open-compaction-handles!
  "The three handles a rewrite needs, or none of them.  Opened in a `let` the three
  throws would escape, a failure from the second or third leaks the ones already taken
  — a compaction that fails on a full disk is exactly when the process keeps running."
  [log-path log-tmp idx-tmp]
  (let [rlog (f/open-log-read log-path)]
    (try
      (let [tlog (f/open-log log-tmp)]
        (try
          [rlog tlog (f/open-idx idx-tmp)]
          (catch Throwable t (f/close! tlog) (throw t))))
      (catch Throwable t (f/close! rlog) (throw t)))))

(defn- compact-kind!
  "Rewrite kind `k`'s log with only its live frames, preserving slot ids, crash-safely
  — **copy-on-write**, so the O(live) record rewrite does not stall the kind's reads
  and writes.  The rewrite (read + thaw + re-freeze + write every live frame, the
  O(bytes) cost that can run to gigabytes) runs *without* the kind lock, reading the
  log's immutable region through a private read handle; the lock is held only for two
  brief brackets:

  - **snapshot** (front): capture the live slots and `cutoff` = log length, and arm
    delta tracking (`:compacting`), all so appends past `cutoff` and slot mutations
    made during the rewrite are recorded rather than missed.
  - **reconcile + swap** (end): fold the touched ids into the temp (copying their
    current frame, or tombstoning a since-deleted id), preserve the high-water mark,
    fsync, write the commit marker, replay the temps over the originals, drop them.

  Crash-safety is unchanged: the marker is written only after every live-file read the
  reconcile needs has succeeded, so a crash (or a `close!`) before it leaves the
  complete originals authoritative and the temps discarded, and one after it replays
  the fsynced temps.  A `clear-records!` that lands mid-rewrite sets `:aborted`, and the
  reconcile discards the temps rather than resurrecting the wiped state."
  [k]
  (let [{:keys [log-tmp idx-tmp marker]} (f/compact-temp-paths (:log-path k) (:idx-path k))
        ;; snapshot (brief lock) — the live slots as of now; everything so far sits at
        ;; offset < cutoff (immutable), so the rewrite can read it lock-free.
        snapshot (locking (:lock k)
                   (let [live (java.util.ArrayList.)]
                     (f/scan-idx! (:idx k)
                                  (fn [id off len flags] (.add live [id off len flags])))
                     (reset! (:compacting k) {:touched #{} :aborted false})
                     (vec live)))
        [rlog tlog tidx] (open-compaction-handles! (:log-path k) log-tmp idx-tmp)
        ;; the commit point, read by the failure path — see its comment
        committed? (volatile! false)]
    (try
      ;; the expensive rewrite — no lock held; reads the immutable region via `rlog`.
      ;; The flags are carried across from the source slot rather than re-derived: a
      ;; frame moves here without being decoded, so the slot is the only thing that
      ;; knows whether its record is a premise.  Losing them would not lose a premise
      ;; — an unannotated slot is answered from its record — but it would quietly put
      ;; every later open back to decoding the whole store.
      (doseq [[id off _len flags] snapshot]
        (let [rec  (f/read-record rlog off)
              noff (f/append-record! tlog rec)
              plen (- (f/log-length tlog) noff 4)]
          (f/write-slot! tidx id noff plen flags 0)))
      (f/close! rlog)
      ;; reconcile + swap (brief lock)
      (locking (:lock k)
        (let [{:keys [touched aborted]} @(:compacting k)]
          (if aborted
            (do (f/close! tlog) (f/close! tidx)
                (f/delete-compact-temps! marker log-tmp idx-tmp))
            (do
              ;; fold in everything stored/killed during the rewrite: copy the current
              ;; frame of a still-live id, tombstone one that is gone.
              (doseq [id touched]
                (let [slot (f/read-slot (:idx k) id)]
                  (if (and slot (not (:tombstone? slot)))
                    (let [rec  (f/read-record (:log k) (:offset slot))
                          noff (f/append-record! tlog rec)
                          plen (- (f/log-length tlog) noff 4)]
                      (f/write-slot! tidx id noff plen (:flags slot) 0))
                    (f/tombstone-slot! tidx id))))
              ;; preserve the high-water mark so `next-id` (1 + max-slot) never reissues
              ;; a handle: if the highest live-idx slot (a deleted id keeps its slot) is
              ;; not addressable in the temp, tombstone it there.
              (let [final-max (f/max-slot-id (:idx k))]
                (when (> final-max (f/max-slot-id tidx))
                  (f/tombstone-slot! tidx final-max)))
              (f/force! tlog false) (f/force! tidx true)
              (f/close! tlog) (f/close! tidx)
              (f/write-commit-marker! marker {:log (:log-path k)})
              (vreset! committed? true)
              (f/replay-temp-onto-raf! (:log k) log-tmp)
              (f/replay-temp-onto-raf! (:idx k) idx-tmp)
              (f/delete-compact-temps! marker log-tmp idx-tmp)))
          (reset! (:compacting k) nil)))
      (catch Throwable t
        ;; A failure **before the marker** takes the temps with it.  No marker was
        ;; written, so the originals stay authoritative and a *later open* would drop
        ;; them via `recover-log-compaction!` — but the next compaction **in this
        ;; session** never goes through recovery, and `f/open-log` seeks to `.length`
        ;; while `f/open-idx` does not truncate.  It would open these and append, and the
        ;; reconcile would replay a temp holding this run's slots over the live index,
        ;; resurrecting records deleted in between.  A failure **after** the marker must
        ;; leave them: it is the commit point, `replay-temp-onto-raf!` truncates before
        ;; copying, and the next open finishes the replay off the marker.
        (f/close! tlog) (f/close! tidx)
        (when-not @committed? (f/delete-compact-temps! marker log-tmp idx-tmp))
        (throw t))
      (finally
        ;; stop delta tracking even if the rewrite threw
        (reset! (:compacting k) nil)
        (f/close! rlog) (f/close! tlog) (f/close! tidx)))))

(defn compact!
  "Compact every kind's log (reclaim the dead frames left by deletes and premise
  re-stores).  Preserves all live records and their handles."
  [{:keys [kinds]}]
  (doseq [k (vals kinds)] (compact-kind! k)))

;; ---- what a paged store holds, declared ---------------------------------
;;
;; The one cache here an operator sizes rather than inherits (`vaelii.disk.cache`), and
;; the only one whose entries are a KB's own records rather than something derived from
;; them.  Cleared with the store, never by hand: dropping it costs the next read a
;; positional read and a thaw apiece, and the record it holds is the same value the log
;; holds — so there is no derivation to re-measure, only latency to re-pay.

(caches/register-cache
 {:cache    :hot-records
  :label    "Hot records"
  :scope    :kb
  :unit     "records"
  :limit    nil
  :counters nil
  :note     (str "Records already fetched off disk, held per kind in an LRU sized by "
                 "vaelii.disk.cache — so the limit is per kind and the count is across "
                 "them. Blank for a KB whose records are in memory: there is nothing to "
                 "page, and so nothing to hold.")
  :read     (fn [kb]
              (when-let [kinds (:kinds (:records kb))]
                {:entries (reduce + 0 (keep (fn [k]
                                              (some-> ^java.util.Map (:cache k) .size))
                                            (vals kinds)))}))})

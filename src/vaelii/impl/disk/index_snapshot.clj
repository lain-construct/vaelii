;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.disk.index-snapshot
  "A **mapped snapshot** of the columnar index: the compacted index is written to disk once
  and mapped back on open, so the fact-scaled postings live in the page cache instead of
  the heap. The index is derived state, so any doubt about a snapshot discards it and runs
  `reindex`. See docs/storage.md, the image
  section under `:disk-snapshot`.

  Under `<dir>/index/`:

  * `trie.csr` — the trie's six CSR sections (`fcounts` `foffsets` `fedge-tok`
    `fedge-tgt` `fleaf-off` `fhandles`), each a raw little-endian `int` run behind a header
    naming the counts.
  * `roots.csr` — every root family as CSR over `dense-roots`' packed `long` keys (sorted
    keys, an offset column, one shared handle run), plus the scope table the count tries'
    leaves decode through: one `(predicate, position)` pair, `(predicate, position,
    context)` triple or `(context, 0, context)` scope per entry, as three columns with -1
    for a pair's context, indexed by `dense-roots`' `argfam-id`.
  * `roots-fallback.nippy` — the vocabulary-scaled counters no routed family claims. Its
    entry count and byte length ride the meta and are checked on open (`read-fallback`).
  * `tokens.log` — the token dictionary the `int` edges cite, in `vaelii.impl.disk.tokens`'
    format.

  Resident on open: the CSR skeleton (`fcounts` `foffsets` `fedge-tok` `fedge-tgt`), the
  roots' key and offset columns, the scope table, the token dictionary and the fallback
  blob. Mapped: `fleaf-off`, `fhandles` and the roots' handle run.

  The meta records the format, `kv/index-layout-version`, a byte-order tag and
  `record-store/slot-fingerprint`; all must agree on every open, else the open discards the
  snapshot with a reason (`:absent` `:layout-changed` `:records-differ` `:entries-truncated`
  `:unsupported-platform`). A commit writes the sections to temps and fsyncs them, deletes
  the meta, renames the temps into place and writes the meta last, so a crash leaves no meta.
  The commit renames over a mapped file, which Windows refuses: `enabled?` is false there."
  (:require [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.impl.columnar :as col]
            [vaelii.impl.config :as config]
            [vaelii.impl.dense-roots :as roots]
            [vaelii.impl.disk.files :as f]
            [vaelii.impl.disk.tokens :as dtok]
            [vaelii.impl.io.thaw :as safe]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.tokens :as tok]
            [vaelii.impl.types.snapshot :as snapshot-types])
  (:import [java.io File RandomAccessFile]
           [java.nio Buffer ByteBuffer ByteOrder IntBuffer LongBuffer]
           [java.nio.channels FileChannel FileChannel$MapMode]
           [java.nio.file Files Paths StandardCopyOption]
           [java.util Arrays]))

(def ^:const format-version
  "The snapshot's own layout number, beside `kv/index-layout-version` (which says what the
  *entries* mean).  Bump when a section's shape or order changes, or when a packed key
  cites a different scope.  4 packs each `[key ctx]` leaf of a count trie other than the
  argument trie under its context's scope `[ctx 0 ctx]`.  5 packs the taxonomy's supporter
  and length-binding count tries, their nodes interned whole, and every name set, so the
  fallback blob holds counters alone."
  5)

(def ^:private ^:const trie-magic  0x56545249)     ; "VTRI"
(def ^:private ^:const roots-magic 0x56524f54)     ; "VROT"

(def ^:private byte-order-tag
  "The byte order the sections are written in — always little-endian, on every platform,
  since `put-ints!` and `map-ints` both force it.  So an image is portable across
  architectures: a big-endian JVM reads it back correctly, not as noise.  Recorded in the
  meta and checked on load so a future format that changed the order could not be read
  under this one's assumptions — it cannot mismatch an image this code wrote."
  "LITTLE_ENDIAN")

;; ---- the platform the image publishes on --------------------------------

(defn- os-name
  "The platform, as a fn so a test can name one this machine is not — asserting the
  guard by re-reading `os.name` would assert the expression it is checking."
  ^String []
  (str (System/getProperty "os.name")))

(defn- publishable-platform?
  "Can an image be published here? True except on Windows, where `Files/move` with
  `REPLACE_EXISTING` fails over a mapped target. The durable store is unaffected. See
  docs/storage.md, \"The image\"."
  []
  (not (str/starts-with? (str/lower-case (os-name)) "windows")))

(defn enabled?
  "Can this platform serve a mapped image?  True, or a throw — never false.

  Which KBs get an image is `kb/backend-axes`' answer, not this one's: `:index :snapshot`
  names the representation and `kb/snapshot-mode?` reads the axis.  What is left here is
  the platform, and it refuses rather than degrades. An operator who named
  `:disk-snapshot` and silently got `:disk-columnar` would be told nothing about the
  rebuild they think they no longer pay for, which is the whole of what the name bought."
  []
  (when-not (publishable-platform?)
    (throw (ex-info (str "the :snapshot index publishes by renaming a new file over the"
                         " live one while it is mapped, which " (os-name) " does not"
                         " permit.  Take :disk-columnar, which rebuilds its index from"
                         " the records on open, or :disk-log, whose index is durable.")
                    {:type :unsupported-platform :index :snapshot :os (os-name)
                     :remedy {:index :columnar}})))
  true)

(defn snapshot-root ^String [dir] (str dir "/index"))

;; ---- the cadence -------------------------------------------------------
;; The image is written when the directory closes, which is right for what it describes
;; and thin for a writer that runs for weeks: a process killed outright has no image, and
;; the next open pays the whole `reindex` the backend was named to skip.  So the writer
;; refreshes it mid-life, when the live index has drifted far enough from the one on disk.
;;
;; **On the writer's thread, and that is not a detail.**  `vaelii.impl.columnar`'s fields
;; are `^:unsynchronized-mutable` and its docstring says whose job the synchronization is:
;; *"the caller's, to keep its reads on the writer's thread."*  `save!` compacts the live
;; trie in place, so a refresh queued onto `disk/durability.clj`'s compaction executor —
;; where the record store and the KV put theirs, both of them built around a monitor —
;; would mutate this index from a second thread.  The record store can be compacted by the
;; daemon; this index can only be written by whoever writes it.
;;
;; The cost is a stall: a refresh is a full CSR rewrite, not a delta, so the writer waits
;; out an image-sized write.  `vaelii.index.snapshot-drift` and the compaction interval
;; floor are what keep that rare, and `docs/storage.md` states the trade rather than
;; leaving it to be discovered.
;;
;; **The write entry point is the only path that reaches this**, and that scoping is the thing to
;; know before diagnosing an image count.  `kb/create-sentex` asks `due?`; nothing else
;; does.  `reindex/index-one!` posts straight to `p/index-sentex`, and the importer's inline
;; bulk load goes through that same function — so a store filled by `reindex` or by an
;; import gets exactly one image, at the close, whatever the drift threshold says, while the
;; same content arriving through `assert` is measured and can refresh many times over.
;;
;; **And a writer that closes cleanly can decline the refresh outright**, with
;; `vaelii.disk.auto-compact=false` — see `due?`.  A batch that fills a whole KB in one run
;; wants exactly one image, at the end.  The interval floor is the wrong lever for that (it
;; only rate-limits, and moves the record store's compaction with it) and so is the drift
;; ratio, whose `0` is the *most* eager setting rather than the off one.

(defonce ^:private image-state
  ;; `{canonical-snapshot-root {:roots n :at ms}}` — the indexed-root count the image on
  ;; disk holds and when it was written or read.  Drift is measured against the first; the
  ;; second is what the interval floor is applied to.
  ;;
  ;; **Keyed canonically**, because the two sides reach it by different spellings of one
  ;; directory: a save is handed the `:dir` opt as the caller wrote it, and the write entry point
  ;; is handed the KB's own `dir`, which the disk backend has already resolved.  On macOS
  ;; that is `/var/…` against `/private/var/…` — two keys, so the cadence would read a
  ;; baseline nothing ever wrote and never fire.
  (atom {}))

(defn- state-key ^String [dir]
  (let [root (snapshot-root dir)]
    (try (.getCanonicalPath (File. root)) (catch Throwable _ root))))

(defn- note-image! [dir roots]
  (swap! image-state assoc (state-key dir) {:roots (long roots) :at (System/currentTimeMillis)})
  nil)

(defn note-attempt!
  "Restart `dir`'s interval floor without moving its drift baseline. A refresh calls this as
  it begins: only a completed save moves the baseline (`note-image!`), while the clock
  advances whether the save lands, throws or declines (`:unchanged`, `:empty`). A no-op
  for a directory with no cadence state."
  [dir]
  (let [k (state-key dir)]
    (swap! image-state
           (fn [m] (if (contains? m k)
                     (update m k assoc :at (System/currentTimeMillis))
                     m))))
  nil)

(defn note-no-image!
  "Start `dir`'s cadence clock with no image on disk. A `load!` that maps overwrites the
  count; one that rebuilds leaves it. It starts a clock and never resets one: a second
  `open-kb` over a directory whose image is current keeps the baseline. `forget-image!`
  drops the state at close."
  [dir]
  (let [k (state-key dir)]
    (swap! image-state
           (fn [m] (if (contains? m k)
                     m
                     (assoc m k {:roots 0 :at (System/currentTimeMillis)})))))
  nil)

(defn forget-image!
  "Drop `dir`'s cadence state — what a close does, so a directory reopened in this JVM
  measures its drift against the image it actually finds rather than against one this
  process happened to write earlier."
  [dir]
  (swap! image-state dissoc (state-key dir))
  nil)

(defn- drift-of
  "`drift` over a cadence entry already read out of the state."
  ^double [{:keys [roots]} roots-now]
  (cond
    (nil? roots)         0.0
    (zero? (long roots)) (if (pos? (long roots-now)) 1.0 0.0)
    :else (/ (double (Math/abs (- (long roots-now) (long roots)))) (double roots))))

(defn drift
  "How far `roots-now` has moved from the image at `dir`, as a ratio of the image's own
  count — or 0.0 when this JVM has neither written nor read one, since there is nothing
  to have drifted from and a refresh would be writing an image against no baseline."
  ^double [dir roots-now]
  (drift-of (get @image-state (state-key dir)) roots-now))

(defn due?
  "Has `dir`'s image drifted past `vaelii.index.snapshot-drift`, with the interval floor
  `vaelii.disk.compact-min-interval-ms` elapsed since the last attempt? False when
  `vaelii.disk.auto-compact=false`, which is read before `state-key` resolves a path. A
  drift threshold of 0 means any drift, not off. See docs/storage.md, \"The cadence\"."
  [dir roots-now]
  (and (config/disk-auto-compact?)
       (let [{:keys [at] :as st} (get @image-state (state-key dir))]
         (and (some? at)
              (>= (- (System/currentTimeMillis) (long at))
                  (long (config/disk-compact-min-interval-ms)))
              (>= (drift-of st roots-now) (config/index-snapshot-drift))))))

(defn- meta-path      ^String [root] (str root "/snapshot.meta"))
(defn- trie-path      ^String [root] (str root "/trie.csr"))
(defn- roots-path     ^String [root] (str root "/roots.csr"))
(defn- fallback-path  ^String [root] (str root "/roots-fallback.nippy"))

;; ---- raw section i/o ----------------------------------------------------

(def ^:private ^:const chunk-ints 65536)

(defn- put-ints!
  "Append `n` ints of `src` (an `int[]` or an `IntBuffer`) to `ch`, little-endian."
  [^FileChannel ch src ^long n]
  (let [bb (doto (ByteBuffer/allocate (* 4 (int (min n chunk-ints))))
             (.order ByteOrder/LITTLE_ENDIAN))]
    (loop [i 0]
      (when (< i n)
        (let [k (int (min chunk-ints (- n i)))]
          (.clear bb)
          (let [ib (.asIntBuffer bb)]
            (if (instance? IntBuffer src)
              (let [^IntBuffer s (doto (.duplicate ^IntBuffer src) (.position (int i)) (.limit (int (+ i k))))]
                (.put ib s))
              (.put ib ^ints src (int i) k)))
          (.limit ^Buffer bb (* 4 k))
          (.position ^Buffer bb 0)
          (while (.hasRemaining bb) (.write ch bb))
          (recur (+ i k)))))))

(defn- put-longs! [^FileChannel ch ^longs src]
  (let [n  (alength src)
        bb (doto (ByteBuffer/allocate (* 8 (int (min n chunk-ints))))
             (.order ByteOrder/LITTLE_ENDIAN))]
    (loop [i 0]
      (when (< i n)
        (let [k (int (min chunk-ints (- n i)))]
          (.clear bb)
          (.put (.asLongBuffer bb) src (int i) k)
          (.limit ^Buffer bb (* 8 k))
          (.position ^Buffer bb 0)
          (while (.hasRemaining bb) (.write ch bb))
          (recur (+ i k)))))))

(defn- put-header! [^FileChannel ch ints]
  (let [bb (doto (ByteBuffer/allocate (* 4 (count ints))) (.order ByteOrder/LITTLE_ENDIAN))]
    (doseq [v ints] (.putInt bb (int v)))
    (.position ^Buffer bb 0)
    (while (.hasRemaining bb) (.write ch bb))))

(defn- section-len [src] (if (instance? IntBuffer src) (.limit ^IntBuffer src) (alength ^ints src)))

(defn- open-write
  "A truncated `rw` channel on `path`.  The truncate is guarded rather than chained onto
  the open: a `.setLength` that throws leaves a `RandomAccessFile` nothing holds a
  reference to and nothing will close, and a publish that fails on a full disk is
  exactly when the process keeps running."
  ^FileChannel [^String path]
  (let [raf (RandomAccessFile. path "rw")]
    (try (.setLength raf 0) (.getChannel raf)
         (catch Throwable t
           (try (.close raf) (catch Throwable _ nil))
           (throw t)))))

(defn- rename! [^String from ^String to]
  (Files/move (Paths/get from (into-array String []))
              (Paths/get to (into-array String []))
              (into-array java.nio.file.CopyOption
                          [StandardCopyOption/ATOMIC_MOVE StandardCopyOption/REPLACE_EXISTING])))

(defn- map-ints ^IntBuffer [^FileChannel ch ^long off ^long n]
  (-> (.map ch FileChannel$MapMode/READ_ONLY off (* 4 n))
      (.order ByteOrder/LITTLE_ENDIAN)
      (.asIntBuffer)))

(defn- map-longs ^LongBuffer [^FileChannel ch ^long off ^long n]
  (-> (.map ch FileChannel$MapMode/READ_ONLY off (* 8 n))
      (.order ByteOrder/LITTLE_ENDIAN)
      (.asLongBuffer)))

(defn- read-ints
  "A section copied into heap — the resident half of the split."
  ^ints [^FileChannel ch ^long off ^long n]
  (let [^IntBuffer b (map-ints ch off n)
        a (int-array n)]
    (.get b a 0 (int n))
    a))

(defn- read-header ^ints [^FileChannel ch ^long n]
  (let [^IntBuffer b (map-ints ch 0 n)
        a (int-array n)]
    (.get b a 0 (int n))
    a))

;; ---- the token remap ----------------------------------------------------

(defn- sort-edge-runs!
  "Re-sort each node's `[token target]` edge run by token.

  The remap into the durable dictionary's id space permutes the labels, and the frozen
  `-get-child` **binary-searches** the run — so per-node sorted order is part of the
  format rather than an accident of how the trie was built.  Sorted through a packed
  `(token << 32) | index` key so a wide node (a broad relation's level-2 node reaches
  hundreds of thousands of children) costs O(w log w), not the O(w²) an in-place pair
  insertion would."
  [^ints offsets ^ints etok ^ints etgt ^long nodes]
  (dotimes [i nodes]
    (let [lo (aget offsets (int i))
          hi (aget offsets (int (inc i)))
          w  (- hi lo)]
      (when (> w 1)
        (let [keys (long-array w)]
          (dotimes [j w]
            (aset keys j (bit-or (bit-shift-left (long (aget etok (+ lo j))) 32) (long j))))
          (Arrays/sort keys)
          (let [ot (int-array w) og (int-array w)]
            (dotimes [j w]
              (let [src (int (bit-and (aget keys j) 0xffffffff))]
                (aset ot j (aget etok (+ lo src)))
                (aset og j (aget etgt (+ lo src)))))
            (System/arraycopy ot 0 etok lo w)
            (System/arraycopy og 0 etgt lo w)))))))

(defn- durable-remap
  "Intern every in-RAM token into the durable dictionary, in id order, and return the
  `int[]` from in-RAM ids to durable ones.

  It is the identity whenever the snapshot was itself loaded from this dictionary (the
  load rebuilds the in-RAM ids from the log, in order), and a genuine permutation after a
  `reindex` re-interned the vocabulary in arrival order.  Both are correct and only the
  second costs anything: **ids are opaque edge labels**, so what has to be preserved is
  the answers, never the numbers."
  ^ints [dict tl]
  (let [n  (long (tok/token-count dict))
        rm (int-array n)]
    (dotimes [i n] (aset rm i (int (dtok/intern! tl (tok/id-token dict i)))))
    rm))

(defn- remap-edges ^ints [^ints etok ^ints remap]
  (let [n (alength etok)
        o (int-array n)]
    (dotimes [i n] (aset o i (aget remap (aget etok i))))
    o))

;; ---- writing ------------------------------------------------------------

(defn- write-trie! [^String path {:keys [nodes counts offsets edge-tok edge-tgt leaf-off handles]}]
  (let [e (section-len edge-tok)
        h (section-len handles)]
    (with-open [ch (open-write path)]
      (put-header! ch [trie-magic format-version nodes e h 0])
      (put-ints! ch counts   nodes)
      (put-ints! ch offsets  (inc (long nodes)))
      (put-ints! ch edge-tok e)
      (put-ints! ch edge-tgt e)
      (put-ints! ch leaf-off (inc (long nodes)))
      (put-ints! ch handles  h)
      (.force ch true))
    {:nodes nodes :edges e :leaves h}))

(defn- write-roots!
  "The routed families as three columns, and the scope table that decodes the argument
  roots among them.

  The table rides this file rather than a log beside `tokens.log` because the key column
  here is its only reader: the two are written in one pass and discarded as one unit, so
  they cannot drift apart.  `tokens.log` is durable ground truth appended as facts arrive,
  which is why it can disagree with an image and why `:duplicate-tokens` exists to repair
  that."
  [^String path {:keys [keys offsets handles preds positions contexts]}]
  (let [k (alength ^longs keys)
        h (alength ^ints handles)
        a (alength ^ints preds)]
    (with-open [ch (open-write path)]
      (put-header! ch [roots-magic format-version k h a])
      (put-longs! ch keys)
      (put-ints!  ch offsets (inc (long k)))
      (put-ints!  ch handles h)
      (put-ints!  ch preds   a)
      (put-ints!  ch positions a)
      (put-ints!  ch contexts a)
      (.force ch true))
    {:keys k :handles h :scopes a}))

(defn save!
  "Write a mapped snapshot of `store` (a columnar `IndexStore`) under `dir/index`, with
  `(fingerprint-fn)` as its records fingerprint. Returns `{:index :saved …}` or `{:index
  :skipped :reason r}`.

  `fingerprint-fn` is a thunk so `load!` can decline before paying for it; it is called
  first, before any byte moves. The save compacts the trie, then writes every section to a
  `.tmp`, drops the meta, renames the temps into place and writes the meta last. A throw
  before the meta drop leaves the previous image readable and deletes the temps. An empty
  index saves nothing and drops any surviving meta."
  [dir store fingerprint-fn]
  (let [root (snapshot-root dir)]
    (f/ensure-dir! root)
    (cond
      (not (col/columnar? store))
      {:index :skipped :reason :not-columnar}

      (zero? (long (p/count-at store [])))
      (do (.delete (File. (meta-path root)))
          {:index :skipped :reason :empty})

      ;; Still reading out of the image it was opened from, so the image *is* this index
      ;; and rewriting it would be pure loss: the roots' `snapshot-read` thaws them to read
      ;; them, which would pull the whole cold tail back into heap at the very moment the
      ;; KB is closing.  A write would have thawed one or both halves and this is false.
      (and (snapshot-types/snapshot-mapped? (:trie store))
           (snapshot-types/snapshot-mapped? (:roots store)))
      {:index :skipped :reason :unchanged}

      :else
      (with-open [_ (progress/start ::save (str (.getName (File. (str dir))) ": write the index snapshot") nil)]
        (let [t0    (System/nanoTime)
              fp    (fingerprint-fn)
              ;; **Freezing the live trie under an unconsumed lazy read is safe**, and it is
              ;; worth noting so, because the write entry point reaches here mid-life while a caller
              ;; may be holding one: `core/sentexes-matching` promises a seq that is lazy over
              ;; live state, and asserting while walking one is the supported pattern
              ;; `forward-chain` is built on.  What makes it safe is that an index read is
              ;; eager *per read* — `res/candidate-handles` has realized its handles before
              ;; `match-one` returns, and `t-lookup` builds its answer with `into #{}` — so no
              ;; walk is ever part-way through the trie when this runs.  What stays lazy above
              ;; is the `get-sentex` per handle, which is the record store's, and at a variable
              ;; context one whole index read per reader (`vantage/fan-distinct`), which lands
              ;; either side of the freeze and never inside it.  The read primitives dispatch
              ;; on `frozen?` at call time (`vaelii.impl.columnar`), so the reader after this
              ;; reads the CSR and answers the same set.
              _     (col/compact! store)
              csr   (snapshot-types/snapshot-read (:trie store) nil)
              dict  (:dict store)
              rts   (:roots store)
              tmp   #(str % ".tmp")
              ;; named out here so the `finally` can reach them: a save that throws
              ;; part-way leaves the previous image whole, but it also leaves behind
              ;; whatever `.tmp` sections it had already written — index-sized files,
              ;; which on a KB that is never reopened sit in the directory for good.
              ;; They are cleared on the way out unless the meta committed, and deleting
              ;; a temp that was already renamed is a harmless false.
              temps [(tmp (trie-path root)) (tmp (roots-path root)) (tmp (fallback-path root))]
              done  (volatile! false)
              ;; this fn's own handle on the durable dictionary, and every step below it
              ;; can throw — a full disk mid-write, a mapped section that will not read.
              ;; It closes in a `finally`, or a failed save would leak a file handle on
              ;; exactly the directory a `close-dir!` is trying to let go of.
              tl    (dtok/open-token-log root)]
          (try
            (let [remap (durable-remap dict tl)
                  etok  (remap-edges (:edge-tok csr) remap)
                  ;; a copy, because `sort-edge-runs!` permutes it and the live index's own
                  ;; array must not move.  The skeleton is heap `int[]` in every trie mode —
                  ;; only the leaf pair is ever mapped (`trie/snapshot-read`), and the walk reads
                  ;; edge targets at every frontier node, so they never page — so this is an
                  ;; array clone, never a buffer read.
                  etgt  (aclone ^ints (:edge-tgt csr))
                  _     (sort-edge-runs! (:offsets csr) etok etgt (:nodes csr))
                  cols  (merge (snapshot-types/snapshot-read rts {:remap remap})
                               (roots/argfam-table rts remap))
                  tstat (write-trie!  (tmp (trie-path root))
                                      (assoc csr :edge-tok etok :edge-tgt etgt))
                  rstat (write-roots! (tmp (roots-path root)) cols)
                  fents (vec (roots/fallback-entries rts))]
              ;; beside its target rather than over it, so the blob the previous meta
              ;; describes stays intact until the swap below
              (f/write-nippy-atomic! (tmp (fallback-path root)) fents)
              (dtok/fsync tl)
              ;; the meta is the commit point: drop it, swap the sections in, write it last
              (.delete (File. (meta-path root)))
              (rename! (tmp (trie-path root))     (trie-path root))
              (rename! (tmp (roots-path root))    (roots-path root))
              (rename! (tmp (fallback-path root)) (fallback-path root))
              (f/write-nippy-atomic!
               (meta-path root)
               {:format       format-version
                :index-layout kv/index-layout-version
                :byte-order   byte-order-tag
                :records      fp
                :trie         tstat
                :roots        rstat
                ;; the blob carries the counters the planner prices a scan by, so its size
                ;; is recorded and checked like the CSR sections'
                :fallback     {:entries (count fents)
                               :bytes   (.length (File. (fallback-path root)))}
                :tokens       (dtok/token-count tl)})
              (vreset! done true)
              (note-image! dir (p/count-at store []))
              (let [ms (/ (- (System/nanoTime) t0) 1e6)]
                (trove/log! {:level :info :id ::saved
                             :msg (format "%s: wrote the index snapshot in %.1f s (%,d nodes, %,d leaf handles, %,d root postings)"
                                          (.getName (File. (str dir))) (/ ms 1e3) (long (:nodes tstat)) (long (:leaves tstat)) (long (:keys rstat)))})
                {:index :saved :ms ms :trie tstat :roots rstat}))
            ;; the deletes first, because `.delete` answers false where the close throws:
            ;; a token log that will not close must not be the reason index-sized temps
            ;; are left behind, and it is still the failure the caller reads.
            (finally
              (when-not @done
                (doseq [^String p temps] (.delete (File. p))))
              (dtok/close! tl))))))))

;; ---- reading ------------------------------------------------------------

(defn- file-len ^long [^String path] (let [f (File. path)] (if (.exists f) (.length f) -1)))

(defn- decision
  "Why this open cannot map the snapshot, or nil when it can. Each mismatch class is its own
  reason. The record fingerprint runs ahead of the three truncation tests, so a truncated
  image pays the slot scan before rejection."
  [root m fingerprint-fn]
  (let [{:keys [nodes edges leaves]} (:trie m)
        {kn :keys hn :handles}       (:roots m)]
    (cond
      (nil? m)                                       :absent
      ;; An image is readable here and could never be refreshed: the publish is what the
      ;; platform refuses, and a mapped index that cannot be rewritten is a cache that
      ;; goes stale against its own records the moment one moves.  So it joins the
      ;; mismatch classes beside byte order, which is the same portability question one
      ;; layer down, and inherits their reindex path.
      (not (publishable-platform?))                  :unsupported-platform
      (not= format-version (:format m))              :layout-changed
      (not= kv/index-layout-version (:index-layout m)) :layout-changed
      (not= byte-order-tag (:byte-order m))          :byte-order
      (not= (:records m) (fingerprint-fn))                 :records-differ
      (or (nil? nodes) (nil? kn))                    :entries-truncated
      (< (file-len (trie-path root))
         (+ 24 (* 4 (+ (long nodes) (inc (long nodes)) (long edges) (long edges)
                       (inc (long nodes)) (long leaves)))))
      :entries-truncated
      (< (file-len (roots-path root))
         (+ 20 (* 8 (long kn)) (* 4 (inc (long kn))) (* 4 (long hn))
            (* 12 (long (or (:scopes (:roots m)) 0)))))
      :entries-truncated
      ;; the fallback blob is read whole, so its length is checked exactly — a
      ;; missing file (-1) and a meta with no record of it both land here
      (not= (file-len (fallback-path root))
            (long (or (:bytes (:fallback m)) -2)))
      :entries-truncated
      :else nil)))

(defn- load-trie! [store ^String path {:keys [nodes edges leaves]}]
  (with-open [raf (RandomAccessFile. path "r")]
    (let [ch  (.getChannel raf)
          ^ints hdr (read-header ch 6)]
      (when-not (= trie-magic (aget hdr 0))
        ;; A sentence, because this message is spliced into the user-visible WARN at
        ;; `mount-or-rebuild!` — "the index snapshot at /var/kb did not read (trie
        ;; snapshot magic)" told a reader nothing about whether their data was gone.
        (throw (ex-info (str "the trie file is not a vaelii trie snapshot — its magic number is "
                             (aget hdr 0) ", expected " trie-magic
                             "; the index will be rebuilt from the records, which are untouched")
                        {:type :bad-snapshot :part :trie :path path
                         :magic (aget hdr 0) :expected trie-magic})))
      (let [n   (long nodes) e (long edges) h (long leaves)
            o1  24
            o2  (+ o1 (* 4 n))
            o3  (+ o2 (* 4 (inc n)))
            o4  (+ o3 (* 4 e))
            o5  (+ o4 (* 4 e))
            o6  (+ o5 (* 4 (inc n)))]
        (snapshot-types/snapshot-install!
         (:trie store)
         ;; resident: the skeleton the walk reads at every frontier node
         {:counts*   (read-ints ch o1 n)
          :offsets*  (read-ints ch o2 (inc n))
          :edge-tok* (read-ints ch o3 e)
          :edge-tgt* (read-ints ch o4 e)
          ;; mapped: the leaves, read once at a walk's terminus
          :leaf-off* (map-ints ch o5 (inc n))
          :handles*  (map-ints ch o6 h)})))))

(defn- load-roots!
  "Map the three routed columns, and read the scope table resident.

  The table is vocabulary-scaled — one entry per `(predicate, position)` pair and per
  `(predicate, position, context)` triple the corpus exhibits — so it joins the resident
  half of the split beside the key and offset columns
  rather than the mapped half.  It is read before the columns are installed: a packed
  argument key whose scope id decodes to nothing is a key that answers the wrong posting,
  and the throw belongs before the install rather than at the first read after it."
  [store ^String path {kn :keys hn :handles an :scopes}]
  (with-open [raf (RandomAccessFile. path "r")]
    (let [ch  (.getChannel raf)
          ^ints hdr (read-header ch 5)]
      (when-not (= roots-magic (aget hdr 0))
        (throw (ex-info (str "the roots file is not a vaelii roots snapshot — its magic number is "
                             (aget hdr 0) ", expected " roots-magic
                             "; the index will be rebuilt from the records, which are untouched")
                        {:type :bad-snapshot :part :roots :path path
                         :magic (aget hdr 0) :expected roots-magic})))
      (let [k  (long kn) h (long hn) a (long (or an 0))
            o1 20
            o2 (+ o1 (* 8 k))
            o3 (+ o2 (* 4 (inc k)))
            o4 (+ o3 (* 4 h))
            o5 (+ o4 (* 4 a))
            o6 (+ o5 (* 4 a))]
        (roots/load-argfam! (:roots store) (read-ints ch o4 a) (read-ints ch o5 a)
                            (read-ints ch o6 a) a)
        (snapshot-types/snapshot-install!
         (:roots store)
         {:keys    (map-longs ch o1 k)          ; resident enough to be read
          :offsets (map-ints  ch o2 (inc k))
          :handles (map-ints  ch o3 h)
          :n       k})))))

(defn- load-dictionary!
  "Rebuild the in-RAM dictionary from the durable log in id order, so an in-RAM id is the
  durable id the mapped edges cite. O(dictionary), which is fact-scaled. A count mismatch
  (a log holding `2` and `(int 2)` as two frames, which both dictionaries key as one token)
  throws into `load!`'s catch after `repair-duplicates!` drops the commit marker first and
  rewrites the log without the pair. That renumbering is legal only for this log, whose ids
  only the mapped edges cite. See docs/storage.md, \"The image\"."
  [dict ^String root]
  (let [tl (dtok/open-token-log root)]
    (try
      (let [dups (dtok/duplicate-count tl)]
        (when (pos? dups)
          (.delete (File. (meta-path root)))
          (let [kept (dtok/repair-duplicates! tl)]
            (throw (ex-info (str "the durable token dictionary at " root " holds " dups
                                 " token(s) an older build wrote twice — Java-unequal but"
                                 " Clojure-equal, an integral pair such as 2 and (int 2)"
                                 " — so it reloads one entry short of the log per"
                                 " duplicate and every id past the first has shifted."
                                 " The log has been rewritten without them (" kept
                                 " entries) and the index is being rebuilt from the"
                                 " records, which are untouched; nothing is owed, and the"
                                 " next open maps its image again")
                            {:type :duplicate-tokens :path root
                             :duplicates dups :entries kept})))))
      (tok/clear-tokens! dict)
      ;; interned on the way in, shape preserved.  A token is often a whole compound
      ;; term — the term index is keyed by one per record — so a dictionary rebuilt
      ;; without this holds a private copy of every name in every one of them, which is
      ;; the opposite of what interning the vocabulary is for.  `intern-deep` rather than
      ;; `canon`, since a `[::subterm k]` marker and a rule's antecedent are vectors and
      ;; canonicalizing would flatten both to lists.
      (let [durable (dtok/token-count tl)]
        (with-open [r (progress/start ::load-dictionary
                                      (str (.getName (.getParentFile (File. root)))
                                           "/index: load the tokens into the dictionary")
                                      durable)]
          (dotimes [i durable]
            (tok/intern-token! dict (sx/intern-deep (dtok/token tl i)))
            (progress/tick! r)))
        (let [loaded (long (tok/token-count dict))]
          (when (not= loaded durable)
            (throw (ex-info (str "the durable token dictionary at " root " reloaded as "
                                 loaded " entries where it holds " durable
                                 " — the ids the mapped edges cite have shifted")
                            {:type :torn-snapshot :path root
                             :durable durable :loaded loaded}))))
        durable)
      (finally (dtok/close! tl)))))

(defn- read-fallback
  "The fallback blob, read strictly: it carries the vocabulary's counters, the predicate
  extent's among them, so a torn thaw or an entry count that disagrees with the meta
  throws (into `load!`'s catch, which rebuilds) rather than defaulting to an empty value
  the index would then serve as a count of 0 for every predicate."
  [root m]
  (let [v    (f/read-nippy-file (fallback-path root) ::torn)
        want (long (get-in m [:fallback :entries] -1))]
    (when (or (= ::torn v) (not= (count v) want))
      (throw (ex-info (str "the roots fallback blob did not thaw whole — "
                           (if (= ::torn v)
                             "unreadable"
                             (str (count v) " entries where the meta records " want))
                           " — and it holds the vocabulary's counters, the predicate"
                           " extent's among them")
                      {:type :torn-snapshot :path (fallback-path root)
                       :entries (when-not (= ::torn v) (count v)) :expected want})))
    v))

(defn load!
  "Map `dir/index` into `store`. Returns `{:index :mapped …}` or `{:index :rebuild :reason r}`
  with `r` one of `:absent` `:layout-changed` `:byte-order` `:unsupported-platform`
  `:records-differ` `:entries-truncated` `:duplicate-tokens` `:unreadable`. The caller
  reindexes on any `:rebuild`. `:duplicate-tokens` also repairs the log (`load-dictionary!`).
  A `VirtualMachineError` in a failed map's cause chain (`safe/vm-error`) empties `store`
  and is rethrown as itself."
  [dir store fingerprint-fn]
  (let [root (snapshot-root dir)
        m    (f/read-nippy-file (meta-path root) nil)]
    ;; sized from the image's count whatever the decision, since a rebuild thaws every
    ;; record and re-interns the same vocabulary (`sentex/size-symbol-pool`)
    (when (integer? (:tokens m)) (sx/size-symbol-pool (:tokens m)))
    (cond
      (not (col/columnar? store)) {:index :rebuild :reason :absent}
      (nil? m)                    {:index :rebuild :reason :absent}
      :else
      (if-let [why (decision root m fingerprint-fn)]
        {:index :rebuild :reason why}
        (try
          (let [t0 (System/nanoTime)]
            (p/clear-index! store)                     ; also wipes the shared dictionary
            (load-dictionary! (:dict store) root)
            (load-trie!  store (trie-path root)  (:trie m))
            (load-roots! store (roots-path root) (:roots m))
            (roots/load-fallback! (:roots store) (read-fallback root m))
            (note-image! dir (p/count-at store []))
            (let [ms (/ (- (System/nanoTime) t0) 1e6)]
              (trove/log! {:level :info :id ::mapped
                           :msg (format "%s: mapped the index snapshot in %.1f s (%,d tokens, %,d nodes)"
                                        (.getName (File. (str dir))) (/ ms 1e3) (long (:tokens m)) (long (:nodes (:trie m))))})
              {:index :mapped :ms ms :trie (:trie m) :roots (:roots m)}))
          (catch Throwable t
            (when-let [e (safe/vm-error t)]
              (p/clear-index! store)
              (throw e))
            ;; a cause this open could do something about names itself, so the operator
            ;; reads what happened rather than "did not read" a third time
            (let [why (if (= :duplicate-tokens (:type (ex-data t))) :duplicate-tokens :unreadable)]
              (trove/log! {:level :warn :id ::unreadable
                           :msg (str "the index snapshot at " root " did not read ("
                                     (.getMessage t) ") — rebuilding from the records")})
              (p/clear-index! store)
              {:index :rebuild :reason why})))))))

(defn discard!
  "Delete a snapshot's commit marker — what a caller does when it knows the image is dead
  and would rather the next open not have to work that out."
  [dir]
  (.delete (File. (meta-path (snapshot-root dir))))
  nil)

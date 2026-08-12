;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.disk.files
  "Low-level file primitives for the on-disk backend.

  - Append-only `.log` files hold length-prefixed nippy frames.
    Frame layout: `[len: i32 big-endian][nippy-bytes]`.  The offset returned from
    `append-record!` points at the len prefix.
  - `.idx` files are fixed-width arrays of 24-byte slots, indexed by id.
    Slot layout:
      bytes  0..7  offset (i64, -1 = empty, -2 = tombstone)
      bytes  8..15 length (i64)
      bytes 16..19 flags  (u32; bit 0 = the premise bit is meaningful, bit 1 = premise)
      bytes 20..23 gen    (u32, reserved — written as 0)
    Reads rely on the OS page cache; writes overwrite the slot in place.
    A slot is read in **one positional channel read**, not a seek plus four primitive
    `readLong`/`readInt` calls — a `RandomAccessFile` is unbuffered, so each of those is
    its own syscall and moving 24 bytes cost six of them (measured: 52% of a warm
    record fetch, `lein bench-records`).
  - `.nippy` files hold whole-blob metadata (counters, the premise set).  Callers
    rewrite them atomically via `write-nippy-atomic!`.

  **Shared-pointer invariant.**  A seek→read/write pair on a `RandomAccessFile` uses that
  object's single shared file pointer, so any access to a store's live RAF must hold the
  owning kind lock; the disk adapters take a per-kind lock around every such touch (write,
  `force!`) for exactly this reason.  The *read* primitives here (`read-slot`,
  `read-record`, `read-record-sized`) are positional `FileChannel` reads instead — they
  name the file offset in the call and never touch the pointer, so they neither disturb a
  concurrent seek nor need one of their own.

  Compression: frames freeze under the nippy compressor named by the
  `vaelii.disk.compress` system property (`lz4` | `zstd` | `none`); default none.
  nippy reads the compressor id from each frame header, so mixed frames thaw
  correctly.  Durability: `vaelii.disk.fsync=dsync` opens logs `rwd` (O_DSYNC) so
  every append is synchronous — off by default (the durability daemon fsyncs on a
  tick instead)."
  (:require [clojure.edn :as edn]
            [taoensso.nippy :as nippy]
            [taoensso.trove :as trove]
            [vaelii.impl.config :as config])
  (:import [java.io DataInputStream DataOutputStream File
            RandomAccessFile FileInputStream FileOutputStream
            BufferedInputStream BufferedOutputStream]
           [java.nio.channels FileChannel]
           [java.nio.file Files Paths StandardCopyOption OpenOption
            StandardOpenOption]))

(def slot-bytes
  "Fixed slot width in `.idx` files: 8 (offset) + 8 (length) + 4 (flags) + 4 (gen) = 24."
  24)

(def empty-offset     "Slot offset meaning 'nothing stored at this id'." -1)
(def tombstone-offset "Slot offset meaning 'this id was deleted'."       -2)

(defn ensure-dir!
  "Create the directory at `path` (and any missing parents); return the `File`."
  ^File [^String path]
  (doto (File. path) (.mkdirs)))

(def format-version
  "On-disk layout version for a backend directory.  Bumped only on an incompatible
  layout change; a directory written before the sentinel is adopted as version 1."
  1)

(def ^:private supported-format-versions #{1})

(defn assert-format!
  "Gate the store directory `root` on its `format.edn` sentinel: a known version is
  ok, an unknown one throws, and a missing sentinel is stamped with the current
  version (a pre-sentinel directory is by definition today's layout)."
  [root]
  (let [file (File. (str root) "format.edn")]
    (if (.exists file)
      (let [v (:format-version (edn/read-string (slurp file)))]
        (when-not (contains? supported-format-versions v)
          (throw (ex-info (str "Unsupported :disk KB format version " v " at " root
                               " — this engine supports " (sort supported-format-versions) ".")
                          {:type :unsupported-format :found v
                           :supported supported-format-versions :root (str root)}))))
      (spit file (pr-str {:format-version format-version})))))

(def ^:private index-layout-file "layout.edn")

(defn index-layout-decision
  "Gate an index directory `root` on its `layout.edn` sentinel against `current`
  (`kv/index-layout-version`), as one of three answers: `:current` when the stamp
  matches, `:stale` when it does not — an absent stamp over a `populated?` log
  included, which is what an index written before the sentinel existed looks like —
  and `:unstamped` for a fresh, empty directory, which needs the stamp but no
  rebuild.  A stale log replays cleanly and then misses every read whose key shape
  moved, so `:stale` is the caller's cue to clear the index, rebuild it from the
  records, and then `stamp-index-layout!`.

  **This reads and never writes.** A base mounted under `:base` opts is gated by the
  same call and may not be written to, so the stamp `:unstamped` calls for is the
  caller's to make — `stamp-index-layout!` for a KB that owns the directory, nothing
  at all for a read-only mount."
  [root current populated?]
  (let [file (File. ^String (str root) ^String index-layout-file)]
    (if (.exists file)
      (if (= current (:index-layout (edn/read-string (slurp file)))) :current :stale)
      (if populated? :stale :unstamped))))

;; A rebuild's *first* write, not its last: `index-layout-decision` reads an absent
;; stamp over an empty index as `:unstamped`, so a crash between the clear and the
;; rebuild's first frame would otherwise leave a directory that opens clean — an empty
;; index over full records, answering nothing.  Marking the directory before the clear
;; makes that window read as `:stale` instead, and `stamp-index-layout!` is what clears
;; the mark.  Any value that is not `current` would do; naming the state says why it is
;; there when somebody reads the file after a crash.
(defn mark-index-rebuilding!
  "Stamp `root`'s `layout.edn` as mid-rebuild, so an open that lands before
  `stamp-index-layout!` reads `:stale` and rebuilds again."
  [root]
  (spit (str root "/" index-layout-file) (pr-str {:index-layout ::rebuilding}))
  nil)

(defn stamp-index-layout!
  "Write `root`'s `layout.edn` naming `current` — the commit mark of a layout
  rebuild (`index-layout-decision`)."
  [root current]
  (spit (str root "/" index-layout-file) (pr-str {:index-layout current}))
  nil)

(defn- dsync? [] (= :dsync (config/disk-fsync-mode)))

(defn- open-rw ^RandomAccessFile [^String path ^String mode]
  (let [parent (.getParentFile (File. path))]
    (when (and parent (not (.exists parent))) (.mkdirs parent)))
  (RandomAccessFile. path mode))

(defn open-log
  "Open a log file for append + read, positioned at EOF.  Under
  `vaelii.disk.fsync=dsync` the channel is `rwd` so every append is durable."
  ^RandomAccessFile [^String path]
  (let [raf (open-rw path (if (dsync?) "rwd" "rw"))]
    (.seek raf (.length raf))
    raf))

(defn open-idx
  "Open an idx file for random read/write.  Always `rw` — idx slots are
  reconstructible from the logs, so they need no per-write durability."
  ^RandomAccessFile [^String path]
  (open-rw path "rw"))

(defn open-log-read
  "Open a private read-only RAF on an existing log.  The copy-on-write compactor reads
  the log's immutable (already-written) region through its own handle, so it needn't
  hold the kind lock while it does the O(live) rewrite — a fresh RAF has its own file
  pointer, so this does not touch the shared-pointer invariant of the store's live RAF."
  ^RandomAccessFile [^String path]
  (open-rw path "r"))

(defn close! [^java.io.Closeable c] (when c (.close c)))

(defn force!
  "fsync `raf`'s channel; `meta-data?` includes file metadata (mtime, length)."
  [^RandomAccessFile raf meta-data?]
  (.force (.getChannel raf) (boolean meta-data?)))

(defn- disk-compressor []
  (case (config/disk-compress)
    :zstd nippy/zstd-compressor
    :lz4  nippy/lz4-compressor
    nil))

(defn- freeze-bytes ^bytes [value]
  (if-let [c (disk-compressor)]
    (nippy/freeze value {:compressor c})
    (nippy/freeze value)))

(defn- thaw-bytes [^bytes bs] (nippy/thaw bs))

(defn append-record!
  "Append a nippy-serialized value to the log; return the byte offset of the `[len]`
  prefix.  The length prefix + payload are packed into one buffer and written with a
  single `.write` (a per-record append is the hot path; four one-byte `writeInt`
  syscalls would dominate).  Caller must hold the log's write lock."
  ^long [^RandomAccessFile log-raf value]
  (let [bs  (freeze-bytes value)
        n   (alength bs)
        off (.length log-raf)
        buf (byte-array (+ 4 n))
        bb  (java.nio.ByteBuffer/wrap buf)]
    (.putInt bb n)
    (.put bb bs)
    (.seek log-raf off)
    (.write log-raf buf)
    off))

(defn- read-at
  "Fill `bb` from `ch` starting at file position `pos`; true iff it filled completely
  (false at EOF).  A positional channel read names its offset, so it neither uses nor
  moves the RAF's shared file pointer."
  [^FileChannel ch ^java.nio.ByteBuffer bb ^long pos]
  (loop [p pos]
    (if (zero? (.remaining bb))
      true
      (let [n (.read ch bb p)]
        (if (neg? n) false (recur (+ p (long n))))))))

(defn read-record-sized
  "Thaw the frame at `offset` whose payload is `length` bytes — **one** positional read,
  of the payload alone.  The slot already recorded the payload length, so a caller
  holding the slot needs neither a seek nor a re-read of the length prefix."
  [^RandomAccessFile log-raf ^long offset ^long length]
  (when (and (>= offset 0) (pos? length))
    (let [bb (java.nio.ByteBuffer/allocate (int length))]
      (when (read-at (.getChannel log-raf) bb (+ offset 4))
        (thaw-bytes (.array bb))))))

(defn read-record
  "Read a nippy value from the log at `offset`; nil for a negative or past-EOF offset.
  For a caller that holds the slot, `read-record-sized` is one read instead of two."
  [^RandomAccessFile log-raf ^long offset]
  (when (>= offset 0)
    (let [ch  (.getChannel log-raf)
          hdr (java.nio.ByteBuffer/allocate 4)]
      (when (read-at ch hdr offset)
        (read-record-sized log-raf offset (.getInt hdr 0))))))

(defn log-length ^long [^RandomAccessFile log-raf] (.length log-raf))

(defn read-slot
  "Read a slot by id: `{:offset :length :flags :gen :tombstone?}`, or nil when the
  slot is past EOF (unwritten), empty (offset=-1), or a zero-filled gap
  (offset=0 AND length=0, left by `.setLength` growing the idx past its high-water
  mark — no real record has length 0, so this is unambiguous).

  One positional read of the 24 bytes, decoded in memory: a short read *is* the
  past-EOF test, so this costs neither a `.length` call to make that test nor a seek
  and four primitive reads to satisfy it."
  [^RandomAccessFile idx-raf ^long id]
  (let [bb (java.nio.ByteBuffer/allocate slot-bytes)]
    (when (read-at (.getChannel idx-raf) bb (* id slot-bytes))
      (let [offset (.getLong bb 0)
            length (.getLong bb 8)
            flags  (long (bit-and 0xffffffff (.getInt bb 16)))
            gen    (long (bit-and 0xffffffff (.getInt bb 20)))]
        (when (and (not= offset empty-offset)
                   (not (and (zero? offset) (zero? length))))
          {:offset offset :length length :flags flags :gen gen
           :tombstone? (= offset tombstone-offset)})))))

;; ---- slot flags ---------------------------------------------------------
;; Two bits of the reserved `flags` word, because one would not be enough: a slot
;; written before they existed reads as 0, and 0 must mean **unknown** rather than
;; "not a premise".  So bit 0 says the slot speaks at all and bit 1 is what it says.
;; A store therefore needs no version bump and no declaration anyone could set wrongly
;; — a slot written by an older build is answered from its record, and any write
;; upgrades it.

(def ^:private flag-premise-known 0x1)
(def ^:private flag-premise       0x2)

(defn premise-flags
  "The `flags` word for a slot whose record is, or is not, a premise."
  ^long [premise?]
  (if premise? (bit-or flag-premise-known flag-premise) flag-premise-known))

(defn slot-premise
  "What `flags` says about its record: `true`, `false`, or **nil** for a slot that does
  not say — which is what sends a caller to the record itself."
  [^long flags]
  (when (pos? (bit-and flags flag-premise-known))
    (pos? (bit-and flags flag-premise))))

(defn write-slot!
  "Write a slot for `id`, growing the idx file if needed (the gap is zero-filled and
  read back as unwritten)."
  [^RandomAccessFile idx-raf id offset length flags gen]
  (let [pos (* (long id) slot-bytes)]
    (when (> pos (.length idx-raf)) (.setLength idx-raf pos))
    (.seek idx-raf pos)
    (.writeLong idx-raf (long offset))
    (.writeLong idx-raf (long length))
    (.writeInt  idx-raf (unchecked-int flags))
    (.writeInt  idx-raf (unchecked-int gen))))

(defn tombstone-slot!
  "Mark slot `id` as a tombstone (offset=-2, other fields zeroed)."
  [^RandomAccessFile idx-raf ^long id]
  (write-slot! idx-raf id tombstone-offset 0 0 0))

(defn max-slot-id
  "The highest slot id the idx file can address, or -1 if empty.  Stable across
  deletes (a tombstone keeps its slot), so `1 + max` never reuses a handle."
  ^long [^RandomAccessFile idx-raf]
  (let [len (.length idx-raf)]
    (if (zero? len) -1 (dec (quot len slot-bytes)))))

(defn slot-count
  "The number of fixed-width slots the idx file currently holds."
  ^long [^RandomAccessFile idx-raf]
  (quot (.length idx-raf) slot-bytes))

(defn truncate!
  "Truncate a log or idx RAF to empty and reposition at the start — the whole-file
  wipe `clear-*!` needs."
  [^RandomAccessFile raf]
  (.setLength raf 0)
  (.seek raf 0))

(defn scan-idx!
  "Walk the idx from the start, invoking `(on-slot id offset length flags)` for every
  live slot (not empty, tombstone, or zero-filled gap).  Reads in 96 KiB chunks (a
  per-id `read-slot` on a large idx pays one seek each); re-seeks per chunk so an
  `on-slot` that itself seeks `idx-raf` cannot derail the scan.

  The flags ride along because this walk is the only one an open makes: whatever a slot
  can answer without reading its record has to be answered here or not at all."
  [^RandomAccessFile idx-raf on-slot]
  (let [total       (.length idx-raf)
        chunk-slots 4096
        chunk-bytes (* slot-bytes chunk-slots)
        buf         (byte-array chunk-bytes)]
    (loop [base-id 0 pos 0]
      (when (< pos total)
        (.seek idx-raf pos)
        (let [to-read (int (min chunk-bytes (- total pos)))
              n       (.read idx-raf buf 0 to-read)]
          (when (pos? n)
            (let [bb (java.nio.ByteBuffer/wrap buf 0 n)]
              (loop [i 0 off 0]
                (when (<= (+ off slot-bytes) n)
                  (let [offset (.getLong bb off)
                        length (.getLong bb (int (+ off 8)))]
                    (when (and (not= offset empty-offset)
                               (not= offset tombstone-offset)
                               (not (and (zero? offset) (zero? length))))
                      (on-slot (+ base-id i) offset length
                               (long (bit-and 0xffffffff (.getInt bb (int (+ off 16)))))))
                    (recur (inc i) (long (+ off slot-bytes)))))))
            (recur (long (+ base-id (quot n slot-bytes))) (+ pos n))))))))

(defn read-nippy-file
  "Read a whole-file nippy value, returning `default` when the file is missing,
  empty, or unreadable (a rare torn blob thaws to default + a warning rather than
  throwing — these blobs hold reconstructible metadata)."
  ([path] (read-nippy-file path nil))
  ([^String path default]
   (let [f (File. path)]
     (if (and (.exists f) (pos? (.length f)))
       (try
         (with-open [in (DataInputStream. (BufferedInputStream. (FileInputStream. f)))]
           (nippy/thaw-from-in! in))
         (catch Throwable t
           (trove/log! {:level :warn
                        :msg (str "disk.files: unreadable nippy blob " path
                                  " (" (.getMessage t) ") — falling back to default")})
           default))
       default))))

(defonce ^:private ^java.util.concurrent.atomic.AtomicBoolean dir-fsync-warned
  (java.util.concurrent.atomic.AtomicBoolean. false))

(defn- fsync-dir!
  "Best-effort fsync of the directory holding `path`, so a file's creation/deletion
  is durable.  Swallowed on filesystems that reject directory fsync — `FileChannel/open`
  on a directory is not portable.

  **Warned once**, because the swallow is not free: a commit marker's *existence* is
  the atomic commit point of a compaction, and `replay-temp-onto-raf!` truncates the
  live log before copying the temp over it.  Where the marker's directory entry never
  reaches the platter, a power loss mid-replay leaves no marker to replay from and no
  original to fall back on.  Silence makes that exposure indistinguishable from a
  filesystem where the fsync worked."
  [^String path]
  (try
    (when-let [dir (.getParentFile (File. path))]
      (with-open [ch (FileChannel/open (.toPath dir)
                                       (into-array OpenOption [StandardOpenOption/READ]))]
        (.force ch true)))
    (catch Throwable t
      (when (.compareAndSet dir-fsync-warned false true)
        (trove/log! {:level :warn :id ::dir-fsync-unsupported
                     :msg (str "this filesystem rejects directory fsync (" (.getMessage t)
                               ") — a file's creation or deletion is durable only when "
                               "the filesystem makes it so, which weakens the compaction "
                               "commit marker.  Reported once.")
                     :data {:path path}}))
      nil)))

(defn write-nippy-atomic!
  "Write a value to `path` by writing a unique temp file, fsyncing it, atomic-renaming
  over `path`, then fsyncing the parent dir — durable, not merely atomic (a power loss
  can otherwise leave the rename visible while the data blocks are still zeros).  The
  per-call unique temp suffix keeps a racing fsync tick from consuming another
  writer's temp."
  [^String path value]
  (let [tmp    (str path ".tmp." (java.util.UUID/randomUUID))
        parent (.getParentFile (File. path))]
    (when parent (.mkdirs parent))
    (try
      (with-open [fos (FileOutputStream. tmp)]
        (let [out (DataOutputStream. (BufferedOutputStream. fos))]
          (nippy/freeze-to-out! out value)
          (.flush out)
          (.sync (.getFD fos))))
      ;; Unguarded by platform, unlike `index-snapshot/rename!`, and the difference is
      ;; the target: every file written this way — the counters, the premise set, the
      ;; clean marker, the image's meta and its fallback blob — is read whole through
      ;; `read-nippy-file`, and only the image's CSR sections are ever mapped.  So no
      ;; process holds a mapping this replace has to break.
      (Files/move (Paths/get tmp (into-array String []))
                  (Paths/get path (into-array String []))
                  (into-array java.nio.file.CopyOption
                              [StandardCopyOption/ATOMIC_MOVE
                               StandardCopyOption/REPLACE_EXISTING]))
      (fsync-dir! path)
      (finally
        (.delete (File. tmp))))))

(defn- try-read-frame
  "Read a length-prefixed frame at `pos`; `[frame-end value]` on success, nil if the
  frame is truncated or corrupt."
  [^RandomAccessFile log-raf ^long pos ^long len]
  (when (<= (+ pos 4) len)
    (.seek log-raf pos)
    (let [n         (.readInt log-raf)
          frame-end (+ pos 4 n)]
      (when (and (not (neg? n)) (<= frame-end len))
        (let [bs (byte-array n)]
          (try
            (.readFully log-raf bs)
            [frame-end (thaw-bytes bs)]
            (catch Throwable _ nil)))))))

(defn log-tail-offset
  "The truncation point after a torn trailing write, computed from the frame **lengths**
  alone — read a prefix, skip `n`, repeat — without thawing anything.

  This is `scan-log`'s return value without decoding the log, and decoding is the whole
  cost: finding one offset in an 11M-record log means thawing eleven million frames whose
  values are then discarded, and it makes the open path depend on whether this build can
  decode what is in the log.  That dependency is not hypothetical — a record class rename
  turned one unreadable store into eleven million exceptions, thrown from a scan whose
  only question was *how long is the log*.

  **Nothing is thawed, deliberately, and the length chain is enough.**  A frame is
  appended before the idx slot that points at it, so a torn tail frame is one nothing
  references, and the idx is the authority on what is live.  Truncating the tail is
  therefore tidiness rather than repair, and `validate-idx-tail!` — which still runs —
  is what actually reconciles a slot against a log that lost its end.  A frame whose
  payload is damaged but whose length is intact stays, to fail (if anything references
  it at all) at that one record, which is the same one-record blast radius the token
  dictionary's own damage check settles for.  The alternative is worse in exactly the
  case that bit us: thawing to decide truncation means a build that cannot decode
  *deletes the log it cannot read*.

  A **non-positive** length terminates the walk rather than being stepped over.  A frame
  payload is a nippy value and is never empty, so a zero can only be space that was never
  written — and on a filesystem that zero-fills past a tear, stepping over zeros four
  bytes at a time would walk to EOF and pronounce the whole torn tail intact.

  The prefixes are read through a **window** rather than one `seek`+`readInt` apiece: a
  `RandomAccessFile` is unbuffered, so per-frame reads make this syscall-bound (measured
  at 5.8M frames: 5.4s that way, 23ms this way). The window is filled by *positional*
  channel reads, which name the offset and never touch the shared file pointer — so this
  neither disturbs a concurrent append nor needs the kind lock."
  ^long [^RandomAccessFile log-raf]
  (let [ch  (.getChannel log-raf)
        len (.length log-raf)
        buf (java.nio.ByteBuffer/allocate 65536)]
    ;; `base` is the file offset of buf[0] and `limit` its valid byte count; -1 = unfilled
    (loop [pos 0, base -1, limit 0]
      (cond
        (> (+ pos 4) len) pos

        ;; the next prefix is not wholly inside the window — refill from `pos`
        (or (neg? base) (< pos base) (> (+ pos 4) (+ base (long limit))))
        (let [_ (.clear buf)
              n (.read ch buf pos)]
          (if (< n 4) pos (recur pos pos n)))

        :else
        (let [n         (.getInt buf (int (- pos (long base))))   ; absolute, big-endian
              frame-end (+ pos 4 (long n))]
          (if (or (not (pos? n)) (> frame-end len))
            pos
            (recur (long frame-end) base limit)))))))

(defn scan-log
  "Scan an append-only log, calling `(f index value)` for each valid frame.  Returns
  the byte offset of the first unreadable tail byte — the truncation point after a
  torn trailing write.

  A caller that wants only that offset wants `log-tail-offset`, which reads the length
  prefixes and skips the decoding entirely."
  ^long [^RandomAccessFile log-raf f]
  (let [len (.length log-raf)]
    (loop [pos 0 idx 0]
      (if (>= pos len)
        pos
        (if-let [[frame-end v] (try-read-frame log-raf pos len)]
          (do (f idx v) (recur (long frame-end) (inc idx)))
          pos)))))

(defn truncate-log!
  "Truncate the log to `new-len` — used after `scan-log` detects a torn tail frame."
  [^RandomAccessFile log-raf ^long new-len]
  (when (< new-len (.length log-raf))
    (.setLength log-raf new-len)
    (.seek log-raf new-len)))

(defn validate-idx-tail!
  "Tombstone any of the last `window` idx slots whose frame (offset + 4 + length)
  extends past the log's current length — a torn trailing write where the idx page
  was persisted but the log pages were not.  Returns the count repaired.

  **This catches a slot that outruns the log, and only that.**  A slot is 24 bytes and a
  page is 4096, which 24 does not divide, so about 0.6% of slots straddle a page boundary
  — and a crash can persist one of those pages and not the other, leaving a slot spliced
  from two different writes.  A splice whose offset and length still land inside the log
  passes this check and surfaces later as a thaw failure on that one handle
  (`:type :malformed-record`, `vaelii.impl.disk.codec`), which is a read that refuses
  rather than a wrong record.  Detecting the splice itself would take a per-slot checksum,
  which the 24-byte slot has no room for; the `gen` word is reserved and written as 0.

  Rides `scan-idx!`'s chunked walk — the caller passes the whole idx as the window, and
  a per-id `read-slot` at that width is a seek and a buffer allocation per slot where
  the chunked read pays one per 4096."
  ^long [^RandomAccessFile idx-raf ^RandomAccessFile log-raf ^long window]
  (let [count-slots (quot (.length idx-raf) slot-bytes)
        start       (max 0 (- count-slots window))
        log-len     (.length log-raf)
        repaired    (volatile! 0)]
    (scan-idx! idx-raf (fn [id offset length _flags]
                         (when (and (>= (long id) start)
                                    (> (+ (long offset) 4 (long length)) log-len))
                           (tombstone-slot! idx-raf id)
                           (vswap! repaired inc))))
    @repaired))

;; ---- crash-safe compaction ----------------------------------------------
;; A log is rewritten (never edited in place) with only its live frames into a temp,
;; the temp is fsynced, a commit marker is fsynced, then the temp replaces the
;; original.  The marker's existence is the atomic commit point: if a crash lands
;; after it, `recover-compaction!` replays the fsynced temps; before it, the
;; originals are still authoritative and the orphan temps are dropped.

(defn compact-temp-paths
  "Sibling temp + commit-marker paths for crash-safe compaction of a (log, idx) pair.
  The marker keys off the log path, so one marker governs the pair."
  [^String log-path ^String idx-path]
  {:log-tmp (str log-path ".compact")
   :idx-tmp (str idx-path ".compact")
   :marker  (str log-path ".compact-commit")})

(defn- copy-into-channel!
  "Truncate `dst` to 0 and copy all of `src-path` into it from position 0."
  [^FileChannel dst ^String src-path]
  (with-open [in (FileInputStream. src-path)]
    (let [src   (.getChannel in)
          total (.size src)]
      (.truncate dst 0)
      (loop [pos 0]
        (when (< pos total)
          (let [n (.transferFrom dst src pos (- total pos))]
            (when (pos? n) (recur (+ pos n)))))))))

(defn replay-temp-onto-raf!
  "Install the freshly-built `tmp-path` over an already-open RAF: truncate, copy the
  temp's bytes in, fsync, leave positioned at EOF.  Used by the live compactor."
  [^RandomAccessFile target ^String tmp-path]
  (copy-into-channel! (.getChannel target) tmp-path)
  (.force (.getChannel target) true)
  (.seek target (.length target)))

(defn- replay-temp-onto-path!
  "Like `replay-temp-onto-raf!` but opens its own RAF — for recovery, before the store
  opens the file."
  [^String target-path ^String tmp-path]
  (with-open [raf (RandomAccessFile. target-path "rw")]
    (copy-into-channel! (.getChannel raf) tmp-path)
    (.force (.getChannel raf) true)))

(defn write-commit-marker!
  "Atomically create the compaction commit marker and fsync it (and its dir).  Its
  existence is the commit point."
  [^String marker info]
  (with-open [fos (FileOutputStream. marker)]
    (let [out (DataOutputStream. (BufferedOutputStream. fos))]
      (nippy/freeze-to-out! out info)
      (.flush out)
      (.sync (.getFD fos))))
  (fsync-dir! marker))

(defn delete-compact-temps!
  "Remove the commit marker then both temps (marker first, so a crash mid-cleanup
  can't leave a marker without its temps).  Idempotent."
  [^String marker ^String log-tmp ^String idx-tmp]
  (.delete (File. marker))
  (.delete (File. log-tmp))
  (.delete (File. idx-tmp))
  (fsync-dir! marker))

;; A single log with no idx (the KV write-ahead log) compacts the same way, minus the
;; idx temp.  The original log is authoritative until the temp fully replaces it, so a
;; crash before the marker keeps the original; a crash after it replays the temp.

(defn log-compact-paths
  "Temp + commit-marker paths for crash-safe compaction of a single `.log`."
  [^String log-path]
  {:tmp (str log-path ".compact") :marker (str log-path ".compact-commit")})

(defn delete-log-compact-temps!
  "Remove a single-log compaction's marker then temp (marker first).  Idempotent."
  [^String marker ^String tmp]
  (.delete (File. marker))
  (.delete (File. tmp))
  (fsync-dir! marker))

(defn recover-log-compaction!
  "Finish or discard a crash-interrupted single-log compaction, BEFORE the log opens.
  Returns :replayed, :discarded-incomplete, or :none.  Idempotent."
  [^String log-path]
  (let [{:keys [tmp marker]} (log-compact-paths log-path)
        marker? (.exists (File. ^String marker))
        tmp?    (.exists (File. ^String tmp))]
    (cond
      (and marker? tmp?)
      (do (trove/log! {:level :warn
                       :msg (str "disk.files: finishing interrupted log compaction of " log-path)})
          (replay-temp-onto-path! log-path tmp)
          (delete-log-compact-temps! marker tmp)
          :replayed)
      marker? (do (delete-log-compact-temps! marker tmp) :discarded-incomplete)
      tmp?    (do (.delete (File. ^String tmp)) :discarded-incomplete)
      :else   :none)))

(defn recover-compaction!
  "Finish or discard a crash-interrupted compaction of the (log, idx) pair, BEFORE
  they are opened for normal use.  Returns :replayed, :discarded-incomplete, or :none.
  Idempotent."
  [^String log-path ^String idx-path]
  (let [{:keys [log-tmp idx-tmp marker]} (compact-temp-paths log-path idx-path)
        marker?  (.exists (File. ^String marker))
        log-tmp? (.exists (File. ^String log-tmp))
        idx-tmp? (.exists (File. ^String idx-tmp))]
    (cond
      (and marker? log-tmp? idx-tmp?)
      (do
        (trove/log! {:level :warn
                     :msg (str "disk.files: finishing interrupted compaction of " log-path)})
        (replay-temp-onto-path! log-path log-tmp)
        (replay-temp-onto-path! idx-path idx-tmp)
        (delete-compact-temps! marker log-tmp idx-tmp)
        :replayed)

      marker?
      ;; marker present but a temp is missing — deeper damage than we can repair; keep
      ;; the originals (validate-idx-tail! handles them) and clear the partial state.
      (do
        (trove/log! {:level :error
                     :msg (str "disk.files: compaction marker for " log-path
                               " present but a .compact temp is missing — keeping originals")})
        (delete-compact-temps! marker log-tmp idx-tmp)
        :discarded-incomplete)

      (or log-tmp? idx-tmp?)
      (do (.delete (File. ^String log-tmp)) (.delete (File. ^String idx-tmp))
          :discarded-incomplete)

      :else :none)))

;; ---- unclean-shutdown marker --------------------------------------------

(defn dirty-marker-path ^String [root] (str root "/dirty.marker"))

(defn token-log-present?
  "True when `root` already holds a (non-empty) token dictionary — so a store must open
  it to decode its frames, whether or not it still writes tokenized ones."
  [root]
  (let [f (File. (str root) "tokens.log")]
    (and (.exists f) (pos? (.length f)))))

(defn dirty-marker-present?
  "True when a previous session's dirty marker survives — that session never ran a
  clean close!, so the open path should run its crash checks."
  [root]
  (.exists (File. (dirty-marker-path root))))

(defn create-dirty-marker!
  "Durably drop the dirty marker (fsync the file AND its dir)."
  [root]
  (let [p (dirty-marker-path root)]
    (with-open [fos (FileOutputStream. p)]
      (.write fos (.getBytes (str (System/currentTimeMillis)) "UTF-8"))
      (.sync (.getFD fos)))
    (fsync-dir! p)))

(defn remove-dirty-marker!
  "Remove the dirty marker after a clean fsync+close.  Idempotent."
  [root]
  (.delete (File. (dirty-marker-path root)))
  (fsync-dir! (dirty-marker-path root)))

;; ---- clean-shutdown log lengths -----------------------------------------
;; A clean close records how long each log was when it fsynced.  On the next open a log
;; whose length still matches needs no tail scan: nothing was appended after the fsync,
;; so there is no torn tail to find.
;;
;; The check is **self-validating**, which is what makes it safe to trust.  A crash
;; leaves the marker describing an earlier, shorter log, and the mismatch sends the open
;; down the full scan; so does a marker that is absent, unreadable, or claims a log
;; longer than exists.  `remove-clean-marker!` on open narrows it further, so the marker
;; exists only while nothing holds the store — a stale one cannot outlive one session.
;;
;; The lengths are a **hint and the bytes are the truth**, the same discipline the
;; counters blob follows: any disagreement resolves toward the file.

(defn clean-marker-path ^String [root] (str root "/clean.nippy"))

(defn write-clean-marker!
  "Durably record `lengths` (a `name -> log length` map) as this session's clean close.
  Call after the final fsync and before closing, so the lengths are the durable ones."
  [root lengths]
  (write-nippy-atomic! (clean-marker-path root) {:logs lengths}))

(defn read-clean-marker
  "The `name -> length` map a clean close left, or nil (absent or unreadable)."
  [root]
  (:logs (read-nippy-file (clean-marker-path root) nil)))

(defn remove-clean-marker!
  "Drop the clean marker — called on open, so it never describes a store in use."
  [root]
  (.delete (File. (clean-marker-path root)))
  (fsync-dir! (clean-marker-path root)))

(defn log-tail-offset-from
  "The truncation offset for `log-raf`, skipping the walk entirely when `clean-length`
  (this log's entry in the clean marker) equals its current length.  Returns
  `[offset scanned?]` so a caller can report whether the fast path was taken."
  [^RandomAccessFile log-raf clean-length]
  (let [len (.length log-raf)]
    (if (and (integer? clean-length) (= (long clean-length) len))
      [len false]
      [(log-tail-offset log-raf) true])))

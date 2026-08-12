;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.disk.index-snapshot
  "A **mapped snapshot** of the columnar index, which pages its cold tail to disk
  instead of holding all of it in heap.

  `:disk-columnar` keeps durable records and rebuilds the derived index on every open.
  That rebuild is O(records) — measured at 5.6 s for 313k, ~30 min at 100M — and the
  rebuilt structure is then wholly resident, which is the wall the scale plan names.
  This writes the compacted index to disk once and maps it back, so an open reads bytes
  and the fact-scaled postings live in the page cache rather than the heap.

  ## The design is a snapshot, not a store

  The index is **derived state**: `reindex` rebuilds every entry from the records.  That
  is what makes this cheap — no write-ahead log, no op log, no crash-consistent mutation
  protocol, no bucket directory.  It needs a *snapshot* that can be thrown away and
  rebuilt whenever it is in doubt, and \"in doubt\" resolves to `reindex` in every case.

  It is also why there is no directory to page.  A flat-map index keys every trie node by
  a boxed vector of its whole path prefix, so an out-of-core design over it has to page
  the keys themselves; the columnar trie has no keys at all — a node's identity is its
  `int` id and its position in the parallel arrays *is* the directory.  `columnar/compact!`
  already produces exactly the arrays this writes.

  ## What is written

  Under `<dir>/index/`, four things:

  * `trie.csr` — the trie's six CSR sections (`fcounts` `foffsets` `fedge-tok`
    `fedge-tgt` `fleaf-off` `fhandles`), each a raw little-endian `int` run behind a
    header naming the counts.
  * `roots.csr` — the *routed* root families (context/functor roots, the term, rule and
    exception indexes) as the same CSR shape over `dense-roots`' packed `long` keys:
    sorted keys, an offset column, one shared handle run.  The argument roots are not
    among them — their four-part key does not pack, so they ride the fallback blob.
  * `roots-fallback.nippy` — everything the routed families do not claim: the term and
    slot rosters (names, not handles) **and the predicate-scoped argument roots**, whose
    four-part key the packed `long` cannot carry (`dense-roots`' `route`).  The rosters
    are vocabulary-scaled; the argument roots are fact-scaled, so this blob carries
    primary index truth at fact scale, not reconstructible metadata alone — which is
    why its entry count and byte length ride the meta and are checked on open like
    the CSR sections' lengths, and why its load is strict (`read-fallback`).
  * `tokens.log` — the durable token dictionary the `int` edges cite, in
    `vaelii.impl.disk.tokens`' format (append-only, id = append position, content-keyed,
    first-writer-wins, never reused).  That module is reused rather than a second
    dictionary format minted: persisting the trie's `int` edges is precisely the seam
    `vaelii.impl.tokens` names as its durable variant.

  **One file per structure**, not one per section.  A structure is mapped or discarded as
  a unit, so per-section files would multiply the crash window by six for nothing; the
  section table in the header already names the offsets `map` needs.

  ## The residency split

  `scale-100m.md`'s rule is *never page the walk* — the worst measured index pathology was
  the leading-variable trie fan, 18,512 lookups for one query, and a disk seek is worse
  than the round trip that pathology was made of.  So the load is deliberately asymmetric:

  * **resident** — the CSR skeleton (`fcounts` `foffsets` `fedge-tok` `fedge-tgt`), the
    roots' key and offset columns, the token dictionary, and the fallback blob — which,
    with the argument roots in it, is itself fact-scaled heap on open.
  * **mapped** — `fleaf-off` / `fhandles` and the routed roots' handle run.  Each
    posting is touched only when its own term is queried.  Cold by construction.

  The argument-root family is the exception to the split: it rides the resident blob,
  not the mapped run, because its four-part key does not pack (`dense-roots`' `route`).
  A fact-scaled family resident on open is a real cost of the predicate scoping.

  With `mmap` the OS page cache is the residency policy, which is the point — but only
  because the skeleton stays hot.

  ## Validity is the whole design

  The failure to fear is a stale snapshot that passes its check: one can be perfectly
  self-consistent and describe a KB that no longer exists.  So the stamp covers the
  **records**, not the snapshot's own bytes, and it is checked on **every** open — never
  behind a flag.  Three things must agree or the snapshot is discarded and `reindex` runs:
  the format and `kv/index-layout-version`, the byte-order tag (an image whose endianness
  differs is refused rather than read wrong), and `record-store/slot-fingerprint`.  The
  decision carries a reason from `import`'s vocabulary — `:absent` `:layout-changed`
  `:records-differ` `:entries-truncated` `:unsupported-platform` — because a rebuild
  nobody can explain is a rebuild nobody notices.

  ## The platform

  The commit is an atomic rename over a file this process has mapped, which Windows does
  not permit, so `vaelii.index.snapshot` is **refused** there (`enabled?`) and an image
  found on disk is discarded as `:unsupported-platform` rather than read and never
  refreshed.  Nothing else in the `:disk` backend is implicated: the logs are appends and
  the slots are positional writes.

  A commit is one atomic step: the sections are written to temps and fsynced, the meta is
  **deleted**, the temps are renamed into place, and the meta is written last.  Its
  presence is the commit point, so a crash anywhere leaves no meta, and no meta means
  reindex.

  ## What it measured

  1.72–1.84× off the index's resident heap and a 1.5× faster open, on a corpus whose
  vocabulary is fixed — and resident heap that still grows with the facts, because the
  token dictionary is fact-scaled and the CSR skeleton is path-scaled.  The acceptance
  property it was built for does **not** hold, which is why it is off by default."
  (:require [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.impl.columnar :as col]
            [vaelii.impl.config :as config]
            [vaelii.impl.dense-roots :as roots]
            [vaelii.impl.disk.files :as f]
            [vaelii.impl.disk.tokens :as dtok]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.tokens :as tok])
  (:import [java.io File RandomAccessFile]
           [java.nio Buffer ByteBuffer ByteOrder IntBuffer LongBuffer]
           [java.nio.channels FileChannel FileChannel$MapMode]
           [java.nio.file Files Paths StandardCopyOption]
           [java.util Arrays]))

(def ^:const format-version
  "The snapshot's own layout number, beside `kv/index-layout-version` (which says what the
  *entries* mean).  Bump when a section's shape or order changes."
  1)

(def ^:private ^:const trie-magic  0x56545249)     ; "VTRI"
(def ^:private ^:const roots-magic 0x56524f54)     ; "VROT"

(def ^:private byte-order-tag
  "The byte order the sections are written in.  Recorded rather than assumed, so an image
  from a machine of the other endianness is refused instead of read as noise."
  "LITTLE_ENDIAN")

;; ---- the platform the image publishes on --------------------------------

(defn- os-name
  "The platform, as a fn so a test can name one this machine is not — asserting the
  guard by re-reading `os.name` would assert the expression it is checking."
  ^String []
  (str (System/getProperty "os.name")))

(defn- publishable-platform?
  "Can an image be *published* here?  The question is the rename, not the map: a
  read-only `FileChannel.map` works everywhere, and what Windows does not permit is
  `Files/move` with `REPLACE_EXISTING` over a target that is currently mapped — which is
  how `rename!` below commits every section.  The JVM offers no portable unmap, so there
  is no way to hold the guarantee there.

  Windows is the refused case and everything else is admitted: the evidence is one
  operating system's file-locking model, so \"not Windows\" is the honest reading of it.
  The `:disk` backend itself is untouched by this — its logs and slots are ordinary
  appends and positional writes, and refusing them here would turn a working platform
  into a refused one on the strength of an off-by-default feature."
  []
  (not (str/starts-with? (str/lower-case (os-name)) "windows")))

(defn enabled?
  "Is the mapped index snapshot on?  `vaelii.index.snapshot` — the property is the switch,
  and the *validity* check is not gated on it: a snapshot that exists is either valid or
  discarded, never trusted because a flag said so.

  On a platform that cannot publish an image, the property is **refused** rather than
  read as off: an operator who set a flag and got the default in silence is the failure
  `config` exists to close, and here the silence would be about durability of a rebuild
  they think they no longer pay for."
  []
  (let [on? (config/index-snapshot?)]
    (when (and on? (not (publishable-platform?)))
      (throw (ex-info (str "vaelii.index.snapshot is on and this is " (os-name)
                           " — the image publishes by renaming a new file over the live"
                           " one while it is mapped, which Windows does not permit."
                           "  Unset the property; :disk-columnar rebuilds its index from"
                           " the records on open.")
                      {:type :unsupported-platform :property "vaelii.index.snapshot"
                       :os (os-name)})))
    on?))

(defn snapshot-root ^String [dir] (str dir "/index"))

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

(defn- open-write ^FileChannel [^String path]
  (.getChannel (doto (RandomAccessFile. path "rw") (.setLength 0))))

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

(defn- write-roots! [^String path {:keys [keys offsets handles]}]
  (let [k (alength ^longs keys)
        h (alength ^ints handles)]
    (with-open [ch (open-write path)]
      (put-header! ch [roots-magic format-version k h])
      (put-longs! ch keys)
      (put-ints!  ch offsets (inc (long k)))
      (put-ints!  ch handles h)
      (.force ch true))
    {:keys k :handles h}))

(defn save!
  "Write a mapped snapshot of `store` (a columnar `IndexStore`) under `dir/index`, stamped
  with `(stamp-fn)`.  Returns `{:index :saved …}`, or `{:index :skipped :reason r}`.

  The stamp arrives as a thunk rather than as a record store: what an image is valid
  against is a *fingerprint of the records*, and which store computed it is none of this
  namespace's business — `record-store/slot-fingerprint` is what the disk KB passes.
  A thunk, so `load!` can decline before paying for it.

  Compacts the trie first — the CSR arrays `compact!` produces *are* the on-disk layout,
  so there is no serialization step, only a write.  An empty index saves nothing and
  drops any meta that survives, since a stale one describing a wiped KB is the one thing
  worse than none.

  **A failed save costs the new image, never the one already there.**  Every section is
  written to a `.tmp` beside its target and the meta — the commit mark — is dropped only
  once all of them are complete, so a throw anywhere before that leaves the previous
  image whole and readable.  The stamp is taken *first*, before a byte moves, because it
  is the one input that lives in another component: on the shutdown path that component
  can already be closed, and taking it late would trade a working image for none."
  [dir store stamp-fn]
  (let [root (snapshot-root dir)]
    (f/ensure-dir! root)
    (cond
      (not (col/columnar? store))
      {:index :skipped :reason :not-columnar}

      (zero? (long (p/count-at store [])))
      (do (.delete (File. (meta-path root)))
          {:index :skipped :reason :empty})

      ;; Still reading out of the image it was opened from, so the image *is* this index
      ;; and rewriting it would be pure loss: `snapshot-columns` thaws the roots to read
      ;; them, which would pull the whole cold tail back into heap at the very moment the
      ;; KB is closing.  A write would have thawed one or both halves and this is false.
      (and (col/mapped? store) (roots/mapped? (:roots store)))
      {:index :skipped :reason :unchanged}

      :else
      (let [t0    (System/nanoTime)
            stamp (stamp-fn)
            _     (col/compact! store)
            csr   (col/csr store)
            dict  (:dict store)
            rts   (:roots store)
            ;; this fn's own handle on the durable dictionary, and every step below it
            ;; can throw — a full disk mid-write, a mapped section that will not read.
            ;; It closes in a `finally`, or a failed save would leak a file handle on
            ;; exactly the directory a `close-dir!` is trying to let go of.
            tl    (dtok/open-token-log root)]
        (try
          (let [remap (durable-remap dict tl)
                etok  (remap-edges (:edge-tok csr) remap)
                etgt  (let [s (:edge-tgt csr)]                ; a copy: the sort permutes it
                        (if (instance? IntBuffer s)
                          (let [n (.limit ^IntBuffer s) a (int-array n)]
                            (.get (doto (.duplicate ^IntBuffer s) (.rewind)) a 0 n) a)
                          (aclone ^ints s)))
                _     (sort-edge-runs! (:offsets csr) etok etgt (:nodes csr))
                cols  (roots/snapshot-columns rts remap)
                tmp   #(str % ".tmp")
                tstat (write-trie!  (tmp (trie-path root))
                                    (assoc csr :edge-tok etok :edge-tgt etgt))
                rstat (write-roots! (tmp (roots-path root)) cols)
                fents (vec (roots/fallback-entries rts))]
            ;; beside its target rather than over it, so the blob the previous meta
            ;; describes stays intact until the swap below
            (f/write-nippy-atomic! (tmp (fallback-path root)) fents)
            (dtok/fsync tl true)
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
              :records      stamp
              :trie         tstat
              :roots        rstat
              ;; the blob carries the argument-root postings — primary index truth — so
              ;; its size is recorded and checked like the CSR sections'
              :fallback     {:entries (count fents)
                             :bytes   (.length (File. (fallback-path root)))}
              :tokens       (dtok/token-count tl)})
            (let [ms (/ (- (System/nanoTime) t0) 1e6)]
              (trove/log! {:level :info :id ::saved
                           :msg (format "wrote the mapped index snapshot at %s in %.0f ms (%d nodes, %d leaf handles, %d root postings)"
                                        root ms (long (:nodes tstat)) (long (:leaves tstat)) (long (:keys rstat)))})
              {:index :saved :ms ms :trie tstat :roots rstat}))
          (finally (dtok/close! tl)))))))

;; ---- reading ------------------------------------------------------------

(defn- file-len ^long [^String path] (let [f (File. path)] (if (.exists f) (.length f) -1)))

(defn- decision
  "Why this open cannot map the snapshot, or nil when it can.  Every mismatch class is its
  own reason, so the log says what changed rather than that something did.  Ordered
  cheapest-first, so the record fingerprint is only computed for an image that has already
  agreed about what it is."
  [root m stamp-fn]
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
      (not= (:records m) (stamp-fn))                 :records-differ
      (or (nil? nodes) (nil? kn))                    :entries-truncated
      (< (file-len (trie-path root))
         (+ 24 (* 4 (+ (long nodes) (inc (long nodes)) (long edges) (long edges)
                       (inc (long nodes)) (long leaves)))))
      :entries-truncated
      (< (file-len (roots-path root))
         (+ 16 (* 8 (long kn)) (* 4 (inc (long kn))) (* 4 (long hn))))
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
        (col/install-csr!
         store
         ;; resident: the skeleton the walk reads at every frontier node
         {:counts*   (read-ints ch o1 n)
          :offsets*  (read-ints ch o2 (inc n))
          :edge-tok* (read-ints ch o3 e)
          :edge-tgt* (read-ints ch o4 e)
          ;; mapped: the leaves, read once at a walk's terminus
          :leaf-off* (map-ints ch o5 (inc n))
          :handles*  (map-ints ch o6 h)})))))

(defn- load-roots! [store ^String path {kn :keys hn :handles}]
  (with-open [raf (RandomAccessFile. path "r")]
    (let [ch  (.getChannel raf)
          ^ints hdr (read-header ch 4)]
      (when-not (= roots-magic (aget hdr 0))
        (throw (ex-info (str "the roots file is not a vaelii roots snapshot — its magic number is "
                             (aget hdr 0) ", expected " roots-magic
                             "; the index will be rebuilt from the records, which are untouched")
                        {:type :bad-snapshot :part :roots :path path
                         :magic (aget hdr 0) :expected roots-magic})))
      (let [k  (long kn) h (long hn)
            o1 16
            o2 (+ o1 (* 8 k))
            o3 (+ o2 (* 4 (inc k)))]
        (roots/install-mapped! (:roots store)
                               (map-longs ch o1 k)          ; resident enough to be read
                               (map-ints  ch o2 (inc k))
                               (map-ints  ch o3 h)
                               k)))))

(defn- load-dictionary!
  "Rebuild the in-RAM dictionary from the durable log, **in id order**, so an in-RAM id is
  the durable id the mapped edges cite.  O(vocabulary) and the one per-entry cost a load
  pays — which is the design's own claim about what a snapshot's open scales with.

  The two dictionaries do not agree on equality, and this is where that would show.  The
  durable log keys a bare `HashMap` on the token, so two entries are one when
  `.equals` says so; the in-RAM one keys `tokens/Key`, which defers to `hasheq`/`equiv`
  and therefore reads `2` and `(int 2)` as one token where the log reads two.  The log
  only ever holds symbols and keywords, which the two agree about — so the counts match,
  and the **check is what makes that a fact rather than an assumption**.  A mismatch means
  the id order has shifted and every mapped edge cites the wrong entry, silently, so it
  throws into `load!`'s catch and the index is rebuilt from the records instead."
  [dict ^String root]
  (let [tl (dtok/open-token-log root)]
    (try
      (tok/clear-tokens! dict)
      ;; interned on the way in, shape preserved.  A token is often a whole compound
      ;; term — the term index is keyed by one per record — so a dictionary rebuilt
      ;; without this holds a private copy of every name in every one of them, which is
      ;; the opposite of what interning the vocabulary is for.  `intern-deep` rather than
      ;; `canon`, since a `[::subterm k]` marker and a rule's antecedent are vectors and
      ;; canonicalizing would flatten both to lists.
      (let [durable (dtok/token-count tl)]
        (dotimes [i durable]
          (tok/intern-token! dict (sx/intern-deep (dtok/token tl i))))
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
  "The fallback blob, read strictly: it carries the argument-root postings — primary
  index truth — so a torn thaw or an entry count that disagrees with the meta throws
  (into `load!`'s catch, which rebuilds) rather than defaulting to an empty value the
  index would then serve as `#{}` on every argument-root read."
  [root m]
  (let [v    (f/read-nippy-file (fallback-path root) ::torn)
        want (long (get-in m [:fallback :entries] -1))]
    (when (or (= ::torn v) (not= (count v) want))
      (throw (ex-info (str "the roots fallback blob did not thaw whole — "
                           (if (= ::torn v)
                             "unreadable"
                             (str (count v) " entries where the meta records " want))
                           " — and it holds the argument roots")
                      {:type :torn-snapshot :path (fallback-path root)
                       :entries (when-not (= ::torn v) (count v)) :expected want})))
    v))

(defn load!
  "Map `dir/index` into `store`, or say why it cannot be.  Returns `{:index :mapped …}` or
  `{:index :rebuild :reason r}` with `r` one of `:absent` `:layout-changed` `:byte-order`
  `:unsupported-platform` `:records-differ` `:entries-truncated` `:unreadable`.

  The caller reindexes on any `:rebuild` — which is always legal, because the index is
  derived state and this is a cache of it."
  [dir store stamp-fn]
  (let [root (snapshot-root dir)
        m    (f/read-nippy-file (meta-path root) nil)]
    (cond
      (not (col/columnar? store)) {:index :rebuild :reason :absent}
      (nil? m)                    {:index :rebuild :reason :absent}
      :else
      (if-let [why (decision root m stamp-fn)]
        {:index :rebuild :reason why}
        (try
          (let [t0 (System/nanoTime)]
            (p/clear-index! store)                     ; also wipes the shared dictionary
            (load-dictionary! (:dict store) root)
            (load-trie!  store (trie-path root)  (:trie m))
            (load-roots! store (roots-path root) (:roots m))
            (roots/load-fallback! (:roots store) (read-fallback root m))
            (let [ms (/ (- (System/nanoTime) t0) 1e6)]
              (trove/log! {:level :info :id ::mapped
                           :msg (format "mapped the index snapshot at %s in %.0f ms (%d tokens, %d nodes)"
                                        root ms (long (:tokens m)) (long (:nodes (:trie m))))})
              {:index :mapped :ms ms :trie (:trie m) :roots (:roots m)}))
          (catch Throwable t
            (trove/log! {:level :warn :id ::unreadable
                         :msg (str "the index snapshot at " root " did not read ("
                                   (.getMessage t) ") — rebuilding from the records")})
            (p/clear-index! store)
            {:index :rebuild :reason :unreadable}))))))

(defn discard!
  "Delete a snapshot's commit marker — what a caller does when it knows the image is dead
  and would rather the next open not have to work that out."
  [dir]
  (.delete (File. (meta-path (snapshot-root dir))))
  nil)

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.io.frames
  "The chunked **nippy stream** framing every serialization in the engine writes to a
  file or a sink — one home, so the export dump, the import reader and the snapshot sink
  cannot drift.

  A chunked stream is a run of `[int32 length][compressed chunk]`, each chunk an
  independent compression window over back-to-back nippy frames.  Constant memory on both
  sides: the writer holds one chunk and never the corpus, and the reader thaws a chunk on
  demand and drops it.  A *frame* is whatever the caller freezes — a record's field map, an
  index `[key value]` pair, a JTMS `[handle label]` pair — this namespace neither reads a
  frame nor cares what one is.

  **Why it is its own namespace and not `export`'s private helper.**  Three callers write
  and read this format — `vaelii.impl.io.export` (the dump), `vaelii.impl.io.import` (the
  reader) and `vaelii.impl.io.snapshot` (the derived-state image) — and the snapshot sink
  is meant to be *a thin adapter over this framing, not a second copy of it*.  A second
  copy is exactly the drift a shared projection was created to avoid one layer up: two
  writers that agree today and diverge on the next compression tweak.  So the framing lives
  once, here, and the container-specific concerns (a dump's `meta.edn`, an image's
  manifest, which streams exist) stay with each caller.

  The legacy single-window reader (`read-window-seq`) is kept for a v4/v5 foreign dump that
  wrote one compression window over the whole file; the engine's own dumps have been chunked
  since v6."
  (:require [clojure.java.io :as io]
            [taoensso.nippy :as nippy])
  (:import (java.io BufferedInputStream BufferedOutputStream ByteArrayInputStream
                    ByteArrayOutputStream DataInputStream DataOutputStream
                    EOFException InputStream OutputStream)
           (java.lang.reflect Constructor)
           (java.util.zip GZIPInputStream GZIPOutputStream)
           (org.tukaani.xz LZMA2Options XZOutputStream)))

;;; ── writing ───────────────────────────────────────────────────────────

(defn- wrap-output
  "The compressing wrapper for one chunk, matching the stream's `:compression`.  Each
  chunk is its own container — closing the wrapper writes the codec's trailer before
  the chunk's length is known, which is what lets a reader decompress any one chunk
  without the rest."
  ^OutputStream [^OutputStream out compression]
  (case compression
    :gzip (GZIPOutputStream. out)
    :xz   (XZOutputStream. out (LZMA2Options.))
    out))

(defn write-frames!
  "Write `frames` into `file` in the chunked layout, `chunk-size` frames per chunk.
  Returns how many frames were written.

  Lazy by construction and by contract: one chunk is realized, frozen, compressed and
  flushed before the next is asked for, so the writer's footprint is a chunk rather
  than a corpus.  `:on-chunk` is called with the running frame count at each chunk
  boundary — the progress hook, and the point a caller's callback can throw to cancel."
  [file frames {:keys [compression chunk-size on-chunk]}]
  (let [written (volatile! 0)]
    (with-open [out (io/output-stream (io/file file))
                raw (DataOutputStream. (BufferedOutputStream. out))]
      (doseq [chunk (partition-all chunk-size frames)]
        (let [baos (ByteArrayOutputStream.)]
          (with-open [cout (DataOutputStream. (wrap-output baos compression))]
            (doseq [frame chunk] (nippy/freeze-to-out! cout frame)))
          (let [^bytes bs (.toByteArray baos)]
            (.writeInt raw (alength bs))
            (.write raw bs 0 (alength bs))))
        (let [n (vswap! written + (count chunk))]
          (when on-chunk (on-chunk n)))))
    @written))

;;; ── reading ───────────────────────────────────────────────────────────

(defn- reflective-input
  "Wrap `in` in the input stream named by `class-name` via its `(InputStream)`
  constructor.  A codec here is one a dump may *arrive* in rather than one this engine writes,
  so it is resolved reflectively: the dump imports iff the library is on the classpath,
  and a clear error names the missing dep otherwise.  `:gzip` and `:none` — the export
  default and the opt-out — need no dep and never reach here; `:xz` is written too
  (`vaelii.impl.io.export`) and its library is a declared dependency, so only `:zstd`
  actually depends on what a build happens to carry."
  ^InputStream [^String class-name ^InputStream in]
  (try
    (let [k    (Class/forName class-name)
          ctor (.getConstructor k (into-array Class [InputStream]))
          ^Constructor ctor ctor]
      (cast InputStream (.newInstance ctor (object-array [in]))))
    (catch ClassNotFoundException _
      (throw (ex-info (str "compression codec not on the classpath: " class-name
                           " — add the dependency, or re-export the dump with :gzip / :none")
                      {:type :unsupported-compression :codec class-name})))))

(defn- wrap-input
  "The un-compression wrapper for a stream, matching the export's `:compression`."
  ^InputStream [^InputStream in compression]
  (case compression
    :gzip       (GZIPInputStream. in)
    (:none nil) in
    :xz         (reflective-input "org.tukaani.xz.XZInputStream" in)
    :zstd       (reflective-input "io.airlift.compress.zstd.ZstdInputStream" in)
    (throw (ex-info (str "unknown compression " compression)
                    {:type :unsupported-compression :compression compression}))))

(defn- thaw-until-eof
  "Realize every back-to-back nippy frame from `in` into a vector, stopping at EOF."
  [^DataInputStream in]
  (loop [acc (transient [])]
    (let [item (try (nippy/thaw-from-in! in) (catch EOFException _ ::eof))]
      (if (identical? ::eof item) (persistent! acc) (recur (conj! acc item))))))

(defn- thaw-chunk
  "Decompress + thaw one v6 chunk payload (`bs`) into a vector of frames."
  [^bytes bs compression]
  (with-open [in (DataInputStream.
                  (BufferedInputStream.
                   (wrap-input (ByteArrayInputStream. bs) compression)))]
    (thaw-until-eof in)))

(defn read-chunked-seq
  "Lazy seq of frames from a v6+ chunked stream file: a run of `[int32 length]
  [compressed chunk]`.  Chunks are read serially and thawed on demand, so the whole
  file never sits in heap.  The stream closes when fully consumed."
  [file compression]
  (let [^DataInputStream in (DataInputStream.
                             (BufferedInputStream. (io/input-stream (io/file file))))
        read-frame! (fn []
                      (try
                        (let [len (.readInt in)
                              bs  (byte-array len)]
                          (.readFully in bs)
                          bs)
                        (catch EOFException _ nil)))
        step (fn step []
               (lazy-seq
                (if-let [bs (read-frame!)]
                  (concat (thaw-chunk bs compression) (step))
                  (do (.close in) nil))))]
    (step)))

(defn read-window-seq
  "Lazy seq of frames from a legacy v4/v5 stream file — one compression window over
  back-to-back frames, read serially.  The stream closes when fully consumed."
  [file compression]
  (let [^DataInputStream in (DataInputStream.
                             (BufferedInputStream.
                              (wrap-input (io/input-stream (io/file file)) compression)))
        step (fn step []
               (lazy-seq
                (let [item (try (nippy/thaw-from-in! in) (catch EOFException _ ::eof))]
                  (if (identical? ::eof item)
                    (do (.close in) nil)
                    (cons item (step))))))]
    (step)))

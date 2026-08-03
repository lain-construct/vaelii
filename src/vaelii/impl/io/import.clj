;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.io.import
  "Import a vaelii **export dump** — a directory of record streams — into a pure KB,
  landing in exactly the state pure's own restart path (`reindex` / `recover`) already
  knows how to produce.

  A dump is a directory whose `meta.edn` is the marker and schema; every other file is
  a nippy stream:

      sentexes.nippy.stream        one field-map frame per sentex
      justifications.nippy.stream  one per justification
      provenance.nippy.stream      [sentex-handle map] per frame — optional

  A `:records+index` dump also carries the index, as a **cache** that is used only when
  it can be proved to describe the records that were just stored (see *the index* below);
  otherwise the index is rebuilt, and the summary says which happened and why.

  **Framing.**  A chunked stream is a run of `[int32 length][compressed chunk]`, each
  chunk a compression window over back-to-back nippy frames; a window stream is one
  compression window over the lot.  Our own dumps **state** which (`:framing`); a
  foreign dump's is inferred from its own version line.  Both are constant-memory lazy
  seqs.

  **A frame of our own dialect is a plain field map** whose `:sentence` is already
  there — but a rule's `set/*Rule` wrappers and its variable names canonicalized *into*
  the record (`:direction` / `:defeasible` / `:varmap`), so both are written back around
  it before the constructor sees it.  A frame that is *not* ours goes to a foreign
  reader (`vaelii.impl.foreign`), which is resolved at runtime and may not be in the
  build at all.  The discrimination is on the **frame**, never on `meta.edn`'s
  `:dialect`: a declaration is not an authority over the bytes beside it, and keying off
  the frame keeps a mixed dump readable.

  Whatever the dialect, **every sentence is re-canonicalized** through this build's own
  constructor (`res/kb-sentex`).  A stored canonical form is never trusted, not even
  our own: variable numbering, symmetric argument order and comparison folding belong to
  the *reading* build, and a record indexed under a key this build's `lookup` never
  reproduces would be silently unfindable.

  **Handles are preserved** for a dump of ours: every record is stored at the handle the
  dump gave it, so a handle means the same thing either side of an export.  Safe because
  the destination must be empty and because a store's counter clears any handle written
  that way (`p/next-id`) — without which the next `assert` would mint handle 1 again and
  overwrite the first imported record.  Two things can still stop a handle landing as
  given, and neither is silent: a frame with no `:id`, and a frame whose canonical form
  is one already stored, which **collapses** onto that handle (a dedup this build is
  right to perform — two engine forms can canonicalize to one pure record — and the
  dump's numbering cannot survive it).  Either makes the import `:remapped`, and then one
  `old->new` map carries the dump's ids across: justification references, and the
  `(sentexHandle H)` a meta-sentex embeds *inside stored content*, which
  `rewrite-embedded-handles!` rewrites in the sentence.

  **The index is replayed only when it can be proved to fit**, and discarding it is
  always safe — which is what makes a cache out of what would otherwise be a risk.  An
  index that does not match its records is *worse* than no index: every lookup then
  answers confidently and short, and nothing in the engine is positioned to notice.  So
  all three of these must hold (`index-decision`):

  * the entries are keyed in the layout this build reads (`kv/index-layout-version`);
  * the fingerprint accumulated **while storing** equals the one written beside the
    entries (`vaelii.impl.io.fingerprint`) — accumulated, not recomputed, since a second
    pass over the records to validate a cache would cost more than the cache saves;
  * the handles were preserved, so a posting names the record it named in the source.

  Anything else rebuilds, at `:info`, with the reason named.  A cache that silently
  stops being used is a cache nobody maintains.

  The store-facing replay is written against pure's real seams: populate the record
  store with the re-canonicalized records + justifications + premise marks, then either
  install the dumped index (`p/index-load`) or rebuild it (`reindex`), then
  `core/recover` — which rebuilds the JTMS and the taxonomy **from the records**, so a
  replayed index shortcuts the index and nothing else.  Out of scope: the `:pg-memory`
  variant."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.walk :as walk]
            [taoensso.nippy :as nippy]
            [taoensso.trove :as trove]
            [vaelii.core :as v]
            [vaelii.impl.disk.durability :as dur]
            [vaelii.impl.foreign :as foreign]
            [vaelii.impl.io.fingerprint :as fp]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reindex :as reindex]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx])
  (:import (java.io BufferedInputStream ByteArrayInputStream DataInputStream
                    EOFException InputStream)
           (java.lang.reflect Constructor)
           (java.util.zip GZIPInputStream)))

(def export-format
  "The marker `vaelii.impl.io.export` writes.  Version numbers alone cannot tell a dump
  of ours from a foreign one — ours starts at 1, which sits inside numbering somebody
  else was already using — so the dialect is named rather than deduced."
  :vaelii/export)

(def supported-export-versions
  "Export-format versions this build reads."
  #{1})

(defn- ours?
  "Is this `meta.edn` one of ours?  Governs which streams are read and how a frame's
  premise mark is decided; the *frame* still decides how a sentence is reconstructed."
  [meta]
  (= export-format (:format meta)))

(def ^:private meta-file           "meta.edn")
(def ^:private sentex-file         "sentexes.nippy.stream")
(def ^:private justification-file  "justifications.nippy.stream")
(def ^:private provenance-file     "provenance.nippy.stream")
(def ^:private index-dir           "index")
(def ^:private index-entry-file    "entries.nippy.stream")
(def ^:private index-meta-file     "index.edn")

;;; ── compression un-wrap ───────────────────────────────────────────────

(defn- reflective-input
  "Wrap `in` in the input stream named by `class-name` via its `(InputStream)`
  constructor.  A codec here is one a dump may *arrive* in rather than one pure writes,
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
    (throw (ex-info (str "unknown compression " compression) {:compression compression}))))

;;; ── stream readers ────────────────────────────────────────────────────

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

(defn- read-chunked-seq
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

(defn- read-window-seq
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

(defn- stream-reader-for
  "The reader for a dump's stream files.  One of ours **states** its framing, because a
  version number already means something else here; a foreign dump's is inferred from
  its own version line — v6+ chunked, v4/v5 single-window."
  [meta]
  (case (:framing meta)
    :chunked read-chunked-seq
    :window  read-window-seq
    (if (>= (long (:format-version meta 0)) 6) read-chunked-seq read-window-seq)))

;;; ── meta + gates ──────────────────────────────────────────────────────

(defn read-meta
  "Read a dump's `meta.edn` (the marker + schema) without loading any records."
  [dir]
  (let [^java.io.File f (io/file dir meta-file)]
    (when-not (.exists f)
      (throw (ex-info (str "no dump at " (.getPath f) " (missing meta.edn)")
                      {:type :no-dump :dir (str dir)})))
    (edn/read-string (slurp f))))

(defn- assert-supported-version!
  "Gate the version against the numbering its own dialect uses — the two overlap, so one
  set would read our v1 as an unsupported foreign v1.  A foreign dump's numbering belongs
  to its reader, so it is asked (and its absence is what refuses the dump)."
  [meta]
  (let [ours      (ours? meta)
        supported (if ours
                    supported-export-versions
                    (:versions (foreign/reader! :engine-dump)))
        vn        (:format-version meta)]
    (when-not (supported vn)
      (throw (ex-info (str (if ours "export" "foreign") " dump format version " vn
                           " is not supported by this build (supports " supported ")")
                      {:type :unsupported-version :found vn :supported supported})))))

(defn- assert-empty-destination! [kb]
  (let [n (count (p/sentex-ids (:records kb)))]
    (when (pos? n)
      (throw (ex-info (str "destination KB is not empty (" n " sentexes); import expects "
                           "a fresh KB to avoid id collisions — clear the store first")
                      {:type :not-empty :sentex-count n})))))

;;; ── frame decode ──────────────────────────────────────────────────────

(defn- our-sentence
  "The sentence for a frame **our own writer** produced, as its author wrote it — which
  is what the constructor takes, and is not quite what the frame stores.

  Two things ride beside a rule's `:sentence` rather than in it, and both have to be put
  back or they are lost silently.  The `set/*Rule` wrappers canonicalized into
  `:direction` / `:defeasible` / `:assumption` / `:constraint`, so they go back around it
  (`rules/rewrap`) — handing over the bare sentence would turn every defeasible forward
  rule into a bare bidirectional one.  And the variables were renumbered to `?var0…`,
  with `:varmap` holding the names the author used, so those go back in
  (`sentex/originalize`) — re-canonicalizing the numbered form instead would rebuild the
  rule correctly and leave it displaying as `?var0` forever.  A fact carries neither: its
  `not` is already in its sentence."
  [{:keys [sentence antecedent varmap direction defeasible assumption constraint]}]
  (if (some? antecedent)
    (-> (sx/originalize sentence varmap)
        (rules/rewrap direction defeasible assumption constraint))
    sentence))

(defn- frame-decoder
  "A `frame -> {:id :context :sentence :strength …}` decoder for this import.

  A map carrying `:sentence` is ours and is decoded here; anything else is a foreign
  dialect's and goes to its reader, resolved **once** (a `delay`, not a lookup per
  frame — this runs 11M times) and possibly not there at all, which is the honest error
  for a build that has finished with that format.

  The discrimination is on the frame rather than on `meta.edn`'s `:dialect`, so a
  declaration cannot be wrong about the bytes beside it and a mixed dump stays readable."
  []
  (let [foreign-decode (delay (:decode-frame (foreign/reader :engine-dump)))]
    (fn [frame]
      (if (and (map? frame) (contains? frame :sentence))
        (assoc frame :sentence (our-sentence frame))
        (if-let [decode @foreign-decode]
          (decode frame)
          (throw (ex-info (str "this build reads only vaelii export dumps — the frame is "
                               "not one, and no foreign reader is present "
                               "(see vaelii.impl.foreign)")
                          {:type :no-foreign-reader :kind :engine-dump})))))))

;;; ── strength ──────────────────────────────────────────────────────────

(defn- strength-class
  "Map a dump's assumption strength onto this build's two-class lattice: `:monotonic`
  survives, everything else (`:default` / `:assumption` / `:uncomputed` / nil) is
  `:default`.  Passed to a foreign replay rather than reimplemented there, so a lattice
  change lands in one place."
  [s]
  (if (= s :monotonic) :monotonic :default))

(defn- stronger [a b]
  (if (or (= a :monotonic) (= b :monotonic)) :monotonic :default))

;;; ── progress ──────────────────────────────────────────────────────────
;;
;; A dump of this size loads for minutes, so the streaming passes report how far in they
;; are.  The report is a **callback**, not a log line, because a caller driving the load
;; from a UI needs the number rather than the text — and because a callback that throws
;; is how that caller **cancels**: the throw propagates out of the pass it interrupted,
;; leaving the KB holding what had already landed (an import is not a transaction).

(defn- ticker
  "A per-frame counter that calls `on-progress` every `every` frames with
  `{:phase :done :total}`.  Returns the tick fn; `(tick!)` counts one frame."
  [on-progress phase total every]
  (let [n (volatile! 0)]
    (fn []
      (let [c (long (vswap! n inc))]
        (when (zero? (rem c (long every)))
          (on-progress {:phase phase :done c :total total}))
        c))))

(def ^:private no-progress (fn [_]))

;;; ── the record passes ─────────────────────────────────────────────────

(defn- embeds-handle?
  "Does `sentence` name another sentex by handle anywhere inside it?  An `exceptWhen`
  meta-sentex does — `(exceptWhen <query> (sentexHandle H))` — and a handle in *content*
  is a reference an id map cannot reach on its own."
  [sentence]
  (boolean (some sx/sentex-handle? (tree-seq sequential? seq sentence))))

(defn- import-sentexes!
  "Stream the sentex frames: decode each to a readable sentence, re-canonicalize through
  `res/kb-sentex`, and store it.  Two dump forms that canonicalize to one pure form
  dedup to one handle (a local `[sentence context] -> handle` map), so a dump id is never
  assumed to survive 1:1.

  For a dump of **ours** the record is stored at the handle the dump gave it rather than at
  a freshly minted one, which is what makes an id in the dump mean something.  It is safe
  because the destination is empty (`assert-empty-destination!`) and because the counter
  now clears any handle written this way (`p/next-id`).  Two things can still stop a
  handle landing as given, and both are counted rather than hidden: a frame carrying no
  `:id` has none to preserve, and a frame whose canonical form is one already stored
  **collapses** onto that handle — a dedup this build is right to perform and the dump's
  numbering cannot survive.  `:collapsed` is counted in either dialect, since it is a
  fact about the frames rather than about the policy.

  Returns `{:sx-meta {dump-id {:handle h :rule? bool :strength s}} :embedding #{handle}
  :collapsed n :minted n :fingerprint {…} :naming {…}}` — the source of the old→new id map
  and the premise decisions, plus the handles whose stored content names another sentex
  (needing a rewrite once the map is complete, unless every handle was preserved and the
  map is the identity), plus the fingerprint of what was stored and the count of what the
  front door would have refused, both accumulated **here** because this is the one pass
  over the records a reader gets.
  `:strength` is the frame's own, unnormalized: the dialects read it differently (in one
  of ours it *is* the premise mark; in a foreign dump its own account of what rests on
  what decides)."
  [kb frames decode ours? tick!]
  (let [records   (:records kb)
        seen      (volatile! {})         ; [sentence context] -> handle
        sx-meta   (volatile! {})
        embed     (volatile! #{})
        collapsed (volatile! 0)
        minted    (volatile! 0)
        naming    (volatile! nm/empty-tally)
        fprint    (fp/accumulator)]
    (doseq [frame frames]
      (tick!)
      (let [fm    (decode frame)
            _     (vswap! naming nm/tally (:sentence fm) (:context fm))
            did   (:id fm)
            ;; born carrying its strength, so the premise pass below has nothing to
            ;; re-store: a premise **is** a sentex whose `:strength` is non-nil, and
            ;; storing it strength-less and marking it after is two record writes per
            ;; premise — 1.14M of them on OpenCyc, the first dead as the second lands.
            ;; **Ours only**: in a foreign dump a frame's `:strength` is not the premise
            ;; mark — that dialect's own account of what rests on what decides, and its
            ;; reader applies it — so carrying it onto the record here would make every
            ;; imported *derivation* a premise.
            rec   (cond-> (res/kb-sentex kb (:sentence fm) (:context fm)) ; id nil
                    (and ours? (:strength fm))
                    (assoc :strength (strength-class (:strength fm))))
            k     [(:sentence rec) (:context rec)]
            h     (if-let [prior (get @seen k)]
                    (do (vswap! collapsed inc) prior)
                    (let [hh (if (and ours? did)
                               (do
                                 ;; a handle is an identity, so a second frame claiming
                                 ;; one already stored is a broken dump — and writing it
                                 ;; would destroy the first record with nothing to show
                                 ;; for it.  Equal content never reaches here; `seen`
                                 ;; has already collapsed it.
                                 (when (contains? @sx-meta did)
                                   (throw (ex-info (str "dump names handle " did " twice, "
                                                        "with different content")
                                                   {:type :duplicate-handle :handle did})))
                                 (p/put-sentex records (assoc rec :id did)))
                               (do (when ours? (vswap! minted inc))
                                   (p/put-sentex records rec)))]
                      (vswap! seen assoc k hh)
                      (fprint hh rec)                  ; only what actually got stored
                      hh))]
        (when (embeds-handle? (:sentence rec)) (vswap! embed conj h))
        (when did
          (vswap! sx-meta assoc did {:handle   h
                                     :rule?    (some? (:antecedent rec))
                                     :strength (:strength fm)}))))
    {:sx-meta @sx-meta :embedding @embed :collapsed @collapsed :minted @minted
     :fingerprint (fprint) :naming @naming}))

(defn- rewrite-embedded-handles!
  "Rewrite the `(sentexHandle <dump-id>)` terms *inside stored content* to the handles
  those records landed at.  A meta-sentex names the rule it qualifies by handle in its
  own sentence, so the id map does not reach it, and a dump id left as it stands would
  name whatever unrelated record this KB has minted at that number — an exception
  silently attached to the wrong rule.  A reference the map cannot resolve is not left
  dangling either: the meta-sentex is dropped, an exception on a rule that is not here
  being an exception on nothing.

  Only a **remapped** import runs this.  When the handles were preserved the id map is
  the identity, so the embedded number already names the record it named in the source
  and there is nothing to rewrite — which is the point of preserving them.  Returns
  `{:rewritten n :dropped n}`."
  [kb handles old->new]
  (let [records   (:records kb)
        rewritten (volatile! 0)
        dropped   (volatile! 0)]
    (doseq [h handles :let [rec (p/get-sentex records h)] :when rec]
      (let [resolved (volatile! true)
            sentence (walk/postwalk
                      (fn [x]
                        (if-let [id (sx/handle-id x)]
                          (if-let [n (get old->new id)]
                            (sx/sentex-handle n)
                            (do (vreset! resolved false) x))
                          x))
                      (:sentence rec))]
        (if @resolved
          (do (p/put-sentex records (assoc (res/kb-sentex kb sentence (:context rec))
                                           :id h :strength (:strength rec)))
              (vswap! rewritten inc))
          (do (p/delete-sentex! records h)
              (vswap! dropped inc)))))
    {:rewritten @rewritten :dropped @dropped}))

;;; ── what rests on what ────────────────────────────────────────────────
;;
;; Our own dump says this directly, which is most of what makes it ours: a justification
;; is a justification rather than something to be classified, and a premise is a sentex
;; whose `:strength` is non-nil rather than a marker record to be recognized.  A foreign
;; dialect's account is read by its own reader (`vaelii.impl.foreign`), which is handed
;; the id map and hands back the same three counts.

(defn- import-justifications!
  "Stream the `Justification` frames against the old→new id map.  Every handle a
  justification names is remapped — its consequence, its antecedents (the rule among
  them), and its informant when that is a rule handle rather than a label — and one it
  cannot resolve drops the justification rather than rebuilding it against whatever
  record now sits at that number.  The reserved `:out` slot is carried across remapped
  too, so filling it later needs nothing here.

  With `preserve?` the justification keeps its own dump handle as well.  Sentexes and
  justifications are numbered from one counter, so preserving one kind and minting the
  other would leave the minted ones colliding with the handles the other kind is holding
  — and a justification handle is what `core/justification` and the web's justification
  pages are addressed by.  Returns `{:stored n :dropped n}`."
  [kb frames old->new preserve? tick!]
  (let [records (:records kb)
        remap   (fn [id] (if (integer? id) (get old->new id) id))
        stored  (volatile! 0)
        dropped (volatile! 0)]
    (doseq [frame frames]
      (tick!)
      (let [{:keys [informant antecedents consequence bindings strength out]} frame
            conseq (get old->new consequence)
            antes  (mapv remap antecedents)
            inf    (remap informant)
            outs   (mapv remap out)]
        (if (or (nil? conseq) (nil? inf) (some nil? antes) (some nil? outs))
          (vswap! dropped inc)
          (let [jid  (or (when preserve? (:id frame)) (p/next-id records))
                just (cond-> (jtms/->just jid inf (set antes) conseq (or bindings {})
                                          (strength-class strength))
                       (seq outs) (assoc :out (set outs)))]
            (p/put-justification records just)
            (vswap! stored inc)))))
    {:stored @stored :dropped @dropped}))

(defn- mark-premises-by-strength!
  "Mark the premises of a dump of ours: a premise **is** a sentex whose `:strength` is
  non-nil — the mark rides on the record in both backends, which is why the format needs
  no premise stream.  Aggregated by handle (dedup can merge several dump ids onto one),
  keeping the strongest.  Returns the count."
  [kb sx-meta]
  (let [records   (:records kb)
        by-handle (reduce (fn [acc [_ {:keys [handle strength]}]]
                            (if strength
                              (update acc handle stronger (strength-class strength))
                              acc))
                          {} sx-meta)]
    (doseq [[handle s] by-handle]
      (p/mark-premise records handle s))
    (count by-handle)))

(defn- import-provenance-frames!
  "Replay the `provenance.nippy.stream` — `[sentex-handle map]` frames, the
  handle remapped.  Optional: a dump whose handles carry none writes no file.  Belief
  never reads provenance, so this is annotation only.  Returns the count stored."
  [kb dir compression read-fn old->new]
  (let [^java.io.File f (io/file dir provenance-file)]
    (if-not (.exists f)
      0
      (let [records (:records kb)
            n       (volatile! 0)]
        (doseq [frame (read-fn f compression)]
          (when (and (sequential? frame) (= 2 (count frame)))
            (let [[did prov] frame
                  h (get old->new did)]
              (when (and h (map? prov))
                (p/put-provenance records h prov)
                (vswap! n inc)))))
        @n))))

;;; ── the index: replay it, or rebuild it ───────────────────────────────

(defn- read-index-meta
  "`index/index.edn`, or nil when the dump has no index beside its records.  Absence is
  ordinary — a `:records` dump has none, and so does a `:records+index` export that was
  cancelled before `index.edn` was written, which is why the writer writes it last."
  [dir]
  (let [^java.io.File f (io/file dir index-dir index-meta-file)]
    (when (.exists f)
      ;; The `.exists` guard already ruled out absence, so this catch fires only on a
      ;; CORRUPT index.edn — a different fact from "there wasn't one", and the caller
      ;; turns both into the same silent full rebuild. Say which happened.
      (try (edn/read-string (slurp f))
           (catch Exception e
             (trove/log! {:level :warn :id ::index-meta-corrupt :error e
                          :msg "index.edn present but unreadable; rebuilding the index"
                          :data {:file (str f)}})
             nil)))))

(defn- index-decision
  "Whether the dumped index may be replayed, as `[:replay]` or `[:rebuild reason]`.

  Three conditions, and each one is a way the entries could describe something other
  than the records now in the store: a **layout** this build does not key its index in
  (which would read as *empty* rather than as wrong), **records** that are not the ones
  the entries were derived from, and **handles** that moved on the way in (a posting is a
  set of handles, so a remap makes every one of them name a ghost)."
  [index-meta fingerprint handles-preserved?]
  (cond
    (nil? index-meta)                                     [:rebuild :absent]
    (not= kv/index-layout-version (:index-layout index-meta)) [:rebuild :layout-changed]
    (not handles-preserved?)                              [:rebuild :handles-remapped]
    (not= (:records index-meta) fingerprint)              [:rebuild :records-differ]
    :else                                                 [:replay]))

(defn- replay-index!
  "Install the dumped entries into `kb`'s index, or report why not.  Returns nil on
  success and a rebuild reason on failure.

  Installed in bounded batches and **checked at the end** rather than realized first: an
  index dump is several entries per record, so holding one to inspect it would cost more
  heap than the records did.  A half-installed index is not left behind either way — the
  caller's fallback is `reindex`, which clears before it rebuilds — so the check is
  allowed to come after the writes, and what it has to catch is a stream that ends early
  or does not read at all.  It cannot be a checksum of the entries themselves: they are
  the thing being validated, and `index.edn` is what vouches for them."
  [kb dir compression read-fn expected]
  (let [n (volatile! 0)]
    (try
      (doseq [batch (partition-all 10000
                                   (read-fn (io/file dir index-dir index-entry-file) compression))]
        (when-not (every? #(and (sequential? %) (= 2 (count %))) batch)
          (throw (ex-info "index entry stream holds something that is not a [key value] pair"
                          {:type :malformed-entry})))
        (vswap! n + (count batch))
        (p/index-load (:index kb) batch))
      (when-not (= (long @n) (long expected))
        (trove/log! {:level :warn :id ::index-short
                     :msg (str "index entry stream holds " @n " entries, index.edn says "
                               expected)})
        :entries-truncated)
      (catch Exception e
        (trove/log! {:level :warn :id ::index-unreadable
                     :msg (str "index entry stream unreadable: " (ex-message e))})
        :entries-truncated))))

(defn- install-index!
  "Put the index in place: replay the dump's entries when they can be proved to describe
  the records just stored, else rebuild from those records.  Returns
  `{:index :replayed :entries n}` or `{:index :rebuilt :reason r}`.

  A rebuild is logged at `:info` with its reason.  Discarding the cache is always safe,
  which is what makes the fallback unremarkable — but a cache that silently stops being
  used is a cache nobody maintains, so the log line is what makes a regression visible.
  It is also what makes a failed *replay* safe to fall through: `reindex` clears the
  index before rebuilding, so whatever a broken stream managed to install is wiped."
  [kb dir compression read-fn index-meta fingerprint preserved? on-progress]
  (let [[verdict reason] (index-decision index-meta fingerprint preserved?)
        rebuild (fn [r]
                  (trove/log! {:level :info :id ::index-rebuilt
                               :msg  (str "index rebuilt rather than replayed: " (name r))
                               :data {:reason r}})
                  (on-progress {:phase :reindex :done 0 :total nil})
                  (reindex/reindex kb)                    ; clears the index itself
                  {:index :rebuilt :reason r})]
    (if (= :replay verdict)
      (do
        (on-progress {:phase :index-entries :done 0 :total (:entry-count index-meta)})
        (if-let [r (replay-index! kb dir compression read-fn (:entry-count index-meta))]
          (rebuild r)
          (do (trove/log! {:level :info :id ::index-replayed
                           :msg  (str "index replayed: " (:entry-count index-meta) " entries")})
              {:index :replayed :entries (:entry-count index-meta)})))
      (rebuild reason))))

;;; ── records-only (no belief) ──────────────────────────────────────────

(defn- bulk-load-records-only!
  "The `{:belief? false}` inline pass: for each sentex frame, re-canonicalize, store it,
  and index it **in the same pass** — indexing the record already in hand rather than
  storing everything and then re-reading it back through `reindex`, which on the `:disk`
  backend re-pages every record from disk.  Wrapped in `with-bulk-writes` so a `:memory`
  index build is one `persistent!` instead of a `swap!` per fact (a no-op on `:disk`,
  which runs its own batched WAL path).

  No dedup map / `sx-meta`: each frame is stored once, so frames map 1:1 to handles and
  each is indexed exactly once — identical to `reindex` folding over the live handles
  (the oracle in the engine-dump reader's own tests).  A dump is already deduped by its
  source and this build's ground-fact canonical form matches the stored one (the import-time
  taxonomy is empty, so symmetric arguments stay as stored and comparisons fold
  identically), so a per-frame dedup map would cost gigabytes to catch essentially
  nothing.

  Which is what lets this path preserve handles with no id map at all: with `preserve?`
  each record is stored at its dump `:id` directly, so a handle a sentence *embeds*
  (`(exceptWhen … (sentexHandle H))`) still names the record it named in the source.  A
  frame with no `:id` is minted a handle, and the count of those is what the caller
  reports — a corpus whose frames are unnumbered has no handles to preserve.

  `index?` is what decides whether the inline index build happens at all.  It is the
  fast path and the default, but a dump carrying a *replayable* index has a cheaper one
  still — installing entries beats deriving them — so the caller turns it off when a
  replay looks possible and installs afterwards.  Reports progress every `report-every`
  frames.  Returns `{:sentexes n :rules n :minted n :fingerprint {…} :naming {…}}`.

  It also **counts** what it does not check.  This path stores names `assert` refuses —
  that is what a bulk path is for — but a store the front door disagrees with is a fact
  about that store, and here, with each record already decoded and in hand, is the one
  cheap moment to learn it.  `nm/tally` is counts and classes only; the spellings behind
  them are a separate question (`vaelii.bench.survey naming`)."
  [kb frames decode preserve? index? report-every on-progress total]
  (let [records (:records kb)
        index   (:index kb)
        n       (volatile! 0)
        rules   (volatile! 0)
        minted  (volatile! 0)
        naming  (volatile! nm/empty-tally)
        fprint  (fp/accumulator)]
    (mem/with-bulk-writes (:backend index)
      (doseq [frame frames]
        (let [fm  (decode frame)
              _   (vswap! naming nm/tally (:sentence fm) (:context fm))
              rec (res/kb-sentex kb (:sentence fm) (:context fm))
              h   (if (and preserve? (:id fm))
                    (p/put-sentex records (assoc rec :id (:id fm)))
                    (do (when preserve? (vswap! minted inc))
                        (p/put-sentex records rec)))
              c   (vswap! n inc)]
          (fprint h rec)
          (if index?
            (when (reindex/index-one! index rec h) (vswap! rules inc))
            (when (rules/rule? rec) (vswap! rules inc)))
          (when (zero? (mod (long c) (long report-every)))
            (on-progress {:phase :sentexes :done c :total total})
            (trove/log! {:level :info :id ::store-progress
                         :msg (str "  loaded " c " sentexes…")})))))
    {:sentexes @n :rules @rules :minted @minted :fingerprint (fprint) :naming @naming}))

(defn- import-records-only!
  "The `{:belief? false}` path: store + index every sentex in one streaming pass, no
  justifications, no premises, no TMS — so no JTMS node or justification is created.  The
  corpus is stored and indexed (browsable by term / functor / argument / context,
  `find-sentexes`, counts, `lookup` levels 0-1) but not belief-filtered-queryable
  (`query` / `ask` read the empty TMS).  This is what lets a corpus far past what
  `recover`'s per-node relabel scales to still be loaded.

  Two of the three replay conditions are known **before** a record is stored — the layout
  the entries are keyed in, and whether this dialect's handles will be preserved — so
  this path decides upfront whether a replay is even possible.  If it is, the inline
  index build is skipped and the entries are installed afterwards; if the fingerprint
  then disagrees (a dump whose index does not match its own records) it falls back to a
  full rebuild, which is the one case that pays for the record walk twice."
  [kb dir meta compression read-fn decode preserve? report-every on-progress]
  (let [index-meta (read-index-meta dir)
        possible?  (and index-meta
                        (= kv/index-layout-version (:index-layout index-meta))
                        preserve?)
        result     (bulk-load-records-only!
                    kb (read-fn (io/file dir sentex-file) compression) decode preserve?
                    (not possible?) report-every on-progress (:sentex-count meta))
        preserved? (and preserve? (zero? (long (:minted result))))
        idx        (if possible?
                     (install-index! kb dir compression read-fn index-meta
                                     (:fingerprint result) preserved? on-progress)
                     {:index :inline})]
    (trove/log! {:level :info :id ::records-loaded
                 :msg (str "loaded " (:sentexes result) " sentexes (no belief), index "
                           (name (:index idx)))})
    ;; the other door, reported rather than enforced: a corpus the front door disagrees
    ;; with is loadable and worth loading, and the operator who chose this path is the
    ;; one who should hear the number — now, not from a failed experiment later
    (when-let [line (nm/tally-line (:naming result))]
      (trove/log! {:level :warn :id ::naming-disagreement
                   :msg  (str "this corpus and `assert` disagree: " line)
                   :data (:naming result)}))
    (merge {:variant           (:variant meta)
            :dialect           (if preserve? :pure :engine)
            :handle-policy     (if preserved? :preserved :remapped)
            :belief?           false
            :sentexes          (:sentexes result)
            :rules             (:rules result)
            :justifications        0
            :naming            (:naming result)
            :source-store-mode (:source-store-mode meta)}
           idx)))

;;; ── the entry point ───────────────────────────────────────────────────

(defn import-dump
  "Import a vaelii export dump from `dir` into the (empty) `kb` — one
  `vaelii.impl.io.export` wrote, or one in a foreign dialect this build still carries a
  reader for (`vaelii.impl.foreign`).

  With `{:belief? true}` (the default) it lands in the state pure's own restart path
  produces: the record store populated from the re-canonicalized records + the
  justifications + premise marks, the index rebuilt (`reindex`), belief recovered
  (`recover`).

  With `{:belief? false}` it stores + indexes every sentex but skips what rests on what,
  the premise marks, and `recover` — the whole corpus is browsable / findable / countable
  but not belief-queryable.  This is the path for a corpus past what `recover`'s per-node
  relabel and the in-RAM JTMS scale to (`recover` resettles a region per premise and per
  justification — millions of them would not finish).

  Reads `meta.edn` first and dispatches on it: the version is gated against its own
  dialect's numbering, the destination must be empty, and only the `:records` /
  `:records+index` variants are read.  `:pg-memory` and an unknown variant throw.

  `opts`: `{:belief? bool :report-every n :on-progress f}`.  `:on-progress` is called
  every `report-every` frames with `{:phase :done :total}` — the phases a dump has, in
  order: `:sentexes`, then (on the belief path) `:justifications` for one of ours or
  whatever phase a foreign reader reports, then either `:index-entries` (a replay) or
  `:reindex` (a rebuild).  A callback that **throws** aborts the import where it stands,
  which is how a caller cancels one; the KB is left holding what had already landed,
  since an import is not a transaction.

  The summary reports the `:dialect` read and the `:handle-policy` used —
  `:preserved` (every record is at the handle the dump gave it) or `:remapped` (with
  `:collapsed`, how many frames canonicalized onto a handle already stored) — and what
  became of the index: `{:index :replayed :entries n}` or `{:index :rebuilt :reason r}`
  (`:absent` / `:layout-changed` / `:handles-remapped` / `:records-differ` /
  `:entries-truncated`).  A caller cannot see any of it for itself, and the first two are
  load-bearing for the third: an index entry is a posting of handles, so it can only be
  replayed over a `:preserved` import.

  `:naming` is the count of what this import stored that `assert` would have refused —
  `{:checked n :refused n :by-class {…}}`, logged as a warning when it is not zero.
  Neither import path runs the naming check (both build records directly, which is what
  makes a corpus this size loadable at all), so the disagreement between the two doors is
  closed by *reporting* it: the operator who chose the bulk path learns the number while
  the records go past, rather than from a re-assertion that throws a year later."
  ([kb dir] (import-dump kb dir {}))
  ([kb dir {:keys [belief? report-every on-progress]
            :or   {belief? true report-every 500000 on-progress no-progress}}]
   (let [meta    (read-meta dir)
         variant (:variant meta :records)]
     (assert-supported-version! meta)
     (assert-empty-destination! kb)
     (when-not (#{:records :records+index} variant)
       (throw (ex-info (str "unsupported dump variant " variant
                            " — this importer reads :records / :records+index")
                       {:type :unsupported-variant :variant variant})))
     (let [compression (or (:compression meta) :none)
           read-fn     (stream-reader-for meta)
           decode      (frame-decoder)]
       ;; A bulk load accumulates index deltas monotonically, tripping the disk
       ;; durability daemon's dead-ratio compaction trigger repeatedly; each firing
       ;; rewrites the whole (growing) index under the backend lock, stalling the writer.
       ;; Pause auto-compaction for the load and let the daemon compact once afterwards
       ;; (a no-op on `:memory`, which registers no daemon).
       (dur/call-with-compaction-paused
        (fn []
          (if-not belief?
            (let [summary (import-records-only! kb dir meta compression read-fn decode
                                                (ours? meta) report-every on-progress)]
              (trove/log! {:level :info :id ::import-complete
                           :msg  (str "import-dump (records-only) complete: "
                                      (:sentexes summary) " sentexes indexed, no belief")
                           :data summary})
              summary)
            (let [ours?    (ours? meta)
                  tick     (fn [phase total] (ticker on-progress phase total report-every))
                  {:keys [sx-meta embedding collapsed minted fingerprint naming]}
                  (import-sentexes! kb (read-fn (io/file dir sentex-file) compression)
                                    decode ours? (tick :sentexes (:sentex-count meta)))
                  _ (when-let [line (nm/tally-line naming)]
                      (trove/log! {:level :warn :id ::naming-disagreement
                                   :msg  (str "this corpus and `assert` disagree: " line)
                                   :data naming}))
                  old->new (into {} (map (fn [[did m]] [did (:handle m)])) sx-meta)
                  ;; every record landed where the dump said, so the id map is the
                  ;; identity and there is nothing to remap or to rewrite
                  kept?    (and ours? (zero? (long collapsed)) (zero? (long minted)))
                  ;; before anything reads a handle out of stored content
                  rewrite  (if kept?
                             {:rewritten 0 :dropped 0}
                             (rewrite-embedded-handles! kb embedding old->new))
                  {:keys [premises provenance dropped]}
                  (if ours?
                    ;; ours says it directly: justifications are justifications, and a
                    ;; premise is a sentex carrying a strength
                    (let [{:keys [dropped]}
                          (import-justifications!
                           kb (read-fn (io/file dir justification-file) compression) old->new
                           kept? (tick :justifications (:justification-count meta)))]
                      {:premises   (mark-premises-by-strength! kb sx-meta)
                       :provenance (import-provenance-frames! kb dir compression read-fn old->new)
                       :dropped    dropped})
                    ;; a foreign dialect's account, read by its own reader
                    ((:replay-belief! (foreign/reader! :engine-dump))
                     kb {:dir dir :compression compression :read-fn read-fn :meta meta
                         :sx-meta sx-meta :old->new old->new
                         :ticker tick :strength-class strength-class}))]
              ;; put the index in place — the dump's own entries when they can be proved
              ;; to describe these records, else rebuilt from them — and then recover the
              ;; JTMS + taxonomy and settle belief.  Recovery reads the *records*, so
              ;; whichever way the index arrived it is the same restart a `:disk` KB makes.
              (let [idx (install-index! kb dir compression read-fn (read-index-meta dir)
                                        fingerprint kept? on-progress)]
                (v/recover kb)
                (let [summary (merge
                               {:variant            variant
                                :dialect            (if ours? :pure :engine)
                                :handle-policy      (if kept? :preserved :remapped)
                                :collapsed          collapsed
                                :belief?            true
                                :sentexes           (count (p/sentex-ids (:records kb)))
                                :justifications     (count (p/justification-ids (:records kb)))
                                :premises           premises
                                :provenance-entries provenance
                                :dropped-justifications dropped
                                :rewritten-handles  (:rewritten rewrite)
                                :dropped-meta-sentexes (:dropped rewrite)
                                :naming             naming
                                :source-store-mode  (:source-store-mode meta)}
                               idx)]
                  (trove/log! {:level :info :id ::import-complete
                               :msg   (str "import-dump complete: " (:sentexes summary)
                                           " sentexes, " (:justifications summary)
                                           " justifications, index " (name (:index summary)))
                               :data  summary})
                  summary))))))))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.disk.belief-snapshot
  "A **belief certificate**: the sparse complement of belief on a *clean* disk KB, written
  beside the records and read on the next cold open so `recover` can skip the one
  expensive pass of its closing settle — the definitional-clash scan
  (`settle/constraint-nogoods`).

  ## This stores a stamp, not belief

  Belief is derived, never stored: `recover` rebuilds it from the records on every open,
  and the records are the sole durable source of truth.  This does not break that.  What
  it writes is a **stamp** asserting two things about the records as they stood when it was
  written — their fingerprint (`record-store/slot-fingerprint`), and whether the KB was
  *clean*: every standing definitional clash an equal-strength tie that disbelieves neither
  side (`settle/decide-nogood`), so the scan produced no defeat.

  On a clean KB the scan is **belief-neutral** — the rest of the closing settle rederives
  the same belief without it (`settle/*skip-constraint-nogoods*`).  So a cold open whose
  records still match the stamp binds that flag and reaches identical belief for the cost
  of the structural rebuild alone: on the 11.36M-sentex corpus, the scan is the settle's
  one costly pass, minutes of it.  A KB that is **not** clean carries a
  strength-differentiated loser whose defeat cascades through what it supported, which no
  post-hoc force reproduces — so its certificate is stamped `:clean? false` and the open
  ignores it and pays the full scan.

  ## What is written

  Under `dir/belief`:
  - `meta.edn` — the stamp: `:format`, `:fingerprint`, `:clean?`, and counts.  Tiny, and
    the only file the open path reads — read and checked before anything is trusted.
  - `out.edn` — the disbelieved sentexes, content-keyed `[sentence context]`, human-readable.
    The sparse complement of belief itself; a verification and inspection artifact, not
    consulted by the fast path (the scan-skipped settle rederives the same set).
  - `notes.edn` — the standing clashes, written only when the caller supplies `:notes`
    (a `:complete` dump), for a reader that wants the dilemma records without a scan.

  ## Why it cannot go wrong

  The failure to fear is a stale stamp that passes its check.  It cannot: the stamp is a
  fingerprint of the **records**, re-read on every open, and any record added, deleted, or
  re-stored moves it (`slot-fingerprint` reads the slots, not the snapshot's own bytes).  A
  mismatch — or `:clean? false`, or an absent or torn file — falls back to the full
  recover, which is always correct because belief is derived.  Nothing here is ever the
  source of truth, so the worst a bad certificate can cost is the recover it was meant to
  save."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.pprint :as pprint]
            [taoensso.trove :as trove]
            [vaelii.impl.config :as config]
            [vaelii.impl.disk.record-store :as drs])
  (:import [java.io File]
           [java.nio.file CopyOption Files Paths StandardCopyOption]))

(def ^:const format-version
  "The certificate's own layout number.  A directory written under an older number is
  refused (the open rebuilds), so a layout change never reads wrong."
  1)

(defn- disk-records?
  "Is `records` the durable disk store — the one a certificate can be written beside?  A
  RAM record store has no directory and nothing survives its JVM, so it is a no-op here."
  [records]
  (instance? vaelii.impl.disk.record_store.DiskRecordStore records))

(defn- kb-dir
  "The KB directory a disk `records` lives in.  Its `:dir` field is `<kbdir>/records`; the
  certificate sits beside that, under `<kbdir>/belief`."
  ^String [records]
  (.getParent (File. (str (:dir records)))))

(defn- cert-dir   ^String [^String kbdir] (str kbdir "/belief"))
(defn- meta-path  ^String [^String cdir]  (str cdir "/meta.edn"))
(defn- out-path   ^String [^String cdir]  (str cdir "/out.edn"))
(defn- notes-path ^String [^String cdir]  (str cdir "/notes.edn"))

(defn- spit-atomic!
  "Write `content` to `path` via a unique temp file and an atomic rename, so a concurrent
  reader never sees a half-written file.  No parent fsync: the certificate is regenerable,
  and a crash that loses it costs the next open a full recover, never a wrong answer."
  [^String path ^String content]
  (let [tmp (str path ".tmp." (java.util.UUID/randomUUID))]
    (io/make-parents path)
    (try
      (spit tmp content)
      (Files/move (Paths/get tmp (into-array String []))
                  (Paths/get path (into-array String []))
                  (into-array CopyOption [StandardCopyOption/ATOMIC_MOVE
                                          StandardCopyOption/REPLACE_EXISTING]))
      (finally (.delete (File. tmp))))))

(defn writable?
  "May a certificate be written for `records`?  The switch is on and the store is durable.
  Read before computing the certificate so a KB with the switch off pays nothing for it."
  [records]
  (and (config/belief-snapshot?) (disk-records? records)))

(defn save!
  "Write the belief certificate for a disk KB whose disbelief the caller has already
  computed into `cert` — `{:clean? :out-count :clash-count :clash-losers :out [[sen ctx]…]}`,
  optionally `:notes`.  Stamps it with the records' current `slot-fingerprint` and writes
  `dir/belief/{meta,out}.edn` (and `notes.edn` when `:notes` is present).  A no-op unless
  `writable?`.  Returns the certificate directory, or nil."
  [records cert]
  (when (writable? records)
    (let [cdir (cert-dir (kb-dir records))
          meta {:format       format-version
                :fingerprint  (drs/slot-fingerprint records)
                :clean?       (boolean (:clean? cert))
                :out-count    (:out-count cert)
                :clash-count  (:clash-count cert)
                :clash-losers (:clash-losers cert)}]
      (spit-atomic! (meta-path cdir) (with-out-str (pprint/pprint meta)))
      (spit-atomic! (out-path cdir)  (with-out-str (pprint/pprint (vec (:out cert)))))
      (when-let [notes (:notes cert)]
        (spit-atomic! (notes-path cdir) (pr-str (vec notes))))
      (trove/log! {:level :info :id ::belief-certificate-written
                   :msg (format "wrote the belief certificate at %s (%d disbelieved, %d clashes, %d losers, clean=%s)"
                                cdir (:out-count cert) (:clash-count cert)
                                (:clash-losers cert) (boolean (:clean? cert)))})
      cdir)))

(defn read-meta
  "The parsed `meta.edn` stamp for `records`, or nil when there is none, the store is not a
  disk store, or the file does not read."
  [records]
  (when (disk-records? records)
    (let [f (io/file (meta-path (cert-dir (kb-dir records))))]
      (when (.exists f)
        (try (edn/read-string (slurp f))
             (catch Exception _ nil))))))

(defn usable?
  "May a cold open trust the certificate and skip the clash scan?  True only when the
  switch is on, the stamp reads, its `:format` is current, it certifies the KB `:clean?`,
  and its `:fingerprint` equals the records' current `slot-fingerprint`.  Every other case
  — off, no file, torn file, changed records, an unclean KB — is false, and the caller pays
  the full recover.  The switch is checked first, so an open with it off never even reads
  the records' fingerprint."
  [records]
  (boolean
   (when (config/belief-snapshot?)
     (when-let [m (read-meta records)]
       (and (= (:format m) format-version)
            (:clean? m)
            (= (:fingerprint m) (drs/slot-fingerprint records)))))))

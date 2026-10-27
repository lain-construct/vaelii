;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.browser.removed
  "The sentexes the browser last removed from each KB, so a removal can be put back.

  A retraction is the browser's one write that loses content: an assert can be retracted
  and an edit edited back, but a retracted sentence exists afterwards only in the reader's
  memory.  So every removal the browser makes is noted here once its write returns — the
  sentence as the editor prints it, its context and its strength — and the newest
  `max-kept` per KB are kept.  `/removed` lists them, and putting one back is an assert of
  what was noted.

  **Per KB, on disk.**  The list is about a KB rather than a session, it has to outlive
  the process that made the removal, and it must not be written into the KB it
  describes, so it is an EDN file per KB under `~/.vaelii/removed/` (the `vaelii.removed.dir`
  property moves it, and the test profile sets it).  A file is
  replaced whole through a rename, so a reader never sees half of one.  A KB the catalog
  never registered has no name that outlives the process, so its list is held in memory,
  one per KB.

  Only the sentexes a removal **took out** are noted.  A selected sentex that stays,
  being derived another way, was not lost, and the derived sentexes the sweep took with a
  removal come back with what they rest on."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str])
  (:import (java.io File)
           (java.nio.charset StandardCharsets)
           (java.nio.file Files StandardCopyOption)
           (java.security MessageDigest)
           (java.time Instant)
           (java.util UUID)))

(def max-kept
  "How many removals each KB's list holds; a note past it drops the oldest."
  50)

(defn- set-to [s] (when-not (str/blank? s) s))

(defn- dir ^File []
  (io/file (or (set-to (System/getProperty "vaelii.removed.dir"))
               (str (System/getProperty "user.home") "/.vaelii/removed"))))

(defn- file-for
  "The list's file for the owner string `owner`: the hex SHA-256 of its UTF-8 bytes, so
  two owners differing in any character, case included, name two files."
  ^File [^String owner]
  (let [d (.digest (MessageDigest/getInstance "SHA-256") (.getBytes owner StandardCharsets/UTF_8))]
    (io/file (dir) (str (apply str (map #(format "%02x" %) d)) ".edn"))))

;; the lists of the KBs no catalog entry holds, by KB.  Weak keys: a list lasts while the
;; KB does.  A KB is a record whose atoms compare by identity, so two KB values are equal
;; only when they are the same KB.
(defonce ^:private unfiled
  (java.util.Collections/synchronizedMap (java.util.WeakHashMap.)))

;; reads and writes of every list are one at a time: a note is a read-modify-write of the
;; file, and two removals landing together must not drop each other's entries
(defonce ^:private file-monitor (Object.))

(defn entries
  "The removals noted for `owner`, newest first: `{:id :at :sentence :context :strength
  :via}`, where `:sentence` and `:context` are text as the editor prints them.  A string
  `owner` names a list kept in a file; any other `owner` is a KB whose list is held in
  memory.  A missing or unreadable file is an empty list."
  [owner]
  (locking file-monitor
    (if-not (string? owner)
      (vec (.get ^java.util.Map unfiled owner))
      (let [f (file-for owner)]
        (if (.exists f)
          (try (vec (edn/read-string (slurp f)))
               (catch Exception _ []))
          [])))))

(defn- write-entries [owner es]
  (if-not (string? owner)
    (.put ^java.util.Map unfiled owner (vec es))
    (let [f   (file-for owner)
          tmp (io/file (.getParentFile f) (str "." (.getName f) ".tmp"))]
      (io/make-parents f)
      (binding [*print-length* nil *print-level* nil *print-meta* false]
        (spit tmp (pr-str (vec es))))
      (Files/move (.toPath tmp) (.toPath f)
                  (into-array [StandardCopyOption/REPLACE_EXISTING
                               StandardCopyOption/ATOMIC_MOVE])))))

(defn note!
  "Prepend `rows` (`{:sentence :context :strength}`, text) to `owner`'s list (`entries`),
  each given an id, the time and `via` (what removed it: `:retract`, `:edit`, `:term`),
  and keep the newest `max-kept`.  Answers the rows as noted."
  [owner via rows]
  (if (empty? rows)
    []
    (locking file-monitor
      (let [at    (str (Instant/now))
            noted (mapv #(assoc % :id (str (UUID/randomUUID)) :at at :via via) rows)]
        (write-entries owner (take max-kept (concat noted (entries owner))))
        noted))))

(defn entry
  "The noted removal `id` in `owner`'s list, or nil."
  [owner id]
  (some #(when (= id (:id %)) %) (entries owner)))

(defn forget!
  "Drop the noted removal `id` from `owner`'s list — once it has been put back."
  [owner id]
  (locking file-monitor
    (write-entries owner (remove #(= id (:id %)) (entries owner)))))

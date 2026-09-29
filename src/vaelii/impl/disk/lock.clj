;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.disk.lock
  "Single-writer guard for the on-disk KB.

  The disk record store and the disk KV index have no cross-process file locking:
  two JVMs appending to the same logs tear them.  This namespace takes an OS advisory
  `FileLock` on `<dir>/.vaelii.lock` when a disk backend opens, and fails fast if
  another live JVM already holds it.  This is the single-writer contract
  (docs/storage.md) — one process holds the KB.

  The lock is exclusive and ref-counted per canonical directory (the record store and
  the index share one dir, so both acquire and the last release drops it).  The OS
  releases it when the JVM exits, so a crash leaves no stale lock to reap.  Set
  `vaelii.disk.lock=false` (system property) to disable in a trusted single-host
  scenario."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.impl.config :as config])
  (:import [java.io File RandomAccessFile]
           [java.nio ByteBuffer]
           [java.nio.channels FileChannel FileLock OverlappingFileLockException]
           [java.nio.charset StandardCharsets]))

(def ^:private lock-file-name ".vaelii.lock")

(defonce ^:private held (atom {}))

(defn disabled?
  "Is locking switched off (`vaelii.disk.lock`)?  **Read at acquire time and nowhere
  else**, because the property can be toggled at runtime and the three operations would
  otherwise disagree about one directory: a lock taken while it was on, then read by a
  `held?` / `release!` that finds it off, is an OS lock this JVM holds for good with the
  map saying the directory is free.  So an *entry* in `held` is the stored answer — it
  exists only for a directory this JVM actually locked — and `held?` and `release!` follow
  the entry."
  [] (not (config/disk-lock?)))

(defn canonical-dir
  "`dir`'s canonical path — the identity a directory's stores are keyed by, and what
  anything else keying state off a disk KB's directory (this lock's registry, the derived
  index's shared state in `vaelii.impl.kb`) must key on too, so two spellings of one
  directory are one KB rather than two.  `vaelii.impl.disk.backend/canonical-dir` is this
  function."
  [dir]
  (.getCanonicalPath (io/file dir)))

(defn- holder-tag []
  (str (.pid (java.lang.ProcessHandle/current))
       "@" (try (.getHostName (java.net.InetAddress/getLocalHost))
                (catch Exception _ "?"))
       " since " (java.time.Instant/now)))

(defn- read-holder
  "The holder tag another JVM wrote into `f`, or nil.  The tag only annotates a refusal, so a
  read that fails is logged and the refusal goes out without it."
  [^File f]
  (try (let [s (slurp f)] (when (seq s) (str/trim s)))
       (catch Exception e
         (trove/log! {:level :debug
                      :msg (str "disk-lock could not read the holder tag in " f ": "
                                (.getMessage e))})
         nil)))

(defn- write-holder! [^FileChannel ch tag]
  (let [bytes (.getBytes (str tag "\n") StandardCharsets/UTF_8)]
    (.position ch 0)
    (.write ch (ByteBuffer/wrap bytes))
    (.truncate ch (long (alength bytes)))
    (.force ch true)))

(defn- conflict-message [path holder]
  (str "Disk KB at " path " is locked by another JVM"
       (when holder (str " (" holder ")"))
       ".  Two processes must not share one disk KB: the logs have no cross-process "
       "locking and concurrent writes would corrupt them.  Point this JVM at a "
       "different directory, or set vaelii.disk.lock=false to override."))

(defn- overlap-message [path]
  ;; `tryLock` **throws** rather than returning nil when the lock is already held by the
  ;; calling JVM, so this branch says nothing at all about another process — and the
  ;; holder tag in the file is then ours, which is why it is written from `holder-tag`
  ;; here rather than read back off disk.  Reaching it means something else in this
  ;; process has `.vaelii.lock` locked through a channel `held` does not know about: a
  ;; second classloader copy of this namespace is the usual way.
  (str "Disk KB at " path " is already locked by this JVM (" (holder-tag) ") through a "
       "channel this namespace does not hold — a second copy of vaelii.impl.disk.lock "
       "under another classloader, or other code in this process holding "
       lock-file-name " locked itself.  The OS refuses an overlapping lock inside one "
       "JVM, so no other process is involved: find the holder in this process, or set "
       "vaelii.disk.lock=false to override."))

(defn- unreleased-message [path ^Throwable cause]
  (str "Disk KB at " path " cannot be locked: this JVM (" (holder-tag) ") took its lock "
       "and the release failed (" (.getMessage cause) "), so the descriptor — and, on a "
       "failed release, the OS lock — is still held here.  Nothing can hand this "
       "directory over until the process exits, which drops both."))

(defn- nearest-existing
  "`f`, or the closest ancestor of it that exists — the file an OS refusal to create
  something under `f` is actually about."
  ^File [^File f]
  (loop [^File f (.getAbsoluteFile f)]
    (if (or (nil? f) (.exists f)) f (recur (.getParentFile f)))))

(defn- os-reason
  "The OS's own words out of a java.io open failure, whose message is `<path> (<reason>)`:
  the reason alone, since the path it names is the lock file and not the directory."
  [^Throwable e]
  (let [m (str (.getMessage e))]
    (or (second (re-find #"\(([^()]*)\)\s*$" m)) m)))

(defn- open-refusal
  "The refusal for a lock file that could not be created or opened in `dir`, naming `dir`
  (canonical, as every lock refusal names it) rather than the lock file inside it.

  Two conditions, told apart by looking at the filesystem rather than at the message:
  `dir`, or the nearest of its ancestors that exists, is a **file** (`:not-a-directory`,
  the keyword an export destination that names a file is refused under), or it is a
  directory this process cannot write (`:not-writable`)."
  [dir ^Throwable cause]
  (let [dir-s  (str dir)
        ^File blocker (nearest-existing (io/file dir-s))
        reason (os-reason cause)
        user   (System/getProperty "user.name")]
    (if (and blocker (.exists blocker) (not (.isDirectory blocker)))
      (ex-info (str "Disk KB at " dir-s " cannot be opened: "
                    (if (= (.getAbsoluteFile (io/file dir-s)) blocker)
                      (str dir-s " is a file, not a directory")
                      (str (.getPath blocker) " is a file, so no directory can be made under it"))
                    ".  Name a directory — an empty or absent one for a new KB — or move the"
                    " file.")
               {:type :not-a-directory :dir dir-s :file (.getPath blocker)}
               cause)
      (ex-info (str "Disk KB at " dir-s " cannot be opened: this process (user " user ") "
                    (if (or (nil? blocker) (= (.getAbsoluteFile (io/file dir-s)) blocker)
                            (.canWrite blocker))
                      (str "cannot create the single-writer lock file " lock-file-name
                           " there (" reason ")")
                      (str "cannot create the directory, because " (.getPath blocker)
                           ", the nearest part of the path that exists, is not writable by it"))
                    ".  Every open takes that lock, reads included, so the directory must"
                    " be writable by the process opening it.  Give " user " write access"
                    " there, or open the KB from a directory it can write.")
               {:type :not-writable :dir dir-s :user user :reason reason}
               cause))))

(defn- attempt
  "Run `(f)`, returning the exception it threw or nil."
  [f] (try (f) nil (catch Exception e e)))

(defn- give-back!
  "Release the OS lock `lk` and close `ch`, the entry `held` keeps for `path`, and drop the
  entry.  Called under `held`'s monitor, by `release!` for the last ref and by `acquire!`
  when writing the holder tag throws after the OS lock was taken.  Both steps are attempted
  and each failure is logged; on a failure the entry stays, marked `:unreleased`, for the
  reason `release!` gives."
  [path ^FileChannel ch ^FileLock lk]
  (let [rel (attempt #(.release lk))
        _   (when rel
              (trove/log! {:level :error
                           :msg (str "disk-lock could not release the lock on "
                                     path ": " (.getMessage ^Exception rel))}))
        cls (attempt #(.close ch))
        _   (when cls
              (trove/log! {:level :error
                           :msg (str "disk-lock could not close the lock file on "
                                     path ": " (.getMessage ^Exception cls))}))]
    (if-let [failed (or rel cls)]
      (do (trove/log!
           {:level :error :id ::unreleased
            :msg (str "disk-lock is keeping " path " marked held: this JVM took"
                      " its lock and could not give it back, so nothing may"
                      " reopen it until the process exits")})
          (swap! held assoc-in [path :unreleased] failed))
      (swap! held dissoc path))))

(defn acquire!
  "Acquire the single-writer lock for `dir`.  Reentrant + ref-counted per canonical
  dir.  Returns :acquired, :reentrant, or :disabled; throws `ex-info` (`:type
  :disk-locked`) when another JVM holds it, or (`:type :unreleased`) when this JVM took
  the lock and could not give it back.

  **The lock file is the first thing an open writes**, so a directory that cannot hold
  one is refused here, naming `dir`: `:not-a-directory` when it or an ancestor is
  a file, `:not-writable` when the process cannot create files in it (`open-refusal`).
  The OS answers both with a message about `.vaelii.lock`, a file the caller never named.

  **The map is consulted before the switch.**  A reentrant acquire follows the entry, not
  `vaelii.disk.lock`: a property toggled between the first acquire and this one would
  otherwise answer `:disabled` here without counting, leaving the ref count one short of
  its releases and dropping the OS lock while a holder still expects it."
  [dir]
  (let [path (canonical-dir dir)]
    (locking held
      (if-let [{:keys [unreleased]} (get @held path)]
        (if unreleased
          (throw (ex-info (unreleased-message path unreleased)
                          {:type :unreleased :dir path :holder (holder-tag)}))
          (do (swap! held update-in [path :count] inc) :reentrant))
        (if (disabled?)
          :disabled
          (let [lock-file (io/file path lock-file-name)
                ^RandomAccessFile raf
                (try (io/make-parents lock-file)
                     (RandomAccessFile. lock-file "rw")
                     (catch java.io.IOException e
                       (throw (open-refusal dir e))))
                ch        (.getChannel raf)
                lk        (try (.tryLock ch 0 Long/MAX_VALUE false)
                               (catch OverlappingFileLockException _ ::overlapping)
                               (catch Throwable t
                                 (when-let [c (attempt #(.close ch))] (.addSuppressed t c))
                                 (throw t)))]
            (cond
              (identical? ::overlapping lk)
              (do (.close ch)
                  (throw (ex-info (overlap-message path)
                                  {:type :disk-locked :dir path :holder (holder-tag)
                                   :same-jvm? true})))

              lk
              (do
                ;; The OS lock is this JVM's from here, so the entry goes in before the
                ;; holder tag is written.  A write that throws is unwound by `give-back!`,
                ;; which keeps the entry marked `:unreleased` when the release fails
                ;; rather than leave an OS lock held here that the map calls free.
                (swap! held assoc path {:channel ch :lock lk :count 1})
                (try (write-holder! ch (holder-tag))
                     (catch Throwable t
                       (give-back! path ch lk)
                       (throw t)))
                (trove/log! {:level :debug :msg (str "acquired disk lock " path)})
                :acquired)

              :else
              (let [holder (read-holder lock-file)]
                (.close ch)
                (throw (ex-info (conflict-message path holder)
                                {:type :disk-locked :dir path :holder holder}))))))))))

(defn held?
  "True when this JVM holds `dir`'s lock (or locking is disabled).  The map is read
  first: a directory locked while `vaelii.disk.lock` was on is still locked after it is
  turned off, and this answers for the OS lock rather than for the switch."
  [dir]
  (or (boolean (get @held (canonical-dir dir))) (disabled?)))

(defn release!
  "Drop one ref on `dir`'s lock; release the OS lock when the last ref goes.  No-op on a
  directory this JVM does not hold — the map is the authority, so a `vaelii.disk.lock`
  toggled off after the acquire cannot strand the OS lock here.

  **A failure to release keeps the entry.**  Both steps are attempted and both are logged,
  and if either throws the entry stays, marked with the failure: dropping it would say the
  directory is free while this JVM still holds the descriptor and, on a failed `.release`,
  the OS lock itself — so a re-`acquire!` here would take neither, hand out a directory two
  writers believe they own, and report the *previous* holder off the file, which is the
  one thing worse than refusing.  `acquire!` refuses such a directory by name (`:type
  :unreleased`) instead.  Only the process exiting drops what is still held."
  [dir]
  (let [path (canonical-dir dir)]
    (locking held
      (when-let [{:keys [channel lock count]} (get @held path)]
        (if (> count 1)
          (swap! held update-in [path :count] dec)
          (give-back! path channel lock))))))

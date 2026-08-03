;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.disk.lock
  "Single-writer guard for the on-disk KB.

  The disk record store and the disk KV index have no cross-process file locking:
  two JVMs appending to the same logs tear them.  This namespace takes an OS advisory
  `FileLock` on `<dir>/.vaelii.lock` when a disk backend opens, and fails fast if
  another live JVM already holds it.  This matches pure's single-writer contract
  (docs/storage.md) — one process holds the KB.

  The lock is exclusive and ref-counted per canonical directory (the record store and
  the index share one dir, so both acquire and the last release drops it).  The OS
  releases it when the JVM exits, so a crash leaves no stale lock to reap.  Set
  `vaelii.disk.lock=false` (system property) to disable in a trusted single-host
  scenario."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [taoensso.trove :as trove])
  (:import [java.io File RandomAccessFile]
           [java.nio ByteBuffer]
           [java.nio.channels FileChannel FileLock OverlappingFileLockException]
           [java.nio.charset StandardCharsets]))

(def ^:private lock-file-name ".vaelii.lock")

(defonce ^:private held (atom {}))

(defn disabled? [] (= "false" (some-> (System/getProperty "vaelii.disk.lock") str/trim)))

(defn- canonical [dir] (.getCanonicalPath (io/file dir)))

(defn- holder-tag []
  (str (.pid (java.lang.ProcessHandle/current))
       "@" (try (.getHostName (java.net.InetAddress/getLocalHost))
                (catch Exception _ "?"))
       " since " (java.time.Instant/now)))

(defn- read-holder [^File f]
  (try (let [s (slurp f)] (when (seq s) (str/trim s))) (catch Exception _ nil)))

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

(defn acquire!
  "Acquire the single-writer lock for `dir`.  Reentrant + ref-counted per canonical
  dir.  Returns :acquired, :reentrant, or :disabled; throws `ex-info` (`:type
  :disk-locked`) when another JVM holds it."
  [dir]
  (if (disabled?)
    :disabled
    (let [path (canonical dir)]
      (locking held
        (if (get @held path)
          (do (swap! held update-in [path :count] inc) :reentrant)
          (let [lock-file (io/file path lock-file-name)
                _         (io/make-parents lock-file)
                raf       (RandomAccessFile. lock-file "rw")
                ch        (.getChannel raf)
                ^FileLock
                lk        (try (.tryLock ch 0 Long/MAX_VALUE false)
                               (catch OverlappingFileLockException _ nil)
                               (catch Throwable t (.close ch) (throw t)))]
            (if lk
              (do
                ;; write-holder! can throw after the OS lock is taken; release before
                ;; rethrowing or the lock leaks untracked for the JVM lifetime.
                (try (write-holder! ch (holder-tag))
                     (catch Throwable t
                       (try (.release lk) (catch Throwable _))
                       (try (.close ch)   (catch Throwable _))
                       (throw t)))
                (swap! held assoc path {:channel ch :lock lk :count 1})
                (trove/log! {:level :debug :msg (str "acquired disk lock " path)})
                :acquired)
              (let [holder (read-holder lock-file)]
                (.close ch)
                (throw (ex-info (conflict-message path holder)
                                {:type :disk-locked :dir path :holder holder}))))))))))

(defn held?
  "True when this JVM holds `dir`'s lock (or locking is disabled)."
  [dir]
  (or (disabled?) (boolean (get @held (canonical dir)))))

(defn release!
  "Drop one ref on `dir`'s lock; release the OS lock when the last ref goes.  No-op
  when disabled or not held by this JVM."
  [dir]
  (when-not (disabled?)
    (let [path (canonical dir)]
      (locking held
        (when-let [{:keys [^FileChannel channel ^FileLock lock count]} (get @held path)]
          (if (> count 1)
            (swap! held update-in [path :count] dec)
            (do (try (.release lock)  (catch Exception _))
                (try (.close channel) (catch Exception _))
                (swap! held dissoc path))))))))

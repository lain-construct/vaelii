;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.disk.tokens
  "A **durable** token dictionary for a disk store: `symbol/keyword ↔ int`, append-only,
  ids assigned in append order and never reused.  It is what lets a record frame spell
  its sentence as ids rather than names (`vaelii.impl.disk.codec`), which is 2.6× smaller
  than the positional frame it replaces — the vocabulary is written once here instead of
  once per frame in all 100M of them.

  **The ordering that makes it safe.**  A frame referencing an id the dictionary cannot
  decode is unreadable data, so the dictionary must never lag the records that cite it.
  Two rules give that, and neither costs a write:

  - a token is appended **before** the record frame citing it (`emit!` interns as it
    encodes, which happens before the frame is written), so the token log leads the
    record log in *write* order at all times;
  - `fsync` fsyncs this log **first, holding the sentexes kind lock**, so nothing is
    appended between the two fsyncs.  Every record durable after a tick therefore has
    its tokens durable too.

  fsyncing *per new token* would also give the ordering, and is what this did first —
  but it makes a cold load fsync-bound (measured: ~217 records/s, since a new token is
  not rare during one).  Between ticks the two logs can still skew on a machine crash,
  exactly as the record log and its idx can; `open-record-store` repairs it the same way
  it repairs those, by tombstoning a record whose ids the dictionary does not hold.

  **Only symbols and keywords are interned.**  Those are bounded by the ontology.
  Numbers and strings are not — a KB of measurements would mint a dictionary entry per
  distinct value — so `codec` carries them beside the id stream as literals instead.

  Ids are **content-keyed and first-writer-wins**, so they are stable for the life of the
  store; the id *value* depends on first-encounter order, which nothing above this reads.
  Tokens are never deleted (an id must keep decoding), so the log has no dead frames and
  needs no compaction; only a whole-store `clear-records!` empties it.

  Writes take the log's lock (there is one writer, and the append must not interleave);
  the *reverse* map is an atom holding a vector, so a decode — which runs on every fetch,
  under a different lock — reads it without one and still sees a safely published entry."
  (:require [vaelii.impl.disk.files :as f]
            [vaelii.impl.sentex :as sx])
  (:import [java.util HashMap]))

(defrecord TokenLog [log path fwd rev lock])

(defn open-token-log
  "Open `dir/tokens.log` and rebuild the in-memory maps from it: frame *i* holds the
  token with id *i*.  A torn trailing frame is truncated exactly as a record log's is —
  the token it held was never handed out, because the append is fsynced before the id
  is returned."
  [dir]
  (let [path (str dir "/tokens.log")
        log  (f/open-log path)
        fwd  (HashMap.)
        rev  (volatile! (transient []))]
    (f/truncate-log! log (f/log-tail-offset log))
    ;; a reloaded token is pooled, so every record decoded through the dictionary shares
    ;; the one vocabulary object per name with the in-memory store — as it did before the
    ;; restart, when the token came from a canonicalized sentence
    (f/scan-log log (fn [_ tok]
                      (let [tok (sx/intern-sym tok)]
                        (.put fwd tok (Integer/valueOf (count @rev)))
                        (vswap! rev conj! tok))))
    (->TokenLog log path fwd (atom (persistent! @rev)) (Object.))))

(defn intern!
  "The id for `tok`, allocating (and durably recording) a fresh one if it is new."
  ^long [{:keys [^HashMap fwd rev lock log]} tok]
  (locking lock
    (if-let [id (.get fwd tok)]
      (long id)
      (let [id (count @rev)]
        (f/append-record! log tok)    ; written before the frame that cites it; `fsynh!` orders the fsyncs
        (.put fwd tok (Integer/valueOf id))
        (swap! rev conj tok)
        (long id)))))

(defn token
  "The token id `id` decodes to.  An id outside the dictionary means a frame referencing
  a token the dictionary never recorded — unreadable data rather than a nil field, so it
  throws instead of decoding to something plausible."
  [{:keys [rev]} ^long id]
  (let [v @rev]
    (if (< -1 id (count v))
      (nth v id)
      (throw (ex-info "token id is not in the dictionary — the frame or the dictionary is damaged"
                      {:id id :dictionary-size (count v)})))))

(defn token-count ^long [{:keys [rev]}] (count @rev))

(defn clear!
  "Empty the dictionary and its log — only for a whole-store wipe, since it invalidates
  every id any surviving frame holds."
  [{:keys [^HashMap fwd rev lock log]}]
  (locking lock
    (f/truncate! log)
    (.clear fwd)
    (reset! rev [])
    nil))

(defn fsync [{:keys [log lock]} fsync?]
  (when fsync? (locking lock (f/force! log false))))

(defn close! [{:keys [log lock]}] (locking lock (f/close! log)))

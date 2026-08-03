;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.overlay.store
  "`OverlayRecordStore` — a composite `RecordStore` layering a private **writable**
  overlay over a shared **read-only** base.  Reads resolve overlay-first, skipping
  tombstoned base handles; writes land only in the overlay; the base is never mutated.
  The record half of the `:overlay` backend (the index half is
  `vaelii.impl.overlay.kv`).

  * **The id seam.**  The overlay's handle counter is seeded above every handle the base
    holds, so a newly minted handle can never collide with a base one.  A record written
    at a handle the base *already* uses is therefore an **override** — the same handle,
    a different record — and the overlay's copy wins every read.  That is how a base
    record is edited without editing the base: `mark-premise` materializes an override
    before it writes, since the assumption strength lives on the record.
  * **Tombstones.**  Deleting a base handle cannot touch the base, so it is recorded and
    the read path filters it.  They are sticky: a base record cannot come back through
    fall-through, only by being written again into the overlay (a revival, at the same
    handle).
  * **Wholesale clear.**  `clear-records!` empties the overlay and marks the base
    hidden — one flag rather than a tombstone per base handle — so a fork can be reset
    to empty without walking what it inherited.
  * **Durable bookkeeping.**  The tombstone sets, the released premise marks and the
    hidden flag live in a small `KvBackend` under reserved keys, mirrored in atoms for
    the read path.  Every mutation writes through, and a mount rebuilds the atoms from
    it, so remounting a durable overlay over the same base serves the same merged view:
    a deleted base record stays deleted, a released premise stays released.  An
    ephemeral fork passes an in-RAM bookkeeping backend and pays nothing for the
    machinery.

  **Counts need no delta bookkeeping here.**  A `RecordStore` in pure exposes handle
  *sets* rather than counts, and everything counted — `sentex-count`, `context-size`,
  `count-with-functor` — is read off the index, where the merge is the trie's own
  copy-on-write counters and the merged root sets (`vaelii.impl.overlay.kv`).  So the
  counts a fork reports are exact by construction rather than by a second, parallel
  accounting that could drift from the records.

  **The fork's belief is rebuilt, not overlaid.**  The JTMS is not storage — it is a
  separate protocol (`vaelii.impl.jtms`) over derived state — and pure already has the
  operation that computes it from records: `recover`.  So a fork gets its own network by
  recovering over the merged view, and nothing here layers one truth-maintenance graph
  over another."
  (:require [clojure.set :as set]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.protocols :as p]))

;; ---- reserved bookkeeping keys --------------------------------------------

(def ^:private cleared-key      ::cleared)
(def ^:private sx-tombstone-key ::sentex-tombstoned)
(def ^:private jd-tombstone-key ::justification-tombstoned)
(def ^:private pv-tombstone-key ::provenance-tombstoned)
(def ^:private released-key     ::premise-released)

;; ---- the fast view + its write-through --------------------------------------
;; Each atom is a mirror of one bookkeeping key; every mutation writes both, and a mount
;; reads the atoms back out of the backend.  The atoms are what the read path touches, so
;; a durable bookkeeping backend costs the reads nothing.

(defn- note! [a meta-kv k id]
  (swap! a conj id)
  (kv/kv-add-to-set meta-kv k id))

(defn- unnote! [a meta-kv k id]
  (swap! a disj id)
  (kv/kv-remove-from-set meta-kv k id))

(defrecord OverlayRecordStore
           [overlay base meta-kv base-highest counter
            hidden? sx-tombstoned jd-tombstoned pv-tombstoned released]

  p/RecordStore
  ;; strictly above every handle the base holds, so a minted handle is never a base one
  ;; and a handle at or below the watermark is unambiguously an override
  (next-id [_] (long (swap! counter inc)))

  (put-sentex [this sentex]
    (let [id (long (or (:id sentex) (p/next-id this)))]
      ;; an explicit handle (an import, a revival) must carry the counter with it, or the
      ;; next mint would reissue it and overwrite a record with no error
      (swap! counter max id)
      (when (contains? @sx-tombstoned id) (unnote! sx-tombstoned meta-kv sx-tombstone-key id))
      (p/put-sentex overlay (assoc sentex :id id))))

  (get-sentex [_ id]
    (or (p/get-sentex overlay id)
        (when-not (or @hidden? (contains? @sx-tombstoned (long id)))
          (p/get-sentex base id))))

  (delete-sentex! [_ id]
    (let [id (long id)]
      (when (p/get-sentex overlay id) (p/delete-sentex! overlay id))
      (when-not @hidden?
        (when (p/get-sentex base id)
          (note! sx-tombstoned meta-kv sx-tombstone-key id)
          ;; the premise mark needs no separate release: `premise-ids` subtracts the
          ;; tombstoned handles, so a deleted base premise is already gone from it
          (when (p/get-provenance base id)      ; provenance dies with its record
            (note! pv-tombstoned meta-kv pv-tombstone-key id)))))
    nil)

  (put-justification [this justification]
    (let [id (long (or (:id justification) (p/next-id this)))]
      (swap! counter max id)
      (when (contains? @jd-tombstoned id) (unnote! jd-tombstoned meta-kv jd-tombstone-key id))
      (p/put-justification overlay (assoc justification :id id))))

  (get-justification [_ id]
    (or (p/get-justification overlay id)
        (when-not (or @hidden? (contains? @jd-tombstoned (long id)))
          (p/get-justification base id))))

  (delete-justification! [_ id]
    (let [id (long id)]
      (when (p/get-justification overlay id) (p/delete-justification! overlay id))
      (when-not @hidden?
        (when (p/get-justification base id) (note! jd-tombstoned meta-kv jd-tombstone-key id))
        (when (p/get-provenance base id) (note! pv-tombstoned meta-kv pv-tombstone-key id))))
    nil)

  (put-provenance [_ id prov]
    (when (contains? @pv-tombstoned (long id)) (unnote! pv-tombstoned meta-kv pv-tombstone-key id))
    (p/put-provenance overlay id prov))

  (get-provenance [_ id]
    (or (p/get-provenance overlay id)
        (when-not (or @hidden? (contains? @pv-tombstoned (long id)))
          (p/get-provenance base id))))

  (delete-provenance! [_ id]
    (let [id (long id)]
      (p/delete-provenance! overlay id)
      (when (and (not @hidden?) (p/get-provenance base id))
        (note! pv-tombstoned meta-kv pv-tombstone-key id)))
    nil)

  ;; an override lives in both halves, so the union dedups it to the one handle it is
  (sentex-ids [_]
    (let [own (p/sentex-ids overlay)]
      (if @hidden?
        own
        (set/difference (into (set (p/sentex-ids base)) own) @sx-tombstoned))))

  (justification-ids [_]
    (let [own (p/justification-ids overlay)]
      (if @hidden?
        own
        (set/difference (into (set (p/justification-ids base)) own) @jd-tombstoned))))

  ;; The strength is a field on the sentex record, so marking a base premise means
  ;; **writing** a base record — which is what an override is for.  Materialize the copy
  ;; first, then mark it in the overlay like any other handle.
  (mark-premise [this id strength]
    (let [id (long id)]
      (when-not (p/get-sentex overlay id)
        (when-let [sx (p/get-sentex this id)]
          (p/put-sentex overlay (assoc sx :id id))))
      (p/mark-premise overlay id strength)
      ;; guarded, so the ordinary assert writes nothing to the bookkeeping backend — the
      ;; release set is only ever consulted for a handle that is in it
      (when (contains? @released id) (unnote! released meta-kv released-key id)))
    nil)

  (unmark-premise! [this id]
    (let [id (long id)]
      (when-not (p/get-sentex overlay id)
        (when-let [sx (p/get-sentex this id)]
          (p/put-sentex overlay (assoc sx :id id))))
      (p/unmark-premise! overlay id)
      ;; The base's own mark cannot be removed, so it is released instead.  Whether the
      ;; base holds one is read off the record's `:strength`, which is what a premise mark
      ;; *is* on both record stores — `mark-premise` writes it there, and the disk store's
      ;; recovery rebuilds its whole premise set from it.
      (when (and (not @hidden?) (:strength (p/get-sentex base id)))
        (note! released meta-kv released-key id)))
    nil)

  (premise-ids [_]
    (let [own (p/premise-ids overlay)]
      (if @hidden?
        own
        ;; a tombstoned handle is not a premise: the record it marked is gone
        (set/difference (into (set (p/premise-ids base)) own) @released @sx-tombstoned))))

  (premise-strength [_ id]
    (cond
      (p/get-sentex overlay id) (p/premise-strength overlay id)
      (and (not @hidden?)
           (not (contains? @sx-tombstoned (long id)))
           (p/get-sentex base id)) (p/premise-strength base id)
      :else :default))

  ;; O(1) rather than a tombstone per inherited handle: the flag hides the base
  ;; wholesale, and the bookkeeping is wiped with it (nothing is left to shadow).
  ;;
  ;; The handle counter restarts from 1, as both concrete stores' does — a cleared store
  ;; is a fresh one, and a handle allocation that depended on what the store *used* to
  ;; hold would make handles a function of history rather than of content.  Safe here
  ;; because the flag is sticky: no base handle is reachable again, so reissuing one
  ;; collides with nothing, and a remount takes the `max` over both watermarks so
  ;; anything minted after it stays above the base's range regardless.
  (clear-records! [_]
    (p/clear-records! overlay)
    (kv/kv-clear! meta-kv)
    (kv/kv-put meta-kv cleared-key true)
    (reset! counter 0)
    (reset! hidden? true)
    (reset! sx-tombstoned #{})
    (reset! jd-tombstoned #{})
    (reset! pv-tombstoned #{})
    (reset! released #{})
    nil))

(defn overlay-record-store
  "Compose a writable `overlay` `RecordStore` over a read-only `base` one, with `meta-kv`
  holding the overlay's record-level bookkeeping.

  The mount reads the bookkeeping back — so a durable overlay remounted over the same
  base serves the merged view it was left in — and seeds the handle counter above both
  stores' watermarks, which is what keeps a minted handle out of the base's range even
  after a restart."
  [overlay base meta-kv]
  (let [base-next (long (p/next-id base))          ; allocation, not mutation (see `frozen`)
        own-next  (long (p/next-id overlay))]
    (map->OverlayRecordStore
     {:overlay        overlay
      :base           base
      :meta-kv        meta-kv
      :base-highest   (dec base-next)
      :counter        (atom (max base-next own-next))
      :hidden?        (atom (some? (kv/kv-get meta-kv cleared-key)))
      :sx-tombstoned  (atom (set (kv/kv-members meta-kv sx-tombstone-key)))
      :jd-tombstoned  (atom (set (kv/kv-members meta-kv jd-tombstone-key)))
      :pv-tombstoned  (atom (set (kv/kv-members meta-kv pv-tombstone-key)))
      :released       (atom (set (kv/kv-members meta-kv released-key)))})))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.overlay.frozen
  "The read-only mount: a `KvBackend` and a `RecordStore` that answer every read and
  **refuse every write**.

  A base shared by N forks is only shared if nothing can write it, and the honest way to
  guarantee that is structurally rather than by review: an overlay composes over one of
  these, so a write path that forgot to divert fails loudly at the seam instead of
  silently mutating what every other fork is reading.  That is invariant 1 of
  docs/overlay.md, held by construction.

  Two calls are deliberately *not* refusals.

  * `next-id` on the frozen record store.  It hands out a handle nobody holds and
    touches no stored record, and it is what the overlay's id watermark is seeded from
    (`vaelii.impl.overlay.store`) — the alternative, a `max` over the base's whole live-id
    set, is O(base) at every mount.  Two JVMs mounting one base each bump their own
    in-RAM counter to the same value and then diverge into their own overlays, which is
    exactly what independent forks are.
  * `kv-entries` / `sentex-ids` and friends.  Enumeration is a read.

  This is a decorator, not a file mode: it says nothing about how the underlying store
  was opened.  Opening the base's files read-only at the OS level is the disk backend's
  business and orthogonal — this is what makes the *composition* safe whatever the base
  is (memory, disk, or a later SQL store)."
  (:require [vaelii.impl.kv :as kv]
            [vaelii.impl.protocols :as p]))

(defn- refuse [op]
  (throw (ex-info (str "the overlay's base is mounted read-only — " op " is refused")
                  {:type :frozen-base :op op})))

;; ---- the index half --------------------------------------------------------

(defrecord FrozenKv [base]
  kv/KvBackend
  (kv-get       [_ k]   (kv/kv-get base k))
  (kv-members   [_ k]   (kv/kv-members base k))
  (kv-member?   [_ k m] (kv/kv-member? base k m))
  (kv-count     [_ k]   (kv/kv-count base k))
  (kv-intersect [_ ks]  (kv/kv-intersect base ks))
  (kv-entries   [_]     (kv/kv-entries base))

  (kv-put             [_ _ _] (refuse "kv-put"))
  (kv-delete          [_ _]   (refuse "kv-delete"))
  (kv-increment       [_ _]   (refuse "kv-increment"))
  (kv-decrement       [_ _]   (refuse "kv-decrement"))
  (kv-add-to-set      [_ _ _] (refuse "kv-add-to-set"))
  (kv-remove-from-set [_ _ _] (refuse "kv-remove-from-set"))
  (kv-batch           [_ _]   (refuse "kv-batch"))
  (kv-load            [_ _]   (refuse "kv-load"))
  (kv-clear!          [_]     (refuse "kv-clear!")))

(defn frozen-kv
  "`base` as a read-only `KvBackend`."
  [base]
  (if (instance? FrozenKv base) base (->FrozenKv base)))

;; ---- the record half -------------------------------------------------------

(defrecord FrozenRecords [base]
  p/RecordStore
  (get-sentex        [_ id] (p/get-sentex        base id))
  (get-justification [_ id] (p/get-justification base id))
  (get-provenance    [_ id] (p/get-provenance    base id))
  (sentex-ids        [_]    (p/sentex-ids        base))
  (justification-ids [_]    (p/justification-ids base))
  (premise-ids       [_]    (p/premise-ids       base))
  (premise-strength  [_ id] (p/premise-strength  base id))
  ;; allocation, not mutation — see the namespace docstring
  (next-id           [_]    (p/next-id base))

  (put-sentex           [_ _]   (refuse "put-sentex"))
  (delete-sentex!       [_ _]   (refuse "delete-sentex!"))
  (put-justification    [_ _]   (refuse "put-justification"))
  (delete-justification! [_ _]  (refuse "delete-justification!"))
  (put-provenance       [_ _ _] (refuse "put-provenance"))
  (delete-provenance!   [_ _]   (refuse "delete-provenance!"))
  (mark-premise         [_ _ _] (refuse "mark-premise"))
  (unmark-premise!      [_ _]   (refuse "unmark-premise!"))
  (clear-records!       [_]     (refuse "clear-records!")))

(defn frozen-records
  "`base` as a read-only `RecordStore`."
  [base]
  (if (instance? FrozenRecords base) base (->FrozenRecords base)))

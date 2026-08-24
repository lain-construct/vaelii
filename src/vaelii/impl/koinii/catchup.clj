;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.koinii.catchup
  "Koinii catch-up: make 'an agent that was offline catches up on what it
  missed' CORRECT, including the case the naive version gets wrong — the feed's ring is
  bounded (256 events), so an agent gone long enough is lagged PAST recovery and its stored
  cursor can no longer replay the gap.

  This is exactly the **CDC snapshot+tail** pattern (Debezium / Kafka): a consumer that
  joined late — or fell too far behind — re-reads current state (the **snapshot**), then
  resumes streaming from the newest offset (the **tail**).  Koinii's context re-read IS the
  snapshot half.  The subscribe loop (the `channel`) handles the happy path; this handles
  the gap.  Commits `koinii.md`'s D6 (snapshot+tail) and D7 (order).

  **Why the snapshot is authoritative, not a fallback nicety.**  The change feed is
  add-oriented: it reports a datum ENTERING or a derived conclusion LEAVING belief, but a
  premise RETRACTED is dropped — its record is gone and 'a datum the dependency-directed
  sweep deleted is dropped rather than guessed at' (docs/feed.md).  So the incremental
  stream cannot, by itself, be a complete replica: only a full re-read reflects retractions.
  The tail is an optimization for the common case (koinii accretes — claims, replies,
  votes); the snapshot is the source of truth, and every catch-up path ends reconciled
  against it or against a live tail.

  **Snapshot reads through the CONE.**  A channel sees its agents' own-context sentexes up
  the `genlCx` cone; `sentexes-matching` does NOT walk the cone (it scopes to a context's
  own sentexes) but `query` does — so the snapshot is `channel/query`, whose solution set is
  the same view the standing-query feed delivers.

  Wire-only: the ring, the cursor, and lag exist on the wire feed (`vaelii.impl.subscribe`).
  An in-process medium has no ring to fall off, so `-feed-open`/`-feed-poll` throw there and
  a single-process agent needs none of this.

  Additive: requires only `channel` and `clojure.walk`.  Nothing in core loads it."
  (:require [clojure.walk :as walk]
            [vaelii.impl.koinii.channel :as ch]))

;; ---- D6/D7: the client-side durable cursor -------------------------------

(defprotocol CursorStore
  "Where an agent keeps 'the last feed position I processed' — `{:token :cursor}` — so a
  restart RESUMES the stream rather than re-reading everything.  Deliberately CLIENT-SIDE
  (D7): a cursor in a KB context would be self-describing but would write to the shared
  truth on every poll, turning a read loop into a write loop through the single writer.  A
  deployment backs this with a file, the agent's own store, or a row — anything durable and
  local; the atom store below is the in-memory default."
  (read-position [store] "The stored `{:token :cursor}`, or nil if none.")
  (write-position! [store position] "Persist `{:token :cursor}`; returns it."))

(defrecord AtomStore [a]
  CursorStore
  (read-position [_] @a)
  (write-position! [_ p] (reset! a p) p))

(defn atom-store
  "An in-memory `CursorStore` over an atom — the default and the test seam.  A durable
  deployment supplies its own (a file, a KV row); the cursor is small (`{:token :cursor}`)
  and written once per processed batch."
  []
  (->AtomStore (atom nil)))

;; ---- the snapshot half: a cone-aware re-read of current state ------------

(defn- ground
  "Substitute a solution's `bindings` into `goal`, reproducing the concrete sentence the
  solution stands for — `(queries ?a ?q)` + `{?a Ava ?q Q1}` -> `(queries Ava Q1)`.  Sound
  for koinii's EXACT-predicate goals (the speech-act vocabulary), where the grounded goal
  equals the stored sentence; a SUBSUMING goal (`(animal ?x)` answered by `(dog Muffet)`)
  would need the stored sentences instead, and is out of scope here."
  [goal bindings]
  (walk/postwalk #(get bindings % %) goal))

(defn snapshot
  "The SNAPSHOT half of CDC: the channel's current truth for `goal` in `context`, as a SET
  of sentences.  A cone-aware re-read (`channel/query`), authoritative over the incomplete
  incremental stream — it reflects retractions the feed drops.  State, NOT order: it
  recovers current beliefs, not the sequence they arrived in (carry the cursor ordinal if
  order matters — D7)."
  [handle goal context]
  (into #{} (map #(ground goal %)) (ch/query handle goal context)))

;; ---- the consumer: a materialized view kept in sync ----------------------

(defn open
  "A CDC consumer for `goal`/`context` over the WIRE channel `handle`, with a client-side
  `store` for the durable cursor.  Holds a materialized view — a SET of sentences — the
  agent's replica of the channel's truth for `goal`.  `initial-view` seeds it: on a restart,
  pass the view the agent persisted (its durable state), so an in-ring resume tails onto it
  without a snapshot; omit it (empty) for a fresh agent.

  **One consumer, one driving thread.**  A consumer is an agent's replica and `sync!` is
  how that agent advances it; two threads driving one consumer is not a shape this is for,
  and the cursor makes the reason concrete — a stored position is a claim about what this
  replica has applied, and two drivers each advancing it apply half the stream apiece.
  `sync!` takes the consumer's own monitor (`:lock`) so an interleaving cannot corrupt the
  view outright, but the serialization it buys is a floor, not a licence: what the second
  caller gets is whatever the first left, which is rarely what it asked for."
  ([handle goal context store] (open handle goal context store #{}))
  ([handle goal context store initial-view]
   {:handle handle :goal goal :context context :store store :view (atom initial-view)
    ;; the monitor `sync!` holds — per consumer, so two consumers never contend, and
    ;; uncontended within one because a consumer has a single driving thread
    :lock (Object.)}))

(defn view-of
  "The consumer's current materialized view — the SET of sentences it believes for its
  goal.  A plain read of the replica; `sync!` is what keeps it current."
  [consumer]
  @(:view consumer))

(defn- apply-events
  "Fold feed `events` into `view`: add every `:believed-added` sentence, drop every
  `:believed-removed` one.  Set-based on sentence identity, so replaying an event a second
  time is a no-op (the channel's idempotence) — a re-read and a replayed tail reach the same view."
  [view events]
  (reduce (fn [v e]
            (as-> v v
              (into v (map :sentence) (:believed-added e))
              (reduce disj v (map :sentence (:believed-removed e)))))
          view events))

(defn sync!
  "Advance the consumer to the channel's current state and return its view (a set of
  sentences).  CDC snapshot+tail:

  - **Resume** from the stored cursor when there is one and it is still in the ring: apply
    the tailed events onto the (durable) view, no snapshot needed — the in-ring happy path.
  - **Snapshot** when `poll` reports `:lagged` non-zero (the cursor fell off the ring) or the
    subscription was reaped (`:unknown-subscription`): re-read current state, reconcile the
    view set-based, and resume tailing from the newest cursor.  This is the correctness
    core — the failure it prevents is SILENT loss, so it re-reads rather than trusting a
    stream it knows is incomplete.
  - **Bootstrap** a fresh consumer (no stored cursor): open a subscription, snapshot, tail.

  Polls non-blocking and drains to the ring's head, persisting the final position.
  Idempotent: calling it again when nothing moved is a no-op that returns the same view.

  **One driving thread per consumer** (`open`).  The body is a read-modify-write over the
  stored cursor and the view, so it runs under the consumer's own monitor — cheap, and
  uncontended when the contract above is kept.  The monitor keeps two callers from
  corrupting the replica; it does not make two drivers a sensible arrangement.

  **Any failure of the poll is a failure.**  A refusal carries a `:type` this reads, but a
  transport that throws something else — or an `ex-info` with no `:type` at all — is still
  the poll not having answered: it is re-thrown with the original as the cause rather than
  falling through to the drained-to-head arm, which would persist a nil cursor and hand
  back the stale view as though the stream were current."
  [consumer]
  (let [{:keys [handle goal context store view lock]} consumer
        m         (:medium handle)
        snapshot! (fn [] (reset! view (snapshot handle goal context)))]
    (locking lock
      ;; the stored position is read INSIDE the monitor: read outside it, two callers both
      ;; see "no cursor", both bootstrap, and the second's snapshot lands on top of the
      ;; first's applied batch
      (let [pos0 (read-position store)]
        (loop [pos     (or pos0
                           ;; bootstrap: open a subscription, snapshot, tail from it
                           (let [{:keys [token cursor]} (ch/-feed-open m goal context)]
                             (snapshot!)
                             {:token token :cursor cursor}))
               snapped (when (nil? pos0) true)]     ; Object, not a primitive boolean (recur)
          (let [{:keys [token cursor]} pos
                result   (try {:ok (ch/-feed-poll m token cursor nil)}
                              (catch Exception e {:err e}))
                err      (:err result)
                ;; nil for anything that is not a typed refusal, which is why the arms
                ;; below branch on `err` itself and read the type only to *classify* it
                err-type (:type (ex-data err))]
            (cond
              ;; the subscription was reaped (idle past the daemon's window) — re-open,
              ;; snapshot, and tail the fresh subscription (its early events overlap the
              ;; snapshot; set-safe)
              (= :unknown-subscription err-type)
              (let [{:keys [token cursor]} (ch/-feed-open m goal context)]
                (snapshot!)
                (recur {:token token :cursor cursor} true))

              (some? err)
              (throw (ex-info "koinii: catch-up feed error"
                              {:type (or err-type :koinii/feed-error) :token token}
                              err))

              :else
              (let [{:keys [events lagged]} (:ok result)
                    next-cursor (:cursor (:ok result))]
                ;; a poll that answered without a cursor cannot be resumed from, and
                ;; storing the nil would turn the next `sync!` into a bootstrap that
                ;; re-snapshots silently — so the malformed reply is refused where it lands
                (when-not (nat-int? next-cursor)
                  (throw (ex-info (str "koinii: catch-up poll answered no cursor ("
                                       (pr-str next-cursor)
                                       ") — there is no position to resume from")
                                  {:type :koinii/no-cursor :token token :cursor next-cursor})))
                (cond
                  ;; fell off the ring: the stored cursor cannot replay the gap.  Snapshot
                  ;; (the only complete recovery), then resume from the cursor the poll
                  ;; handed back — the surviving ring events are already in the snapshot.
                  ;; `snapped` guards against re-snapshotting in the same pass.
                  (and (pos? (long (or lagged 0))) (not snapped))
                  (do (snapshot!)
                      (recur {:token token :cursor next-cursor} true))

                  ;; drained to the head — persist the position and return the view
                  (empty? events)
                  (do (write-position! store {:token token :cursor next-cursor})
                      @view)

                  ;; in-ring: apply the batch onto the durable view and keep draining
                  :else
                  (do (swap! view apply-events events)
                      (write-position! store {:token token :cursor next-cursor})
                      (recur {:token token :cursor next-cursor} snapped)))))))))))

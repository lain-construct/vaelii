;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.jobs
  "Long work, as jobs: one registry, one progress reading, one cancel.

  Three things this process does take minutes rather than milliseconds — filling a KB
  from a corpus, writing one back out, and joining every rule over everything stored.
  Each of them wants the same four capabilities, and they are the only four: run on a
  thread of its own so the pages keep answering, say where it has got to, stop when
  asked, and leave a report somebody can read afterwards.  That shape is here once.

  **A job** is `{:id :label :kind :status :progress :started :finished :error :summary
  :result-url}`, plus a cancel flag and the future, which no view carries.  `submit`
  returns the id; `job` reads one; `jobs` lists them, newest first.  The caller's `work`
  is handed a `progress!` fn and nothing else: what it records shows up under
  `:progress`, and what it *throws* is how cancellation lands, because a tight assert
  loop has no other point at which stopping is safe.

  **One status vocabulary**, whatever the job is doing:

      :running → :cancelling → :done | :cancelled | :failed

  `:cancelling` is the honest middle: `cancel!` sets the flag and returns, and the work
  keeps running until it reaches its next progress report — which, for a phase that
  reports none (opening a large store scans its whole record log before it says
  anything), can be a while.

  **The single writer stays single.**  `:writes` names the KB a job writes, or `true` for
  one it has not opened yet, and **one writing job runs at a time**: a second is refused
  with a message naming the job that holds the writer.  Two interleaved writers are not
  serializable (docs/storage.md, the single-writer contract), and a registry that let two
  through would be a way around the contract rather than a place to watch it from.
  `writes-kb?` is the other half of the same question, asked by identity, so a job filling
  one KB never blocks a write to another.

  **Cancellation is cooperative, and for a KB-writing job that is not negotiable.**  A
  thread interrupt landing mid-cascade on a durable store surfaces as
  `ClosedByInterruptException` and can leave a torn removal, so a job with `:writes` is
  flagged and never interrupted however long it takes to notice.  A job that writes
  nothing may say `:interruptible? true` and be cancelled the hard way as well; the
  registry checks both, so the two can never be confused for one another.

  **A finished job's report outlives the job**, for an hour — long enough to read what it
  did, since the page that would have shown it is usually the page you navigated away
  from.  Nothing *unsettled* is ever dropped, at any age: forgetting a job is releasing
  its writer claim, and a thread that is still running is still writing.  So a wedged job
  keeps its place and keeps counting towards the running badge, which is the truth about
  the process — better than a store two writers took turns on."
  (:require [taoensso.trove :as trove]))

(def fast-path-ms
  "How long a caller may wait for a job before answering with a progress page instead of
  its result.  A quarter of a second: the point is that a small operation does **not**
  acquire a spinner and a second round trip, since a tool where every action costs one
  feels slower than the thing it replaced."
  250)

(def ^:private finished-ttl-ms
  "How long a settled job's report stays in the registry.  There is deliberately no
  companion bound for an *unsettled* one — `sweep` says why."
  (* 60 60 1000))

(defonce ^:private state (atom {:jobs {} :order [] :next-id 0}))

;; `submit`'s writer claim is a read-test-write across `@state` — the test that no other
;; job holds the writer and the `swap!` that registers this one — which one `swap!` cannot
;; express, since it refuses rather than retries.  This makes the two one step.
(defonce ^:private claim-monitor (Object.))

(def ^:private cancelled
  "The `:type` a cancelled `progress!` throws, and the only thing that tells a cancelled
  job from a failed one."
  ::cancelled)

(defn cancelled?
  "Was `t` thrown by a **cancellation** rather than by a failure — the `progress!` throw
  `cancel!` arms, or the interrupt it sends a job that writes nothing?

  Public because a caller filing a status of its own beside the registry's — the catalog,
  onto the entry a load leaves behind — has to classify a throw exactly as `submit` does,
  and the alternative is this literal written in two places."
  [t]
  (or (= cancelled (:type (ex-data t)))
      (instance? InterruptedException t)))

(defn- now [] (System/currentTimeMillis))

(defn- settled? [j] (not (#{:running :cancelling} (:status j))))

(defn- view
  "A job as something safe to render or send: the cancel flag, the future and the KB it
  writes dropped, elapsed time filled in.  `:writes?` survives the dropping because it is
  what decides the cancel tier and what a refusal is about; the KB itself is nobody's to
  hand out."
  [j]
  (when j
    (-> (dissoc j :cancel :future :thread :writes)
        (assoc :writes?    (some? (:writes j))
               :elapsed-ms (- (or (:finished j) (now)) (:started j))))))

(defn- sweep
  "Drop the reports nobody can still be reading.  Runs on `submit`, which is the only
  moment the registry grows.

  **Only a settled job is ever dropped**, and no age changes that.  Forgetting a job is
  releasing its writer claim — `writer` and `writes-kb?` are both reads of this map — so
  dropping one whose thread is still running admits a second writer to a KB the first is
  still writing, which is the single thing the claim exists to prevent (docs/storage.md,
  the single-writer contract).  A wedged job therefore keeps its place and keeps counting
  towards the running badge: a thread that will never return is a true thing to say about
  this process, and saying it is better than a store two writers took turns on."
  [s]
  (let [cutoff (- (now) finished-ttl-ms)
        live?  (fn [j] (or (not (settled? j))
                           (> (or (:finished j) (:started j)) cutoff)))
        kept   (into {} (filter (comp live? val)) (:jobs s))]
    (assoc s :jobs kept :order (vec (filter kept (:order s))))))

(defn- update-job!
  "Apply `f` to job `id` — **and only while the registry still holds it**.  Every write to
  a job goes through here, because a `swap!` reaching `[:jobs id]` for an id the sweep or
  `reset-registry!` has already dropped does not fail: it *recreates* the job as a
  fragment, a `:status` with no `:started` for `view` to subtract from, absent from
  `:order` and so invisible to every listing that would have shown it up."
  [id f]
  (swap! state (fn [s] (cond-> s (contains? (:jobs s) id) (update-in [:jobs id] f))))
  nil)

(defn job
  "Job `id`, as a view, or nil once it has been swept."
  [id]
  (view (get-in @state [:jobs id])))

(defn jobs
  "Every job the registry still holds, newest first — the order `/jobs` lists them in."
  []
  (let [{js :jobs :keys [order]} @state]
    (into [] (comp (map js) (keep view)) (reverse order))))

(defn running
  "The jobs that have not settled, newest first.  What a panel polls on, and what the
  running badge counts."
  []
  (into [] (remove settled?) (jobs)))

(defn latest
  "The newest job of `kind`, settled or not — the last export's report is what the export
  panel shows, and it is worth keeping visible until the next one replaces it."
  [kind]
  (first (filter #(= kind (:kind %)) (jobs))))

(defn writer
  "The running job that holds this process's writer, or nil.  What `submit` refuses a
  second writing job against, and what a refusal names."
  []
  (first (filter :writes? (running))))

(defn writes-kb?
  "Is a job writing **this** KB, by identity?  Reading beside a writer is sound and
  writing beside one is not, and the question is about the KB rather than about the
  process: a job filling one KB is no reason to refuse a write to another."
  [kb]
  (let [{:keys [jobs]} @state]
    (boolean (and kb
                  (some (fn [j] (and (not (settled? j)) (identical? kb (:writes j))))
                        (vals jobs))))))

(defn- progress-fn
  "The `:on-progress` callback a job's work is handed: record where it has got to, and
  throw when it has been asked to stop.  Throwing is the whole of cancellation — every
  long operation in this engine takes an `:on-progress` and none of them has another
  point at which stopping leaves a readable KB or a directory rather than a file
  half-written."
  [id cancel]
  (fn [p]
    ;; the message is what the card shows beside the status, so it says what stopping here
    ;; means rather than repeating the status word
    (when @cancel
      (throw (ex-info "stopped at a progress report, as asked — what had landed stays"
                      {:type cancelled})))
    (update-job! id #(update % :progress merge (assoc p :at (now))))))

(defn submit
  "Run `work` as a job and return its id.  `work` takes one argument, the `progress!` fn
  above, and its return value is filed as the job's `:summary` (a map may carry a
  `:result-url`, which then overrides the one submitted).

  `opts`:

  | key | |
  |---|---|
  | `:label` | what the job is called on screen |
  | `:kind` | `:load` / `:export` / `:chain` — what a panel filters on |
  | `:writes` | the KB this job writes, or `true` for one it will open |
  | `:interruptible?` | may its thread be interrupted on cancel?  Only for a job that writes nothing |
  | `:progress` | the first progress reading, before the work has said anything |
  | `:result-url` | where to send a reader when it finishes |

  Any other key is carried through onto the job, which is how the export's destination
  and the entry's name reach the panel that renders them.

  Throws `{:type :job-busy}` when `:writes` is asked for and another job already holds
  the writer.  The refusal names the holder rather than queueing behind it: two writers
  are not serializable, and a queue would make a load's wall-clock reading mean whatever
  was in front of it."
  [{:keys [label kind writes progress result-url] :as opts} work]
  (let [cancel (atom false)
        ;; the work's own thread, published by the work itself.  `cancel!` interrupts
        ;; *that* rather than calling `future-cancel`, so the body always reaches its own
        ;; catch and files its own status — a cancelled future's `deref` throws instead of
        ;; answering, which would have `wait` return before the job had settled.
        thread (promise)
        id     (locking claim-monitor
                 (when writes
                   (when-let [w (writer)]
                     (throw (ex-info (str "job " (:id w) " (" (:label w) ") is already"
                                          " running, and it is this process's one writer")
                                     {:type :job-busy :holder (:id w) :label (:label w)}))))
                 (let [id (str (:next-id (swap! state update :next-id inc)))]
                   (swap! state (fn [s]
                                  (-> (sweep s)
                                      (assoc-in [:jobs id]
                                                (merge (dissoc opts :progress)
                                                       {:id id :label label :kind kind
                                                        :status :running
                                                        :progress (or progress {:phase :starting :done 0})
                                                        :result-url result-url
                                                        :started (now)
                                                        :cancel cancel}))
                                      (update :order conj id))))
                   id))
        f      (future
                 (deliver thread (Thread/currentThread))
                 (try
                   (let [summary (work (progress-fn id cancel))]
                     (update-job! id
                                  (fn [j]
                                    (-> (merge j (cond-> {:status :done :finished (now)}
                                                   (map? summary)        (assoc :summary summary)
                                                   (:result-url summary) (assoc :result-url (:result-url summary))))
                                        ;; the last reading a finished job took is the phase it
                                        ;; finished *in*, which reads as though it stopped there.
                                        ;; A failed or cancelled one keeps its last reading, since
                                        ;; where it got to is the whole of what it has to say
                                        (assoc-in [:progress :phase] :done))))
                     (trove/log! {:level :info :id ::done
                                  :msg (str "job " id " (" label ") finished")
                                  :data (when (map? summary) summary)}))
                   (catch Throwable t
                     ;; an interrupt is what `cancel!` does to a job that writes nothing,
                     ;; so it reads as a cancellation and not as a failure
                     (let [c? (cancelled? t)]
                       (update-job! id #(merge % {:status (if c? :cancelled :failed)
                                                  :finished (now)
                                                  :error (or (.getMessage t) (str (class t)))}))
                       (when-not c?
                         (trove/log! {:level :error :id ::failed
                                      :msg (str "job " id " (" label ") failed: "
                                                (.getMessage t))}))))
                   (finally
                     ;; a `future` runs on a pooled thread, so an interrupt this job was
                     ;; sent and never blocked long enough to observe would otherwise be
                     ;; delivered to whatever ran next on it.  Reading the flag clears it.
                     (Thread/interrupted))))]
    (update-job! id #(assoc % :future f :thread thread))
    id))

(defn cancel!
  "Ask job `id` to stop at its next progress report, and answer whether there was one to
  ask.  `!` because of what a stopped job leaves behind: a KB holding a prefix of a load
  or of a chaining run, or a directory holding part of a dump.

  A job that writes a KB is flagged and **never** interrupted, however long it takes to
  notice — an interrupt landing mid-cascade on a durable store tears the write it lands
  in.  A job that writes nothing and says `:interruptible? true` is flagged *and*
  interrupted, so it unwinds promptly rather than at a report it may not reach.  Both are
  checked, not one: a job that says it may be interrupted and writes a KB anyway is not
  interrupted, since the reason is about the store rather than about the promise."
  [id]
  (when-let [j (get-in @state [:jobs id])]
    (when-not (settled? j)
      (reset! (:cancel j) true)
      (swap! state assoc-in [:jobs id :status] :cancelling)
      (when (and (:interruptible? j) (nil? (:writes j)))
        ;; bounded, because a thread that has not published itself yet is one the
        ;; cooperative flag already covers — waiting on it forever would hang the request
        ;; that asked for the cancel
        (some-> ^Thread (deref (:thread j) 1000 nil) .interrupt)))
    true))

(defn wait
  "Block up to `ms` for job `id` to settle, then answer its view — settled or not, so the
  caller decides what to do about a job that is still going.  This is what the fast path
  is: submit, wait `fast-path-ms`, and answer with the result if it is already there."
  [id ms]
  (when-let [f (:future (get-in @state [:jobs id]))]
    (deref f ms ::timeout))
  (job id))

(defn reset-registry!
  "Cancel every job and forget them all.  For a process shutting down and for tests;
  nothing in the browser calls it."
  []
  (doseq [id (:order @state)] (cancel! id))
  (reset! state {:jobs {} :order [] :next-id 0}))

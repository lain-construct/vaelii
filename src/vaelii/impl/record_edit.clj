;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.record-edit
  "Premise removals and rule direction changes applied to the records of a KB whose belief
  is not built (`apply!`), and the sweep that follows the rebuild (`sweep!`):
  `vaelii.core/edit-records!` and `vaelii.core/settle-record-edits!` are the entry points.
  See docs/storage.md, \"Editing the records of a KB without belief\"."
  (:require [vaelii.impl.capabilities :as cap]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.integrate :as integrate]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.opts :as opts]
            [vaelii.impl.progress :as progress]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.recovery :as recovery]
            [vaelii.impl.reindex :as reindex]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.special :as special]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- the batch --------------------------------------------------------------------

(defn- check-kb!
  "Refuse a KB that has belief: the batch skips the checks, the dependency sweep and the
  settle that belief owes, so it runs only where there is none."
  [kb]
  (let [hz (kb/write-hazards kb)]
    (when (or (not (:no-belief hz)) (:stale-belief hz))
      (throw (ex-info (str "edit-records! writes records with no checks, no dependency sweep and no"
                           " settle, so it runs only on a KB whose belief is not built: open the"
                           " store with {:recover? false}.  This KB "
                           (if (:stale-belief hz)
                             "answers from an installed reasoning image"
                             "has belief")
                           "; edit! is the write for it.")
                      {:type :belief-built :operation "edit-records!"
                       :hazards (vec (sort (keys hz)))})))))

(defn- removable-problem
  "Why the record `sx` at handle `h` cannot be removed at record level, or nil.  The
  departure of an `except`, a `defeat` or an `exceptWhen` meta-sentex re-posts what the
  remaining ones still name, which `reindex/unindex-one!` does not do."
  [h sx]
  (let [s (sx/sentence-of sx)
        f (nm/functor s)]
    (when (or (sx/exceptWhen-meta? s) (= sx/except-functor f) (= sx/defeat-functor f))
      {:type :record-edit-unsupported :handle h :functor f :operation "edit-records!"
       :message (str "handle " h " is " (pr-str f) " record; its departure re-posts the index"
                     " entries the remaining ones need, which edit-records! does not compute."
                     "  Remove it with edit! on a KB with belief.")})))

(defn- direction-problem
  "Why rule handle `h`, stored as `sx`, cannot take `direction`, or nil."
  [h sx direction]
  (cond
    (not (contains? sx/direction-engines direction))
    {:type :unknown-option :mismatch :bad-value :handle h :direction direction
     :options (vec (sort (keys sx/direction-engines))) :operation "edit-records!"
     :message (str "unknown direction " (pr-str direction) " for handle " h)}

    (nil? sx)
    {:type :unknown-handle :handle h :operation "edit-records!"
     :message (str "handle " h " names no stored record, so it has no direction to change")}

    (not (rules/rule? sx))
    {:type :unknown-option :mismatch :conflict :handle h :direction direction
     :operation "edit-records!"
     :message (str "handle " h " is not a rule, so it has no direction")}

    (contains? (:engines sx) :solve)
    {:type :unknown-option :mismatch :conflict :handle h :direction direction
     :operation "edit-records!"
     :message (str "handle " h " is a choice or constraint rule; a solve decides its head,"
                   " so it takes no direction")}))

(defn- throw-problem! [problem]
  (when problem (throw (ex-info (:message problem) (dissoc problem :message)))))

(defn- scan-justifications
  "One pass over every stored justification, keeping the ones a batch can kill: those
  resting on a handle of `removals` or fired by a rule of `narrowed`, and those concluding
  a handle of `removals`.  Returns `{jid justification}`."
  [records removals narrowed]
  (with-open [r (progress/start ::scan "edit-records!: read the justifications"
                                (cap/count-justifications records))]
    (persistent!
     (reduce (fn [acc id]
               (progress/tick! r)
               (if-let [j (p/get-justification records id)]
                 (if (or (contains? removals (:consequence j))
                         (contains? narrowed (:informant j))
                         (some removals (jtms/rests-on j)))
                   (assoc! acc id j)
                   acc)
                 acc))
             (transient {})
             (cap/hinting (cap/justification-prefetcher records) cap/recovery-hint-chunk
                          (p/justification-ids records))))))

(defn- plan
  "Which removals are deleted and which only lose their premise mark, and which
  justifications go.  A removal is deleted unless a justification that survives the batch
  concludes it.  Keeping one revives the justifications resting on it, so the split is
  iterated to a fixpoint; the deleted set only shrinks.  Returns `{:delete #{h} :keep #{h}
  :dead {jid justification}}`."
  [removals narrowed js]
  (loop [deleted removals]
    (let [dead?  (fn [j] (or (contains? narrowed (:informant j))
                             (some deleted (jtms/rests-on j))))
          kept   (into #{} (comp (remove dead?) (map :consequence) (filter deleted)) (vals js))]
      (if (seq kept)
        (recur (reduce disj deleted kept))
        {:delete deleted
         :keep   (into #{} (remove deleted) removals)
         :dead   (into {} (filter (comp dead? val)) js)}))))

(defn apply!
  "Apply `batch` to the records of `kb`, which must have no belief: `:remove`, a seq of
  handles, and `:direction`, `{handle direction}` with a direction `sx/direction-engines`
  names.  No check, no dependency sweep and no settle runs.

  A removed record is deleted with its index postings unless a justification that
  survives the batch concludes it; such a record only loses its premise mark.  A rule's
  direction is written into its record.  Every stored justification resting on a deleted
  record, and every firing of a rule the batch takes off `:forward`, is deleted, except a
  firing that rests on a deleted `genl` or `genlCx` edge: that one stays stored for
  `sweep!`, which reads its antecedents as the facts to re-chain and then deletes it.  A
  removal naming no stored record is counted under `:absent`, so the same batch run again
  after a crash completes it.

  Returns `{:removed n :unpremised n :absent n :redirected n :justifications-removed n
  :seeds [h …]}`: `:seeds` are what the settle starts from, the kept removals, the stored
  conclusions of the deleted justifications and the rules the batch puts on `:forward`.

  Refuses a KB with belief (`:belief-built`), an `except`, `defeat` or `exceptWhen`
  removal (`:record-edit-unsupported`), and a direction on a handle that is not a stored
  derive rule (`:unknown-option`, `:unknown-handle`), before writing anything."
  [kb batch]
  (opts/check! batch #{:remove :direction} "edit-records!"
               "A key nothing reads would leave its edits unapplied.")
  (check-kb! kb)
  (let [records    (:records kb)
        index      (:index kb)
        directions (into {} (:direction batch))
        removes    (into [] (distinct) (:remove batch))
        ;; a nil removal, `handle-of`'s answer for a sentence the KB does not hold, names
        ;; no stored record and counts under `:absent`
        stored     (into {} (keep #(when-let [sx (and (integer? %) (p/get-sentex records %))]
                                     [% (assoc sx :id %)]))
                         (concat removes (keys directions)))
        removals   (into #{} (filter stored) removes)]
    ;; every refusal before the first write
    (run! #(throw-problem! (removable-problem % (stored %))) removals)
    (doseq [[h d] directions]
      (throw-problem! (direction-problem h (stored h) d))
      (when (contains? removals h)
        (throw-problem! {:type :unknown-option :mismatch :conflict :handle h
                         :operation "edit-records!"
                         :message (str "handle " h " is both removed and redirected")})))
    (let [engines  (into {} (map (fn [[h d]] [h (sx/direction-engines d)])) directions)
          narrowed (into #{} (comp (remove (fn [[_ e]] (contains? e :forward))) (map key)) engines)
          js       (if (or (seq removals) (seq narrowed))
                     (scan-justifications records removals narrowed)
                     {})
          {:keys [delete keep dead]} (plan removals narrowed js)
          ;; a firing that named a deleted closure edge as its witness may still be
          ;; licensed by a second route; `recover` leaves it out as `:unrooted`, and
          ;; `sweep!` reads the facts to re-chain off it before deleting it
          edges    (into #{} (filter #(special/closure-edge-relation (sx/sentence-of (stored %)))) delete)
          left     (into #{} (comp (filter (fn [[_ j]] (and (integer? (:informant j))
                                                            (not (contains? narrowed (:informant j)))
                                                            (some edges (:antecedents j)))))
                                   (map key))
                         dead)
          ;; a rule the batch puts on `:forward` is a seed too, every run, so a run after a
          ;; crash names it again although its record already holds the direction
          seeds    (-> (into (sorted-set) keep)
                       (into (comp (map :consequence) (remove delete) (filter integer?)) (vals dead))
                       (into (comp (filter (fn [[_ e]] (contains? e :forward))) (map key)) engines))]
      ;; Written in this order so that a crash at any point leaves a store the same batch
      ;; run again completes: the direction and the premise marks first, then each deleted
      ;; record with its postings, and the dead justifications last, which `recover` leaves
      ;; out of the network while their records are gone (`:unrooted`).
      (doseq [[h e] engines
              :let [old (stored h)]
              :when (not= e (:engines old))
              :let [new (assoc old :engines e)]]
        (p/unindex-sentex! index old h)
        (p/put-sentex records new)
        (p/index-sentex index new h))
      (run! #(p/unmark-premise! records %) keep)
      (doseq [h (sort delete)]
        (reindex/unindex-one! index (stored h) h)
        (p/delete-sentex! records h))
      (run! #(p/delete-justification! records %) (sort (remove left (keys dead))))
      (kb/refresh-index-image! kb)
      {:removed                (count delete)
       :unpremised             (count keep)
       :absent                 (- (count removes) (count removals))
       :redirected             (count engines)
       :justifications-removed (- (count dead) (count left))
       :seeds                  (into [] (filter #(p/get-sentex records %)) seeds)})))

;; ---- the sweep after the rebuild ----------------------------------------------------

(def ^:private sweep-steps
  "The steps of `sweep!`, in order."
  [:unrooted :sweep :settle :chain :rechain :settle-chain])

(defn sweep!
  "Delete the unrooted justifications the last `recover` left out (`:unrooted`), sweep
  the consequence closure of their stored conclusions and of `seeds` as a retraction
  sweeps it — every record there that is not a premise and is OUT goes, with the
  justifications touching it (`jtms/sweep!`), through the removal choke point — and settle;
  then chain each forward rule among `seeds` over the stored facts, re-chain the
  antecedents of the unrooted rule firings (`special/firing-seeds`, a deleted record
  standing for the edge each one named), and settle again.  Runs over a KB with belief.
  Returns `{:unrooted n :removed-sentexes n :removed-justifications n :rules-chained n
  :rechained n}`.

  `report`, when given, is called with `{:phase :sweep :step k :done i :total 6}` as each
  step begins (`sweep-steps`), and with the chain's `:derived` and `:pending` beside while
  it runs."
  ([kb seeds] (sweep! kb seeds nil))
  ([kb seeds report]
   (let [step!   (fn [k & [extra]]
                   (when report
                     (report (merge {:phase :sweep :step k
                                     :done (.indexOf ^java.util.List sweep-steps k)
                                     :total (count sweep-steps)}
                                    extra))))
         _       (step! :unrooted)
         records (:records kb)
         tms     (reasoning/tms kb)
         unrooted (:unrooted @(:unrecovered kb))
         js      (into [] (keep #(p/get-justification records %)) unrooted)
         concl   (into [] (keep :consequence) js)
         gone?   (fn [h] (and (integer? h) (nil? (p/get-sentex records h))))
         ;; read off the records before they go, as `edit!` reads its seeds off the
         ;; justifications its sweep removed (`special/resubsumption-seeds`)
         refire  (special/firing-seeds js gone? gone?)
         _       (run! #(p/delete-justification! records %) unrooted)
         _       (swap! (:unrecovered kb) dissoc :unrooted)
         _       (step! :sweep)
         seeds   (into #{} (filter #(and (integer? %)
                                         (jtms/known-datum? tms %)
                                         (not (recovery/inert-marked? kb %))))
                       (concat seeds concl))
         rm      (if (seq seeds) (jtms/sweep! tms seeds) {})
         _       (integrate/apply-removals! kb rm)
         _       (step! :settle)
         _       (settle/settle kb)
         ;; the rules a batch put on `:forward`, joined over the facts as `assert` joins a
         ;; rule that newly runs forward
         rules   (into [] (filter #(some-> (p/get-sentex records %) rules/forward-sentex?))
                       (sort seeds))]
     (step! :chain {:rules (count rules)})
     (when (seq rules)
       (chain/chain-all kb rules (if report
                                   {:on-progress #(step! :chain (assoc % :rules (count rules)))}
                                   {})))
     (step! :rechain {:firings (count refire)})
     ;; re-asking firings the removal swept, so one that places nothing is not reported
     ;; (`chain/*report-no-placement?*`)
     (when (seq refire)
       (binding [chain/*report-no-placement?* false] (settle/rechain-seeds kb refire)))
     (when (or (seq rules) (seq refire))
       (step! :settle-chain)
       (settle/settle kb))
     {:unrooted               (count unrooted)
      :removed-sentexes       (count (:removed-sentexes rm))
      :removed-justifications (count (:removed-justifications rm))
      :rules-chained          (count rules)
      :rechained              (count refire)})))

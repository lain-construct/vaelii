;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.host.spindle
  "Bring a KB's shipped spindle up to the running engine's.

  A KB stores the starter ontology it was built with, and the engine that opens it later
  ships its own: a strength marked `set/monotonic`, a vocabulary term added to CxCore, a
  disjointness the ontology stopped stating.  `sync-spindle!` makes the KB state what this
  engine ships, context by context, and leaves everything else alone.

  **What is shipped** is what `starter/load-into` produces, read off a scratch in-memory KB
  it is loaded into — not the text of the files.  The two differ: `genlCx` edges are stored
  in CxUniverse whichever file states them, and the closing `unary_predicate` batch is
  stated by no file.  Each premise is attributed to the file whose load stored it.

  **Which contexts are synced exactly**: CxCore and the `kb/upper/` and `kb/middle/`
  contexts.  These are the engine's, so a premise there that the engine does not ship is
  retracted, a strength that differs is restated, and a missing one is asserted.  A
  context an author adds to the spindle — wired between CxCore and CxUniverse, say — is
  not one of them and is not read.

  **Which are only added to**: the collectors (`kb/` root files, CxUniverse today) and any
  other context a shipped file's content is stored in.  A collector gathers what the
  engine routes there from every context, so what it holds beyond the shipped content is
  not the engine's to retract.

  **Only the layers a KB has.**  A file whose context holds nothing in the KB is not
  loaded into it, and the collector files and the `unary_predicate` batch follow the upper
  layer: a core-only KB stays core-only.

  Comparison is by the form a KB file writes (`text/premise-entries`): a fact or rule
  under its strength wrapper, an `exceptWhen` as the wrapper it was asserted as.  A
  strength the engine **raised** is only an assertion, since `assert` raises a held
  premise's strength in place; one it **lowered** is the form retracted and the weaker one
  asserted, since nothing lowers a strength in place.

  **One batch.**  The sync is one `v/edit!`: the additions first, then the retractions,
  one settle.  So the belief a retraction would sweep and the addition rebuild keeps its
  witness through the batch, where retracting first tore the TMS down only to build it
  back up.  What cannot go in that order — a retraction of a record an addition lands on —
  goes before it (`sync-spindle!`)."
  (:require [vaelii.core :as v]
            [vaelii.host.seed :as seed]
            [vaelii.host.starter :as starter]
            [vaelii.impl.io.text :as text]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]))

(defn exact-contexts
  "The contexts `sync-spindle!` makes state exactly what the engine ships: CxCore and the
  upper and middle layers' contexts, as discovered on the classpath."
  []
  (into ['CxCore] (concat (seed/layer-contexts "upper") (seed/layer-contexts "middle"))))

(defn- premise-records
  [kb ids]
  (let [recs (:records kb)]
    (into [] (keep #(p/get-sentex recs %)) ids)))

(defn shipped
  "Every premise the starter stores, as `{:context c :form f :file ctx}`: the form a KB
  file writes it in, the context it is stored in, and the context of the file whose load
  stored it — `:unary-predicates` for the closing batch no file states.  In the order the
  load stored them, which is an order they assert in: the load retried what arrived
  before its dependencies.  Built in a scratch in-memory KB that is cleared before this
  returns."
  []
  (let [kb      (v/open-kb {:backend :memory :space [::shipped (random-uuid)] :recover? false})
        recs    (:records kb)
        seen    (volatile! #{})
        file-of (volatile! {})]
    (try
      (starter/load-into kb (fn [file]
                              (let [ids (set (p/premise-ids recs))]
                                (vswap! file-of into (map (fn [h] [h file])) (remove @seen ids))
                                (vreset! seen ids))))
      (let [[entries _] (text/premise-entries kb (premise-records kb (sort (p/premise-ids recs))))]
        (mapv (fn [{:keys [handles] :as e}]
                (-> e (dissoc :handles) (assoc :file (@file-of (first handles)))))
              entries))
      (finally
        (v/clear! kb)
        (v/close! kb)))))

(defn- held-forms
  "`{[context form] entry}` for the premises `kb` stores in `context`."
  [kb context]
  (let [[entries _] (text/premise-entries
                     kb (filterv #(some? (:strength %)) (v/sentexes-in-context kb context)))]
    (into {} (map (fn [e] [[(:context e) (:form e)] e])) entries)))

(defn- stored?
  "Does `kb` hold `form` in `context` as a premise at least as strong as the form states?
  Asked by lookup, so a collector holding a whole corpus is not read to answer it.  A form
  the lookup cannot take — a rule under its wrapper — reads as absent, and asserting it
  again is a no-op when it is there."
  [kb context form]
  (let [[sentence o] (text/peel-strength form)
        h (try (v/handle-of kb sentence context) (catch clojure.lang.ExceptionInfo _ nil))
        have (some->> h (v/sentex kb) :strength)]
    (boolean (and have (or (= have :monotonic) (not= :monotonic (:strength o)))))))

(defn plan
  "What `sync-spindle!` would change in `kb`, without changing it:

    :add     `{:context :form}` the shipped content `kb` lacks, in the layers it has,
             in `shipped`'s order
    :remove  `{:context :form :handles}` premises in an exact context the engine does not
             ship

  A premise the engine ships at a higher strength is an `:add` alone: asserting it raises
  the held one.  One it ships at a lower strength is a `:remove` and an `:add`.

  `shipped` defaults to a fresh `(shipped)`."
  ([kb] (plan kb (shipped)))
  ([kb shipped]
   (let [exact   (set (exact-contexts))
         upper   (set (seed/layer-contexts "upper"))
         roots   (set (seed/root-contexts))
         present (into #{}
                       (filter #(pos? (v/count-in-context kb %)))
                       (distinct (filter (every-pred symbol? (complement roots))
                                         (keep :file shipped))))
         ;; a collector file's axioms name terms from several upper members, and the
         ;; closing batch marks the types the upper layer defines: both belong to a KB that
         ;; has that layer.  A core-only KB holds CxUniverse too — the edge to CxCore.
         present (cond-> present
                   (some upper present) (into (conj roots :unary-predicates)))
         ours    (into #{} (map (juxt :context :form)) shipped)
         held    (into {} (mapcat #(held-forms kb %)) (filter (every-pred exact present) exact))
         wanted  (filter #(present (:file %)) shipped)
         ;; a default premise of one record, shipped known-true: the `:add` raises it.
         ;; An exceptWhen is two records, and is restated whole.
         raised? (fn [{:keys [context form handles]}]
                   (and (= 1 (count handles))
                        (nil? (second (text/peel-strength form)))
                        (contains? ours [context (list sx/strength-wrapper form)])))]
     {:add    (into []
                    (comp (remove (fn [{:keys [context form]}]
                                    (if (exact context)
                                      (contains? held [context form])
                                      (stored? kb context form))))
                          (map #(select-keys % [:context :form])))
                    wanted)
      :remove (into [] (comp (remove (fn [[k _]] (ours k))) (map val) (remove raised?)) held)})))

(defn- add!
  "Assert every `{:context :form}` of `entries` into `kb`, retrying the refused ones while a
  round makes progress — a file's order is its terms', not its dependencies'
  (`text/load-entries!`).  Returns what is still refused, each with the refusal's `:type`
  and message, rather than throwing: a KB whose own content refuses a shipped sentence is
  a finding about that KB, and the rest of the sync still applies."
  [kb entries]
  (let [attempt (fn [es]
                  (reduce (fn [acc {:keys [context form] :as e}]
                            (let [[sentence o] (text/peel-strength form)]
                              (try (v/assert kb sentence context (or o {})) acc
                                   (catch clojure.lang.ExceptionInfo ex
                                     (conj acc (assoc e :type (:type (ex-data ex))
                                                      :message (ex-message ex)))))))
                          [] es))]
    (v/with-deferred-settle kb
      (loop [pending (attempt entries)]
        (if (empty? pending)
          []
          (let [remaining (attempt (map #(select-keys % [:context :form]) pending))]
            (if (< (count remaining) (count pending))
              (recur remaining)
              remaining)))))))

(defn- records
  "The records asserting `form` lands on, each spelled without its strength: the sentence,
  or for an `exceptWhen` the wrapper and the rule it qualifies — a rule another form
  states too."
  [form]
  (let [[s _] (text/peel-strength form)]
    (if (and (seq? s) (= sx/except-wrapper (first s)) (= 3 (count s)))
      (let [[_ q rule] s]
        #{(list sx/except-wrapper (first (text/peel-strength q)) rule) rule})
      #{s})))

(defn- edit-entry
  "`{:context :form}` as a `v/edit!` `:add` line."
  [{:keys [context form]}]
  (let [[sentence o] (text/peel-strength form)]
    (cond-> [sentence context] o (conj o))))

(defn- batch!
  "Assert `entries`, then retract `handles`, as one `v/edit!`: one settle.  The edit is
  all-or-nothing, so an entry it refuses rolls the batch back; that entry is set aside
  with its refusal's `:type` and message and the batch runs again without it.  Returns
  the entries set aside."
  [kb entries handles]
  (loop [entries (vec entries) aside []]
    (if (and (empty? entries) (empty? handles))
      aside
      (let [refused (try (v/edit! kb {:add (mapv edit-entry entries) :remove handles})
                         nil
                         (catch clojure.lang.ExceptionInfo ex
                           (let [{:keys [rolled-back in index] :as data} (ex-data ex)]
                             ;; a removal's refusal is the KB refusing writes: not an
                             ;; entry to set aside
                             (if (and rolled-back (= :add in))
                               {:index index :type (:type data) :message (ex-message ex)}
                               (throw ex)))))]
        (if-let [{:keys [index] :as r} refused]
          (recur (into (subvec entries 0 index) (subvec entries (inc index)))
                 (conj aside (merge (nth entries index) (dissoc r :index))))
          aside)))))

(defn sync-spindle!
  "Make `kb`'s shipped spindle state what this engine ships (see the namespace doc), as
  one `v/edit!`: the additions, then the retractions, one settle.  Returns

    {:added n :removed n :refused [{:context :form :type :message} …]}

  **A retraction goes first** only when an addition lands on a record it retracts: a
  strength the engine lowered, whose weaker form would otherwise be asserted onto the
  premise and then retracted with it, or an `exceptWhen` restated around a rule the KB
  keeps.  Those are their own `edit!` before the batch.

  **An addition the batch refuses is set aside**, the batch rolled back and run without
  it, so the rest lands in one settle.  The ones set aside are asserted after it,
  retrying while a round makes progress (`add!`): the batch's refusal can be an order the
  batch could not fix, or content its own retractions then took away.  What still refuses
  is `:refused`.  Each refusal costs the batch one rollback.

  `kb` must accept writes (`v/write-hazards` empty).  `ships` is `(shipped)`, passed by a
  caller that syncs more than one KB or prices the sync apart from the scratch load."
  ([kb] (sync-spindle! kb (shipped)))
  ([kb ships]
   (let [{adds :add removes :remove} (plan kb ships)
         landing  (into #{} (mapcat (fn [{:keys [context form]}]
                                      (map #(vector context %) (records form))))
                        adds)
         restated (fn [{:keys [context form]}] (some #(landing [context %]) (records form)))
         handles  (fn [es] (into [] (comp (mapcat :handles) (distinct)) es))
         before   (handles (filter restated removes))]
     (when (seq before)
       (v/edit! kb {:remove before}))
     (let [aside   (batch! kb adds (handles (remove restated removes)))
           refused (if (seq aside)
                     (add! kb (map #(select-keys % [:context :form]) aside))
                     [])]
       {:added   (- (count adds) (count refused))
        :removed (count removes)
        :refused refused}))))

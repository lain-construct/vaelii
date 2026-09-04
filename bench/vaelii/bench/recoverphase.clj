;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.recoverphase
  "Where `recover`'s per-open time goes, step by step — the measurement
  `doc/design/persistence-prompts/01-recover-decomposition.md` rests on.

  `recover` is a **per-open** cost: every process start over a durable store pays it,
  proportional to the corpus.  `bench-reindex` times it whole; this splits it into the
  nine steps its body runs, so a design downstream (persist a derived-state image, bulk
  the TMS rebuild, parallelize) can be aimed at the step that actually holds the clock
  rather than a guess.  The four `rebuild-tms` steps had been measured; the other five —
  the taxonomy rebuild, the exception re-check, the supersession refresh, the opposed
  rebuild, the closing settle — were one number between them.  This is that split.

  **Method: a faithful replay, timed step by step.**  `timed-recover!` is `core/recover`'s
  body unrolled, each top-level call wrapped in a nanosecond clock and nothing else moved
  — same order, same bindings (`tax/*defer-depths?*`, `settle/*rebuilding?*`), same
  private `recovered-supersessions`.  It calls the engine, so it measures the engine; a
  drift from `core/recover` is a bug in this file, and the assertion `recover-parity!`
  runs both against one store and checks `in?` agrees for every handle.

  **The rebuild is cold by construction.**  The corpus is generated into a `:disk` record
  store, the store is closed, and a *fresh* KB is reopened against it with an empty TMS
  and taxonomy — so the closing settle genuinely iterates and its `:passes` (sub-question
  B) is the real scan count rather than 1 over an already-settled KB.

  Three sub-questions ride along, each deciding another prompt:
  - **B — settle passes.**  `(:passes (v/settle-stats kb))` after the replay: how many
    times the closing settle scanned the corpus.
  - **A — justification order.**  Steps 3+4 (load + relabel) rerun with the justification
    ids in `sort`ed order against hash order.  If sorting alone collapses the cost, the
    fix for [08] is three characters, not a protocol change.
  - **C — supersession over an equality closure.**  `recovered-supersessions` binds over
    equality *edges* while using the endpoint, so a class of k re-enters `equiv-class` k
    times: `Σ kᵢ²` at fixed total membership, invisible until a KB declares equalities.
    The `equality` mode holds the member count fixed and grows k; the cost tracking k is
    the signature.

  And the fetch this prompt removes, priced where it bites: `fetchfix` mode times one
  `get-sentex` per live sentex on a `:disk` store — the per-record read the node/premise
  loops no longer make, since the enumerator already proves the handle live.

  Run: `lein bench-recoverphase [mode] [args…]`
    decomp   [sizes…]   nine-step split at each size (default 100000 500000 1000000)
    fetchfix [size]     the removed fetch, priced on disk (default 300000)
                        idx picks the derived index kind (memory|columnar|dense|disk, default
                        memory).  memory is a RAM trie — too large for an 11M corpus; columnar
                        is the compact native index of a disk-columnar store.  Run with
                        -Dvaelii.disk.sync-ms=0 so the syncer never starves it
    equality [ks…]      supersession vs class size k (default 2 4 8 16 32 64)
    all                 decomp defaults + fetchfix 300000 + equality defaults
  Large sizes want heap: prefix with
    lein update-in :jvm-opts conj '\"-Xmx24g\"' -- with-profile +bench run -m vaelii.bench.recoverphase …"
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.pprint :as pprint]
            [clojure.set :as set]
            [taoensso.nippy :as nippy]
            [vaelii.core :as v]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.disk.backend :as disk]
            [vaelii.impl.disk.belief-snapshot :as bs]
            [vaelii.impl.io.generate :as gen]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reindex :as reindex]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]))

;; ---- plumbing -----------------------------------------------------------

(defn- tmpdir ^String []
  (str (java.nio.file.Files/createTempDirectory
        "vaelii-recphase-" (into-array java.nio.file.attribute.FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (java.io.File. dir)))] (.delete ^java.io.File f)))

(defmacro ^:private timed
  "[value ms] of evaluating `body`."
  [& body]
  `(let [t0# (System/nanoTime) r# (do ~@body)]
     [r# (/ (- (System/nanoTime) t0#) 1e6)]))

(defmacro ^:private ms
  "Milliseconds of evaluating `body` (value discarded)."
  [& body]
  `(let [t0# (System/nanoTime)] ~@body (/ (- (System/nanoTime) t0#) 1e6)))

(defn- gc! [] (dotimes [_ 3] (System/gc) (Thread/sleep 80)))

(def ^:private default-memo-budget
  "The scoped-closure memo budget a recover phase runs under when `vaelii.memo.budget`
  names none — core's steady-state constant for `tax/*scoped-memo-budget*`."
  8192)

(defn- memo-budget
  "The scoped-memo budget for a recover run: `vaelii.memo.budget` if it is set, the
  default otherwise.  Resolved per call, like the corpus, so a run can size the cache
  without a box's number baked into the source."
  ^long []
  (or (some-> (System/getProperty "vaelii.memo.budget") parse-long) default-memo-budget))

;; ---- the corpus ---------------------------------------------------------
;; A generated KB *with a forward rule*, so the store holds justifications and the
;; relabel has a derived structure to walk — the case every prior `recover` figure
;; skipped (`:chain? false`).  Written to a `:disk` store so the rebuild can be measured
;; cold against a fresh reopen.

(defn- gen-disk!
  "Generate a corpus into a fresh `:disk` store at `dir`, then close it.  Returns the load
  summary.  `chain?` toggles the forward rules that mint justifications; `:individuals` is
  held at the fact count so joins stay sparse (each derived fact gets ~one justification
  rather than the dense generator default's dozen), and `:max-derivations` caps the
  cascade so the record count lands near `n` rather than running away."
  ([^String dir n] (gen-disk! dir n {:chain? false}))
  ([^String dir n {:keys [chain? rules max-derivations individuals]}]
   (let [kb (v/open-kb {:records :disk :index :memory :dir dir :recover? false})]
     (v/clear! kb)
     (let [summary (gen/load-into kb (cond-> {:facts n
                                              :rules (if chain? (or rules 6) 0)
                                              :individuals (or individuals n)
                                              :types 200 :predicates 40
                                              :chain? (boolean chain?)}
                                       max-derivations (assoc :max-derivations max-derivations)))]
       (disk/close-dir! dir)
       summary))))

(defn- reopen-cold
  "A fresh KB over the on-disk store — empty TMS and taxonomy, records durable, `:memory`
  index empty (rebuilt by `reindex` before the replay reads it)."
  [^String dir]
  (v/open-kb {:records :disk :index :memory :dir dir :recover? false}))

;; ---- the replay: recover's body, unrolled and timed ---------------------
;; This must track `core/recover` line for line.  If that changes, change this and rerun
;; `recover-parity!` — the drift is otherwise silent.

(defn- rebuild-tms-split!
  "`core/rebuild-tms`, its four steps timed apart.  Returns `{:node :premise :just
  :relabel :skipped}` in ms.  The premise loop tests membership in the live set rather
  than fetching a record (the landed shape)."
  [kb]
  (let [tms  (:tms kb)
        rec  (:records kb)
        live (p/sentex-ids rec)
        stored? (fn [h] (or (not (integer? h)) (some? (p/get-sentex rec h))))
        skipped (volatile! 0)
        t-node (ms (doseq [id live] (jtms/ensure-node tms id 0)))
        t-prem (ms (doseq [id (p/premise-ids rec) :when (contains? live id)]
                     (jtms/add-premise tms id (p/premise-strength rec id))))
        t-just (ms (doseq [id (p/justification-ids rec)
                           :let [d (p/get-justification rec id)] :when d]
                     (if (and (stored? (:consequence d)) (every? stored? (:antecedents d)))
                       (jtms/add-justification tms d)
                       (vswap! skipped inc))))
        t-rel  (ms (jtms/relabel tms))]
    {:node t-node :premise t-prem :just t-just :relabel t-rel :skipped @skipped}))

(defn- timed-recover!
  "`core/recover` unrolled, every step timed.  Returns a map of ms per step plus the
  four-way `rebuild-tms` split and the settle stats."
  [kb]
  (v/reset-settle-stats! kb)
  (let [split   (rebuild-tms-split! kb)
        t-tax   (ms (binding [tax/*defer-depths?* true]
                      (special/rebuild-taxonomy kb)
                      (tax/refresh-beliefs (:taxonomy kb) #(jtms/in? (:tms kb) %)))
                    (tax/restore-depths (:taxonomy kb)))
        t-exc   (ms (special/recheck-every-exception kb))
        t-sup   (ms (special/refresh-supersessions kb (#'v/recovered-supersessions kb)))
        t-opp   (ms (kb/rebuild-opposed! kb)
                    (kb/rebuild-excepted! kb))
        t-set   (ms (binding [settle/*rebuilding?* true]
                      (settle/settle kb)
                      (let [{:keys [derived]} (chain/rerecord-refusals! kb)]
                        (when (pos? (long (or derived 0))) (settle/settle kb))))
                    (kb/note-hazards! kb {:no-belief false}))]
    {:split split
     :rebuild-tms (+ (:node split) (:premise split) (:just split) (:relabel split))
     :taxonomy t-tax :exceptions t-exc :supersessions t-sup
     :opposed t-opp :settle t-set
     :settle-stats (v/settle-stats kb)}))

;; ---- sub-question A: justification order --------------------------------
;; Steps 3+4 rerun with the justification ids sorted.  A separate cold reopen, since the
;; first replay has already built the network; here nodes+premises are rebuilt (the
;; prerequisite of add-justification) and then the two orders are each timed on their own
;; fresh relabel.

(defn- order-probe
  "[hash-ms sorted-ms just-count] for steps 3+4 — load justifications + relabel — in the
  two id orders, each over its own freshly-reopened cold store."
  [^String dir]
  (let [run (fn [order-fn]
              (let [kb  (reopen-cold dir)
                    _   (reindex/reindex kb)
                    tms (:tms kb) rec (:records kb)
                    live (p/sentex-ids rec)
                    stored? (fn [h] (or (not (integer? h)) (some? (p/get-sentex rec h))))]
                (doseq [id live] (jtms/ensure-node tms id 0))
                (doseq [id (p/premise-ids rec) :when (contains? live id)]
                  (jtms/add-premise tms id (p/premise-strength rec id)))
                (let [ids (order-fn (p/justification-ids rec))
                      t   (ms (doseq [id ids
                                      :let [d (p/get-justification rec id)] :when d]
                                (when (and (stored? (:consequence d))
                                           (every? stored? (:antecedents d)))
                                  (jtms/add-justification tms d)))
                              (jtms/relabel tms))]
                  [t (count ids)])))]
    (gc!)
    (let [[hash-ms jn] (run seq)
          _            (gc!)
          [sort-ms _]  (run sort)]
      [hash-ms sort-ms jn])))

;; ---- reporting the decomposition ----------------------------------------

(def ^:private step-order
  [[:node          "1 node creation        (ensure-node)"]
   [:premise       "2 premise marking      (add-premise)"]
   [:just          "3 justification load   (add-justification)"]
   [:relabel       "4 relabel              (whole graph)"]
   [:taxonomy      "5 rebuild-taxonomy     (+ refresh-beliefs)"]
   [:exceptions    "6 recheck-every-exception"]
   [:supersessions "7 refresh-supersessions"]
   [:opposed       "8 rebuild-opposed! + rebuild-excepted!"]
   [:settle        "9 closing settle       (+ rerecord-refusals)"]])

(defn- flat
  "The nine step timings as one map, folding the rebuild-tms split back in."
  [r]
  (merge (:split r)
         (select-keys r [:taxonomy :exceptions :supersessions :opposed :settle])))

(defn- report-decomp [n r order]
  (let [f     (flat r)
        total (reduce + (map (fn [[k _]] (double (get f k 0.0))) step-order))
        us    (fn [x] (* 1000.0 (/ (double x) n)))
        st    (:settle-stats r)]
    (println (format "%n── recover decomposition, %,d records ──" n))
    (println (format "%-42s %10s %9s %8s" "step" "ms" "µs/rec" "share"))
    (doseq [[k label] step-order]
      (let [x (double (get f k 0.0))]
        (println (format "%-42s %10.1f %9.2f %7.1f%%" label x (us x) (* 100.0 (/ x total))))))
    (println (format "%-42s %10.1f %9.2f %7.1f%%" "TOTAL (recover)" total (us total) 100.0))
    (println (format "  rebuild-tms subtotal            %10.1f ms   (skipped justifications: %,d)"
                     (double (:rebuild-tms r)) (long (:skipped (:split r)))))
    (println (format "  sub-Q B — closing settle: %d passes over %d settle iteration(s)"
                     (long (:passes st 0)) (long (:iterations st 0))))
    (when order
      (let [[h s jn] order]
        (println (format "  sub-Q A — justifications (%,d): steps 3+4  hash %.1f ms · sorted %.1f ms  (%.2f×)"
                         (long jn) (double h) (double s)
                         (if (pos? s) (/ (double h) (double s)) 0.0)))))))

;; ---- mode: decomp -------------------------------------------------------

(defn- recover-parity!
  "The replay believes what `core/recover` believes — the assertion that keeps
  `timed-recover!` honest against `core/recover`.  Two cold reopens of the same store,
  one settled by each path; `in?` compared for every handle."
  [^String dir]
  (let [a (reopen-cold dir) _ (reindex/reindex a) _ (timed-recover! a)
        b (reopen-cold dir) _ (v/reindex b)                 ; v/reindex = reindex + core/recover
        rec (:records a)
        ids (vec (p/sentex-ids rec))
        mism (reduce (fn [c id] (if (= (jtms/in? (:tms a) id) (jtms/in? (:tms b) id)) c (inc c)))
                     0 ids)]
    (println (format "  parity with core/recover: %s (%,d handles, %d disagreements)"
                     (if (zero? mism) "OK" "MISMATCH") (count ids) (long mism)))
    (zero? mism)))

(defn- decomp-run [n]
  (let [dir (tmpdir)]
    (try
      (let [summary (gen-disk! dir n {:chain? true :max-derivations (quot n 2)})
            recs    (:stored summary)]
        (println (format "%n=== %,d facts requested → %,d records, %,d derived%s ==="
                         (long n) (long recs) (long (:derived summary 0))
                         (if (:truncated? summary) " (chain truncated)" "")))
        (recover-parity! dir)
        (gc!)
        (let [kb          (reopen-cold dir)
              [_ ix-ms]   (timed (reindex/reindex kb))
              [r rec-ms]  (timed (timed-recover! kb))
              order       (order-probe dir)]
          (println (format "  reindex %.0f ms · recover %.0f ms · OPEN %.0f ms"
                           ix-ms rec-ms (+ ix-ms rec-ms)))
          (report-decomp recs r order)))
      (finally (disk/close-dir! dir) (rm-rf! dir)))))

;; ---- mode: fetchfix -----------------------------------------------------
;; The per-record read the landed node/premise loops skip, priced on disk: one
;; `get-sentex` per live sentex, a fetch those loops no longer make.

(defn- fetchfix-run [n]
  (let [dir (tmpdir)]
    (try
      (let [summary (gen-disk! dir n)
            recs    (long (:stored summary))
            kb      (reopen-cold dir)
            rec     (:records kb)
            _       (gc!)
            sweep   (ms (reduce (fn [c id] (if (some? (p/get-sentex rec id)) (inc c) c))
                                0 (p/sentex-ids rec)))]
        (println (format "%n── fetch-fix, priced on :disk (%,d records) ──" recs))
        (println (format "  one get-sentex per live sentex: %.1f ms  (%.3f µs/record)"
                         (double sweep) (* 1000.0 (/ (double sweep) recs))))
        (println (format "  ⇒ removed from the node loop at 100M: %.1f min at this per-record cost"
                         (/ (* (/ (double sweep) recs) 100000000) 60000.0)))
        (println "  (the enumerator already proved the handle live; the loop no longer re-reads it)"))
      (finally (disk/close-dir! dir) (rm-rf! dir)))))

;; ---- shared helpers (timestamps, heap occupancy, belief census) --------
;; The nine-step split against a real, already-imported `:disk` store on disk — no
;; generation, no truncation.  This is the true decade point the generated corpus could
;; only approach: an 11.36M-sentex corpus opened cold and settled once.  The daemon that
;; starved earlier settles is off here (`-Dvaelii.disk.sync-ms=0`); the read is otherwise
;; the engine's own `reindex` + `recover` path, timed.

(defn- now-str ^String [] (str (java.time.LocalTime/now)))

(defn- heap-str
  "Used / committed / max heap in GiB — the headroom a run has left, printed at each
  milestone so an OOM downstream still leaves the last good occupancy in the log."
  ^String []
  (let [rt  (Runtime/getRuntime)
        g   (fn [b] (/ (double b) 1073741824.0))
        max (.maxMemory rt) tot (.totalMemory rt) free (.freeMemory rt)]
    (format "heap used %.1f / committed %.1f / max %.1f GiB"
            (g (- tot free)) (g tot) (g max))))

(defn- in-count
  "Sentexes believed `in?` over the whole live set (out = live − in)."
  [kb]
  (let [tms (:tms kb)]
    (reduce (fn [c id] (if (jtms/in? tms id) (inc c) c)) 0 (p/sentex-ids (:records kb)))))

;; ---- mode: taxstats -----------------------------------------------------
;; How context-scoped is the genl relation of a real corpus?  The scoped closure walk
;; (`visible-neighbours`) filters every edge by context-visibility; if the edges are
;; overwhelmingly universal, that filter drops nothing yet pays per edge.  Open → reindex →
;; rebuild-tms → rebuild-taxonomy (no settle), then read the genl relation's context census.

(defn- taxstats-run [^String dir]
  (println (format "%n=== genl context census: %s ===" dir))
  (let [kb (v/open-kb {:records :disk :index :columnar :dir dir :recover? false})]
    (println (format "  [%s] reindex…" (now-str)))
    (reindex/reindex kb)
    (println (format "  [%s] rebuild-tms + rebuild-taxonomy…" (now-str)))
    (rebuild-tms-split! kb)
    (binding [tax/*defer-depths?* true]
      (special/rebuild-taxonomy kb)
      (tax/refresh-beliefs (:taxonomy kb) #(jtms/in? (:tms kb) %)))
    (tax/restore-depths (:taxonomy kb))
    (let [genl    (get (deref (:taxonomy kb)) :genl)
          fwd     (:fwd genl)
          ectxs   (:edge-ctxs genl)
          ccounts (:ctx-counts genl)
          nedges  (reduce + 0 (map count (vals fwd)))
          nilctx  (count (filter (fn [[_ cs]] (some nil? cs)) ectxs))
          setsz   (into (sorted-map) (frequencies (map count (vals ectxs))))
          total-c (reduce + 0 (vals ccounts))]
      (println (format "%n  genl nodes with up-edges : %,d" (count fwd)))
      (println (format "  total genl edges         : %,d" (long nedges)))
      (println (format "  edge-ctxs entries        : %,d" (count ectxs)))
      (println (format "  edges w/ a nil context   : %,d  (universal by the nil rule)" (long nilctx)))
      (println (format "  distinct asserting ctxs  : %,d  (total edge-context incidences %,d)"
                       (count ccounts) (long total-c)))
      (println "  top 15 contexts by genl-edge count:")
      (doseq [[c n] (take 15 (sort-by (comp - val) ccounts))]
        (println (format "    %-34s %,10d  (%.1f%%)" (str c) (long n) (* 100.0 (/ (double n) (max 1 total-c))))))
      (println (format "  edge context-set sizes   : %s" (pr-str setsz))))
    (disk/close-dir! dir)
    (println (format "  [%s] done." (now-str)))))

;; ---- mode: equality (sub-question C) ------------------------------------
;; `recovered-supersessions` re-enters `equiv-class` per equality edge — Σ kᵢ².  Hold the
;; total member count fixed and grow the class size k: equal classes give Σ kᵢ² =
;; (members/k)·k² = members·k, so the cost tracking k *is* the quadratic signature.

(defn- equality-corpus!
  "A `:memory` KB whose only structure is `members` symbols partitioned into classes of
  size `k`, chained by `sameAs`, each member carrying one ground fact so
  `find-sentexes` has something to return."
  [k members]
  (let [kb (v/open-kb {:backend :memory :space 20 :recover? false})]
    (p/clear-records! (:records kb))
    (p/clear-index! (:index kb))
    (let [nclasses (max 1 (quot members k))
          ;; individuals are CapitalCamelCase (no underscore): class c member i → EcNmM
          nm (fn [c i] (symbol (str "Ec" c "m" i)))]
      (v/with-deferred-settle kb
        (dotimes [c nclasses]
          (dotimes [i k]
            (v/assert kb (list 'holds (nm c i)) 'CxEq {:chain? false})
            (when (pos? i)
              (v/assert kb (list 'sameAs (nm c (dec i)) (nm c i)) 'CxEq {:chain? false})))))
      [kb nclasses])))

(defn- equality-run [ks]
  (let [members 6000]
    (println (format "%n── sub-Q C — recovered-supersessions vs class size (≈%,d members held fixed) ──"
                     members))
    (println (format "%-8s %10s %14s %14s %12s" "k" "classes" "recov-supers ms" "refresh-sup ms" "ms/class"))
    (doseq [k ks]
      (let [[kb nclasses] (equality-corpus! k members)]
        (gc!)
        (let [[cands rs-ms] (timed (vec (#'v/recovered-supersessions kb)))
              rf-ms         (ms (special/refresh-supersessions kb cands))]
          (println (format "%-8d %10d %14.1f %14.1f %12.3f"
                           (long k) (long nclasses) (double rs-ms) (double rf-ms)
                           (/ (double rs-ms) nclasses))))
        (p/clear-records! (:records kb))
        (p/clear-index! (:index kb))))
    (println "  Σkᵢ² signature: at fixed membership, recov-supers ms rising ~linearly in k is the quadratic")))

;; ---- main ---------------------------------------------------------------

;; ---- mode: cleanup-preview ----------------------------------------------
;; What would a destructive "make the stored KB consistent" pass remove?  Open →
;; reindex → recover (so belief exists), then enumerate every disbelieved (OUT)
;; sentex and classify it: a clash loser (the disbelieved side of a definitional
;; clash), a superseded premise (a spelling an equality merged away), an
;; unsupported orphan (a stored record no premise and no justification backs — dead
;; weight), or a derived-out (a conclusion whose every support is out/blocked — the
;; excepted conclusions the settle withdraws).  Also dumps the clash nogoods with
;; each side's belief, so the pairs cleanup would resolve are visible.

(defn- cleanup-preview-run [^String dir index-kind]
  (println (format "%n=== cleanup preview: %s (index %s) ===" dir index-kind))
  (let [kb  (v/open-kb {:records :disk :index index-kind :dir dir :recover? false})
        rec (:records kb)
        tms (:tms kb)]
    (println (format "  [%s] reindex…" (now-str)))
    (reindex/reindex kb)
    (println (format "  [%s] recover…" (now-str)))
    (binding [tax/*scoped-memo-budget* (memo-budget)]
      (timed-recover! kb))
    (println (format "  [%s] recovered; scanning belief…" (now-str)))
    (let [ids       (p/sentex-ids rec)
          clashes   (deref (:clashes kb))
          pairs     (:pairs clashes)
          nogoods   (:nogoods clashes)
          clash-ids (into #{} (mapcat identity) pairs)
          outs      (into [] (remove #(jtms/in? tms %)) ids)
          classify  (fn [id]
                      (cond
                        (contains? clash-ids id)        :clash-loser
                        (jtms/premise? tms id)          :superseded-premise
                        (empty? (jtms/supports tms id)) :unsupported-orphan
                        :else                           :derived-out))
          by-cat    (group-by classify outs)
          sen-str   (fn [id] (let [s (p/get-sentex rec id)]
                               (str (pr-str (:sentence s))
                                    (when (:context s) (str " @" (:context s))))))]
      (println (format "%n  sentexes %,d · in %,d · OUT %,d"
                       (count ids) (- (count ids) (count outs)) (count outs)))
      (println (format "  clash nogood pairs: %,d · clash-side handles: %,d"
                       (count pairs) (count clash-ids)))
      (println (format "%n  === OUT by category (what destructive cleanup removes) ==="))
      (doseq [cat [:clash-loser :superseded-premise :unsupported-orphan :derived-out]]
        (println (format "    %-22s %,d" (name cat) (count (get by-cat cat [])))))
      (println (format "%n  === clash nogoods (%,d): each side's belief ===" (count nogoods)))
      (doseq [ng (take 300 (vals nogoods))]
        (println (format "    [%s]" (name (:kind ng))))
        (doseq [id (vec (:nogood ng))]
          (println (format "       %-3s %s" (if (jtms/in? tms id) "IN" "OUT") (sen-str id)))))
      (doseq [cat [:unsupported-orphan :superseded-premise :derived-out]]
        (let [xs (get by-cat cat [])]
          (println (format "%n  === %s (%,d) — sample up to 40 ===" (name cat) (count xs)))
          (doseq [id (take 40 xs)] (println (str "    " (sen-str id)))))))
    (disk/close-dir! dir)
    (println (format "%n  [%s] done." (now-str)))))

;; ---- mode: disjoint-audit -----------------------------------------------
;; Two disjointness pathologies that inflate the clash scan without ever being a
;; real dilemma the way `lex/person` vs `dod_operation` is:
;;   - self-disjoint (T disjoint T): never convicts (`disjointness-test` guards
;;     `not=`), but its non-empty `seps` defeats the `constantly-false` fast path,
;;     so every instance of T — and of every subtype of T — pays the full scan.
;;   - subsumption-contradictory (T disjoint S with T ⊑ S): every instance of T
;;     *is* an S, so it clashes with itself by construction — a whole family of the
;;     86,300 dilemmas from one bad declaration.
;; Open → reindex → rebuild-taxonomy (no settle), then read the disjoint index.

(defn- disjoint-audit-run [^String dir]
  (println (format "%n=== disjoint audit: %s ===" dir))
  (let [kb  (v/open-kb {:records :disk :index :columnar :dir dir :recover? false})
        tax (:taxonomy kb)]
    (println (format "  [%s] reindex…" (now-str)))
    (reindex/reindex kb)
    (println (format "  [%s] rebuild-tms + rebuild-taxonomy…" (now-str)))
    (rebuild-tms-split! kb)
    (binding [tax/*defer-depths?* true]
      (special/rebuild-taxonomy kb)
      (tax/refresh-beliefs (:taxonomy kb) #(jtms/in? (:tms kb) %)))
    (tax/restore-depths tax)
    (let [didx    (:disjoint-index (deref tax))
          types   (keys didx)
          self-ts (filterv (fn [t] (contains? (get didx t) t)) types)
          seen    (volatile! #{})
          subcon  (into []
                        (comp (mapcat (fn [t] (map (fn [s] [t s]) (get didx t))))
                              (keep (fn [[t s]]
                                      (let [k #{t s}]
                                        (when (and (not= t s) (not (contains? @seen k)))
                                          (vswap! seen conj k)
                                          (when (or (contains? (tax/genls-global tax t) s)
                                                    (contains? (tax/genls-global tax s) t))
                                            [t s]))))))
                        types)]
      (println (format "%n  disjoint-declared types      : %,d" (count types)))
      (println (format "  disjoint-index incidences    : %,d" (reduce + 0 (map (comp count val) didx))))
      (println (format "  self-disjoint (T disjoint T) : %,d" (count self-ts)))
      (println (format "  subsumption-contradictory    : %,d  (T disjoint S with T⊑S or S⊑T)" (count subcon)))
      (when (seq self-ts)
        (println (format "%n  === self-disjoint types — each de-optimizes the scan for its down-closure ==="))
        (doseq [t (take 80 (sort-by (fn [t] (- (count (tax/specs-global tax t)))) self-ts))]
          (println (format "    %-42s down-closure(subtypes): %,d" (str t) (long (count (tax/specs-global tax t)))))))
      (when (seq subcon)
        (println (format "%n  === subsumption-contradictory pairs (sample 60) ==="))
        (doseq [[t s] (take 60 subcon)]
          (println (format "    %-36s  disjoint  %s" (str t) (str s))))))
    (disk/close-dir! dir)
    (println (format "%n  [%s] done." (now-str)))))

;; ---- mode: snapshot-verify ----------------------------------------------
;; Prove the belief certificate end to end on the real corpus:
;;   1. full recover → capture belief (the OUT set, keyed by content so it is
;;      stable across the re-open) + the notes (:clashes, :contradictions);
;;   2. dump :complete (belief + notes) and :minimal (belief only) with nippy,
;;      report both sizes, and check the :complete dump round-trips losslessly;
;;   3. re-open fresh and recover with the disjointness scan SKIPPED
;;      (`*skip-constraint-nogoods*`), the :minimal fast path — then assert its
;;      belief equals the full recover's, and time it.
;; The whole thesis in one run: belief is reproducible without the 14-min scan, the
;; notes are the only thing lost, and the dump is small.

(defn- capture-belief
  "The disbelieved sentexes as a content-keyed set `#{[sentence context] …}` — stable
  across a re-open, where raw handles are not."
  [kb]
  (let [recs (:records kb) tms (:tms kb)]
    (into #{}
          (comp (remove #(jtms/in? tms %))
                (keep (fn [id] (when-let [s (p/get-sentex recs id)]
                                 [(:sentence s) (:context s)]))))
          (p/sentex-ids recs))))

(defn- capture-notes
  "The clash notes in a reload-stable, EDN-friendly form: each nogood as its two
  sides' content `{:sides [[sentence context] …] :kind kw :priority n}` — no handles
  (unstable across a re-open) and no justifications (re-derivable from records), which
  is what bloated the raw structure past nippy's guard.  Pure data, so it reads back
  through `clojure.edn`."
  [kb]
  (let [recs (:records kb)
        side (fn [id] (when-let [s (p/get-sentex recs id)] [(:sentence s) (:context s)]))]
    (into []
          (keep (fn [ng]
                  (let [sd (into [] (keep side) (:nogood ng))]
                    (when (= 2 (count sd))
                      {:sides sd :kind (:kind ng) :priority (:priority ng)}))))
          (vals (:nogoods (deref (:clashes kb)))))))

(defn- spit-edn
  "Write `data` as EDN — pretty-printed when `pretty?`, else a single `pr-str` line
  (still valid EDN, greppable, and fast for the large `:complete` payload)."
  [f data pretty?]
  (binding [*print-length* nil *print-level* nil]
    (spit f (if pretty? (with-out-str (pprint/pprint data)) (pr-str data)))))

(defn- resolve-id
  "The handle in `kb` of the sentex whose content is `[sentence context]`, via the
  arg-1 posting index (a handful of candidates), or nil.  Content, not handle, because
  handles are re-allocated on a fresh open."
  [kb [sen ctx]]
  (let [recs (:records kb)
        a1   (when (sequential? sen) (second sen))]
    (when (some? a1)
      (some (fn [h] (let [s (p/get-sentex recs h)]
                      (when (and s (= (:sentence s) sen) (= (:context s) ctx)) (:id s))))
            (p/sentexes-with-arg (:index kb) 1 a1)))))

(defn- snapshot-verify-run [^String dir index-kind]
  (println (format "%n=== snapshot verify: %s (index %s) ===" dir index-kind))
  (let [f-comp (str dir "/belief-complete.edn")
        f-min  (str dir "/belief-minimal.edn")
        out0
        (let [kb (v/open-kb {:records :disk :index index-kind :dir dir :recover? false})]
          (println (format "  [%s] reindex + full recover…" (now-str)))
          (reindex/reindex kb)
          ;; the full/fast A/B holds the budget fixed on both sides, so it reads the
          ;; default rather than the property — the comparison is of recover strategies
          (binding [tax/*scoped-memo-budget* default-memo-budget] (timed-recover! kb))
          (let [out0     (capture-belief kb)
                clashes  (deref (:clashes kb))
                notes    (capture-notes kb)
                minimal  {:out (vec out0)}
                complete {:out (vec out0) :notes notes}]
            (spit-edn f-min minimal true)
            (spit-edn f-comp complete false)
            (println (format "  OUT %,d · clash pairs %,d · notes captured %,d"
                             (count out0) (count (:pairs clashes)) (count notes)))
            (println (format "  :minimal.edn = %,d bytes · :complete.edn = %,d bytes"
                             (.length (io/file f-min)) (.length (io/file f-comp))))
            (println (format "  EDN round-trip lossless?  :minimal %s · :complete %s"
                             (= minimal  (edn/read-string (slurp f-min)))
                             (= complete (edn/read-string (slurp f-comp)))))
            (disk/close-dir! dir)
            out0))]
    (println (format "%n  [%s] fast reload — recover with the disjointness scan SKIPPED…" (now-str)))
    (let [kb2 (v/open-kb {:records :disk :index index-kind :dir dir :recover? false})]
      (reindex/reindex kb2)
      (let [[_ fast-ms] (timed (binding [tax/*scoped-memo-budget*        default-memo-budget
                                         settle/*skip-constraint-nogoods* true]
                                 (timed-recover! kb2)))
            out1 (capture-belief kb2)]
        (println (format "  fast recover %.0f ms (%.2f min) — clashes now %,d"
                         (double fast-ms) (/ (double fast-ms) 60000.0)
                         (count (:pairs (deref (:clashes kb2))))))
        (println (format "  belief reproduced WITHOUT the scan? %s   (fast OUT %,d vs full OUT %,d)"
                         (= out0 out1) (count out1) (count out0)))
        (when (not= out0 out1)
          (println (format "    only in full recover: %s" (vec (take 8 (set/difference out0 out1)))))
          (println (format "    only in fast reload : %s" (vec (take 8 (set/difference out1 out0))))))
        (disk/close-dir! dir)))
    ;; --- pass 3: read-only WARM reload — rebuild-tms + taxonomy (the ~5-min floor),
    ;; then force belief from the :minimal.edn certificate, running NO settle.  This is
    ;; the aggressive path the tiny file is for: labels are forced (exception mechanisms
    ;; are not reinstalled, so it is read-only), and the whole clash + exception
    ;; derivation is skipped.
    (println (format "%n  [%s] warm reload — structural rebuild only, then force belief from EDN…" (now-str)))
    ;; `:tms :reference` on purpose: this pass forces the OUT set by poking the TMS state
    ;; atom directly (`.-state` below), which only the atom-backed `RefTms` carries — the
    ;; default `:dense` TMS has no such field, so on it the force step throws.
    (let [kb3 (v/open-kb {:records :disk :index index-kind :dir dir :recover? false :tms :reference})]
      (reindex/reindex kb3)
      (let [[_ rebuild-ms]
            (timed (do (rebuild-tms-split! kb3)
                       (binding [tax/*defer-depths?* true]
                         (special/rebuild-taxonomy kb3)
                         (tax/refresh-beliefs (:taxonomy kb3) #(jtms/in? (:tms kb3) %)))
                       (tax/restore-depths (:taxonomy kb3))))]
        (println (format "  structural rebuild (no settle) %.0f ms (%.2f min) — natural OUT %,d"
                         (double rebuild-ms) (/ (double rebuild-ms) 60000.0) (count (capture-belief kb3))))
        (try
          (let [want (:out (edn/read-string (slurp f-min)))
                [ids force-ms] (timed (into [] (keep #(resolve-id kb3 %)) want))
                st   (.-state ^vaelii.impl.jtms.RefTms (:tms kb3))]
            (swap! st update :in (fn [in] (reduce disj in ids)))
            (let [out3 (capture-belief kb3)]
              (println (format "  resolved %,d / %,d handles in %.0f ms; forced OUT"
                               (count ids) (count want) (double force-ms)))
              (println (format "  belief matches full recover? %s   (warm OUT %,d vs full OUT %,d)"
                               (= out0 out3) (count out3) (count out0)))
              (when (not= out0 out3)
                (println (format "    only in full: %s" (vec (take 6 (set/difference out0 out3)))))
                (println (format "    only in warm: %s" (vec (take 6 (set/difference out3 out0))))))))
          (catch Throwable t
            (println (format "  force-belief step FAILED: %s" (.getMessage t)))))
        (disk/close-dir! dir))))
  (println (format "%n  [%s] done." (now-str))))

(defn- show-belief-run [^String npy]
  (let [data (nippy/thaw-from-file npy)
        out  (:out data)
        edn  (str npy ".edn")]
    (println (format "%n=== belief certificate: %s ===" npy))
    (println (format "  OUT entries: %,d" (count out)))
    (spit-edn edn {:out (vec (sort-by pr-str out))} true)
    (println (format "  wrote human-readable EDN: %s (%,d bytes)" edn (.length (io/file edn))))
    (println "  --- disbelieved sentexes (first 30, sorted) ---")
    (doseq [[sen ctx] (take 30 (sort-by pr-str out))]
      (println (format "    %s  @%s" (pr-str sen) ctx)))))

;; ---- mode: beliefcert ---------------------------------------------------
;; The belief certificate end to end against the real store, through the *production*
;; `core/recover` (not the unrolled `timed-recover!` — the certificate is consulted inside
;; `recover` itself).  Pass 1 mints it: a full recover, clash scan and all, writes the
;; stamp.  Pass 2 reopens cold and takes the certified fast path.  The two beliefs must
;; agree, and the two recover times are the saving.  One JVM, so pass 2's records are warm
;; in the OS cache — the honest shape of a restart, and it isolates the delta to the one
;; pass the fast path drops: the definitional-clash scan.

(defn- clash-pairs [kb] (count (:pairs (some-> (:clashes kb) deref))))

(defn- belief-census
  "[in out] over the whole live set — belief and its sparse complement."
  [kb]
  (let [n (count (p/sentex-ids (:records kb))) in (in-count kb)]
    [in (- n in)]))

(defn- beliefcert-run [^String dir index-kind]
  (System/setProperty "vaelii.belief.snapshot" "true")
  (println (format "%n=== belief certificate: %s (index %s) ===" dir index-kind))
  (binding [tax/*scoped-memo-budget* (memo-budget)]
    ;; ---- PASS 1: mint (a full recover writes the certificate) ----
    (println (format "  [%s] PASS 1 mint — open cold" (now-str)))
    (let [kb1   (v/open-kb {:records :disk :index index-kind :dir dir :recover? false})
          nsent (count (p/sentex-ids (:records kb1)))]
      (println (format "  records: %,d sentexes" (long nsent)))
      (println (format "  usable? before mint: %s (expect false — no certificate yet)"
                       (bs/usable? (:records kb1))))
      (gc!)
      (let [[_ ix1] (timed (reindex/reindex kb1))]
        (println (format "  reindex %.2f min — %s" (/ ix1 60000.0) (heap-str)))
        (gc!)
        (println (format "  [%s] recover (full, mints certificate)…" (now-str)))
        (let [[_ rc1]   (timed (v/recover kb1))
              [in1 out1] (belief-census kb1)
              cp1       (clash-pairs kb1)
              meta      (bs/read-meta (:records kb1))]
          (println (format "  MINT  recover %.2f min · clash-pairs %,d · in? %,d · out %,d — %s"
                           (/ rc1 60000.0) (long cp1) (long in1) (long out1) (heap-str)))
          (println (format "  certificate: clean? %s · out-count %,d · clash-count %,d · clash-losers %,d"
                           (:clean? meta) (long (:out-count meta)) (long (:clash-count meta))
                           (long (:clash-losers meta))))
          (disk/close-dir! dir)
          (gc!)
          ;; ---- PASS 2: fast (the certificate skips the clash scan) ----
          (println (format "%n  [%s] PASS 2 fast — reopen cold" (now-str)))
          (let [kb2 (v/open-kb {:records :disk :index index-kind :dir dir :recover? false})]
            (println (format "  usable? %s (expect true — clean stamp matches records)"
                             (bs/usable? (:records kb2))))
            (let [[_ ix2] (timed (reindex/reindex kb2))]
              (println (format "  reindex %.2f min — %s" (/ ix2 60000.0) (heap-str)))
              (gc!)
              (println (format "  [%s] recover (fast, certificate skips the scan)…" (now-str)))
              (let [[_ rc2]   (timed (v/recover kb2))
                    [in2 out2] (belief-census kb2)
                    cp2       (clash-pairs kb2)]
                (println (format "  FAST  recover %.2f min · clash-pairs %,d · in? %,d · out %,d — %s"
                                 (/ rc2 60000.0) (long cp2) (long in2) (long out2) (heap-str)))
                (disk/close-dir! dir)
                (println "\n  === VERDICT ===")
                (println (format "  belief identical: %s   (in %,d==%,d · out %,d==%,d)"
                                 (= [in1 out1] [in2 out2])
                                 (long in1) (long in2) (long out1) (long out2)))
                (println (format "  recover  full %.2f min → fast %.2f min   (%.2f min saved, %.1f%%)"
                                 (/ rc1 60000.0) (/ rc2 60000.0) (/ (- rc1 rc2) 60000.0)
                                 (if (pos? rc1) (* 100.0 (/ (- rc1 rc2) rc1)) 0.0)))
                (println (format "  clash records: full %,d → fast %,d (the fast path rederives none)"
                                 (long cp1) (long cp2)))))))))))

(defn- default-corpus
  "The corpus directory the store-reading modes default to when given no path.
  A dev-box location — an absolute default could only name whoever wrote it — so it
  comes from $VAELII_RECOVER_CORPUS, resolved per call, and an unset variable is an
  error a run hits rather than a path baked into the source."
  ^String []
  (or (System/getenv "VAELII_RECOVER_CORPUS")
      (throw (ex-info (str "VAELII_RECOVER_CORPUS is unset. Set it to the corpus "
                           "directory these modes read (the :disk store of sentexes), "
                           "or pass the path as the second argument.")
                      {:env "VAELII_RECOVER_CORPUS"}))))

(defn -main [& args]
  (let [mode (or (first args) "decomp")]
    (println (format "recover-phase decomposition — %s" mode))
    (case mode
      "decomp"   (let [sizes (if (next args)
                               (map parse-long (rest args))
                               [100000 500000 1000000])]
                   (doseq [n sizes] (decomp-run n)))
      "fetchfix" (fetchfix-run (or (some-> ^String (second args) parse-long) 300000))
      "taxstats" (taxstats-run (or (second args) (default-corpus)))
      "cleanup-preview" (cleanup-preview-run (or (second args) (default-corpus))
                                             (keyword (or (nth args 2 nil) "columnar")))
      "disjoint-audit" (disjoint-audit-run (or (second args) (default-corpus)))
      "snapshot-verify" (snapshot-verify-run (or (second args) (default-corpus))
                                             (keyword (or (nth args 2 nil) "columnar")))
      "beliefcert" (beliefcert-run (or (second args) (default-corpus))
                                   (keyword (or (nth args 2 nil) "columnar")))
      "show-belief" (show-belief-run (or (second args) (str (default-corpus) "/belief-minimal.npy")))
      "equality" (equality-run (if (next args)
                                 (map parse-long (rest args))
                                 [2 4 8 16 32 64]))
      "all"      (do (doseq [n [100000 500000 1000000]] (decomp-run n))
                     (fetchfix-run 300000)
                     (equality-run [2 4 8 16 32 64]))
      (println (str "unknown mode: " mode)))
    (shutdown-agents)
    (System/exit 0)))

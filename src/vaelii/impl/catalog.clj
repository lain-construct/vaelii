(ns vaelii.impl.catalog
  "What knowledge bases this process can load, and the lifecycle of loading one.

  Everything above the engine assumes it is holding *the* KB.  A browser that lists the
  KBs available, loads one while you watch, and switches to it needs two things the
  engine does not have: a description of a KB that has not been loaded yet, and somewhere
  for a load that takes minutes to run while the pages keep answering.  Those are the two
  halves here.

  **A source** is a KB you could load, as data — a kind, a name, and wherever the content
  comes from.  Six kinds:

  | kind         | content                                             | loader |
  |--------------|-----------------------------------------------------|--------|
  | `:core`      | the CoreContext vocabulary head alone               | `vaelii.impl.core-context` |
  | `:starter`   | the shipped schema-only ontology                    | `vaelii.impl.starter` |
  | `:generated` | synthesized from numbers — types, rules, a fwd mix  | `vaelii.impl.io.generate` |
  | `:corpus`    | a translated sentence corpus (OpenCyc)              | a foreign reader, `:cyc-corpus` |
  | `:dump`      | a vaelii export dump                                | `vaelii.impl.io.import` |
  | `:store`     | an on-disk KB already in vaelii's own format        | opened in place |

  The first three ship in this repo and are always offered.  The last three are **found**:
  each directory on the search path (`VAELII_KB_PATH`, else `./kbs` and `~/.vaelii/kbs`)
  is probed, and what marks it — a corpus `meta.edn`, a dump `meta.edn`, a `records/` +
  `index/` pair — decides its kind.  A `catalog.edn` (`VAELII_KB_CATALOG`, else
  `~/.vaelii/catalog.edn`) names sources outside the search path.  Nothing about a
  machine's paths is baked into the repo.

  **An entry** is a source that has been loaded, or is loading: a KB, a status, and a
  progress reading the loaders report into (`:on-progress`, reported by every loader —
  the corpus reader, `io.import/import-dump` and `io.generate/load-into`).  One load runs at a time, on its
  own thread, and is cancelled by a flag the progress callback throws on — the loaders
  have no other safe interruption point, and an import is not a transaction, so a
  cancelled load leaves the KB holding what had already landed.

  **A KB is readable before it is finished.**  `activate` asks only that an entry hold a
  KB, so the one arriving can be the one every page reads — a corpus is browsable from
  its first thousand sentexes, and a store that opens in seconds is browsable while
  belief is still being rebuilt behind it.  What that costs a reader is completeness, not
  correctness, and `active-caveat` is what says so.

  **And a KB can go back out.**  `export-entry!` writes a loaded one as an export dump on
  the same thread discipline a load runs on, which closes the loop: a dump written under
  the search path is a `:dump` source the moment its `meta.edn` lands, so exporting and
  reloading needs nothing outside this namespace.

  **Unloading never deletes an on-disk KB.**  A memory-backed entry has its stores
  cleared (they would otherwise hold the corpus for the life of the JVM); a disk-backed
  one is *closed* — the file lock released, the directory left exactly as it was.  The
  same directory can then be loaded again, or opened by another process."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.disk.backend :as disk]
            [vaelii.impl.foreign :as foreign]
            [vaelii.impl.io.generate :as generate]
            [vaelii.impl.io.import :as import]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.starter :as starter])
  (:import (java.io File)))

;; ---- the shipped sources -------------------------------------------------

(def built-in
  "The sources that need no files beyond the ones in this repo.  `:options` is what the
  UI offers per source, as data: each entry is a form control, and `load-source` reads
  the same keys back out of the params map."
  [{:id      "core"
    :kind    :core
    :name    "Core vocabulary"
    :blurb   "CoreContext alone — the predicates the engine interprets, and nothing else."
    :scale   "~200 sentexes"
    :options [{:key :chain? :type :flag :label "Forward-chain after loading" :default false}]}
   {:id      "starter"
    :kind    :starter
    :name    "Starter ontology"
    :blurb   "The shipped schema: the vocabulary head, the definitional upper band, and the middle theories. No individuals."
    :scale   "~1.2k sentexes"
    :default? true
    :options [{:key :chain? :type :flag :label "Forward-chain after loading" :default false}]}
   {:id      "generated"
    :kind    :generated
    :name    "Generated corpus"
    :blurb   "A synthetic KB of a chosen shape — types, individuals, rules, a forward/backward mix — deterministic in its seed."
    :scale   "as large as you ask for"
    :repeat? true                                        ; loadable many times over, at different shapes
    :options (concat
              [{:key :base :type :choice :label "Base vocabulary" :default "core"
                :choices [["core" "Core vocabulary"] ["starter" "Starter ontology"]]}]
              (for [k generate/knobs] (assoc k :type :slider))
              [{:key :seed :type :number :label "Seed" :default 1 :min 0 :max 1000000}
               {:key :chain? :type :flag :label "Forward-chain after loading" :default false}
               {:key :max-derivations :type :number :label "Derivation cap" :default 100000
                :min 1000 :max 100000000 :step 1000
                :help "chaining is by far the longest phase of a chained load — this is what bounds it (a run overshoots by the last datum's fan-out)"}])}])

(def ^:private corpus-options
  [{:key :profile :type :choice :label "Profile" :default "ontology"
    :choices [["ontology" "Ontology (drops the lexical layers)"]
              ["core" "Core (Cyc's own upper vocabulary)"]
              ["full" "Full (everything, including natural language)"]]}
   {:key :dir :type :path :label "Target directory" :default ""
    :help "empty loads into memory; a path makes it a durable :disk KB"}
   {:key :bulk? :type :flag :label "Bulk load (skip the per-fact checks)" :default false}
   {:key :chain? :type :flag :label "Forward-chain after loading" :default false}
   ;; Bounded for the reason the generator's is, and harder: a generated KB's layer count
   ;; bounds its own chain, and a corpus of a million assertions has nothing playing that
   ;; part, so the cap is the whole bound.
   {:key :max-derivations :type :number :label "Derivation cap" :default 100000
    :min 1000 :max 100000000 :step 1000
    :help "chaining a corpus is by far the longest thing a load can do — this is what bounds it, and a run that hits it is reported as truncated"}])

;; `recover` rebuilds two things, not one — the JTMS *and* the cached taxonomy — so
;; skipping it costs more than belief.  A dump loaded without it has no genl or
;; genlContext closure at all: `types` and `contexts` are empty, `genls` answers only the
;; term it was asked about, and the ontology page has nothing to draw.  Measured on the
;; 1.1M-sentex OpenCyc dump: off gives 0 types and 0 contexts, on gives 125,385 and
;; 13,196.  The flag has to say that, or an operator reads "not belief-queryable", leaves
;; it off, and concludes the KB imported wrong.
(def ^:private dump-options
  [{:key :belief? :type :flag :label "Rebuild belief and the taxonomy (slow — a JTMS node per sentex)"
    :default false
    :help "off stores and indexes everything but leaves the TMS and the genl/genlContext closures empty: findable by term and countable, but no type hierarchy and no belief-filtered query"}
   {:key :dir :type :path :label "Target directory" :default ""
    :help "empty loads into memory; a path makes it a durable :disk KB"}])

(def ^:private store-options
  [{:key :recover? :type :flag :label "Recover belief and the taxonomy on open (slow)" :default false
    :help "off opens the records and index as they stand: no genl/genlContext closure, and belief-filtered queries answer nothing"}])

;; ---- discovery -----------------------------------------------------------

(defn- file-at ^File [dir & parts] (apply io/file dir parts))

(defn- readable-edn
  "`f` read as EDN, or nil — a malformed or unreadable file makes a directory *not* a
  source rather than an error, since discovery runs over directories nobody promised
  anything about."
  [^File f]
  (when (.isFile f)
    (try (edn/read-string (slurp f)) (catch Exception _ nil))))

(defn classify
  "The kind of KB in directory `d`, or nil.  Reads the marker each writer leaves: a
  corpus's `meta.edn` carries the context order it was written in, a dump's carries a
  `:format-version`, and a vaelii `:disk` store is a `records/` + `index/` pair."
  [^File d]
  (when (.isDirectory d)
    (let [m (readable-edn (file-at d "meta.edn"))]
      (cond
        (and (map? m) (:context-order m))                                :corpus
        (and (map? m) (or (:format-version m) (:variant m)))             :dump
        (and (.isDirectory (file-at d "records"))
             (.isDirectory (file-at d "index")))                         :store))))

(defn- corpus-scale
  "How big a found corpus says it is — from the report its writer left beside it, which
  is the only thing that knows before a load."
  [^File d]
  (when-let [r (readable-edn (file-at d "report.edn"))]
    {:sentences (:sentences r) :contexts (:contexts r)}))

(defn- dump-scale
  "What a found dump says it holds, and **whose** it is.  The two dialects spell the
  second count differently — a pure dump has justifications where an engine dump has
  deductions — and the dialect decides how much re-canonicalization an import faces, so
  a card that did not name it would leave the operator guessing at the slow part.

  `:index?` says the dump carries its index as well.  That is a claim about what is on
  disk, never a promise it will be used: the importer replays those entries only if it
  can prove they describe the records beside them, and rebuilds otherwise."
  [^File d]
  (when-let [m (readable-edn (file-at d "meta.edn"))]
    {:sentences (:sentex-count m)
     :supports  (or (:justification-count m) (:deduction-count m))
     :index?    (= :records+index (:variant m))
     :dialect   (if (= :vaelii/export (:format m)) :pure :engine)}))

(defn- du
  "Bytes on disk under `d`, or nil.  A store carries no count of what it holds, so its
  size on disk is the honest thing to show instead."
  [^File d]
  (when (.isDirectory d)
    (reduce + 0 (map #(.length ^File %) (filter #(.isFile ^File %) (file-seq d))))))

(defn human-bytes
  "A byte count as something to read at a glance.  Public because the browser shows byte
  counts of its own (a KB's estimated footprint, the heap) and there is no reason for two
  spellings of the same figure."
  [n]
  (cond (nil? n)        nil
        (< n 1048576)   (format "%.0f kB" (/ (double n) 1024))
        (< n 1073741824) (format "%.0f MB" (/ (double n) 1048576))
        :else            (format "%.1f GB" (/ (double n) 1073741824.0))))

(defn- discovered-source
  "A source map for the KB directory `d`, or nil when it holds none.

  A found KB is offered whether or not this build has a reader for it: a corpus and a
  foreign-dialect dump each need one that ships as a plugin rather than in-tree
  (`vaelii.impl.foreign`), and the honest answer to \"I cannot read this\" is a load that
  fails saying so, not a KB that silently stops being listed."
  [^File d]
  (when-let [kind (classify d)]
    (let [name* (.getName d)
          path  (.getAbsolutePath d)]
      (merge {:id (str (clojure.core/name kind) ":" name*)
              :kind kind
              :name name*
              :path path
              :found? true}
             (case kind
               :corpus (let [{:keys [sentences contexts]} (corpus-scale d)]
                         {:blurb (str "A translated sentence corpus"
                                      (when contexts (str " over " contexts " contexts")) ".")
                          :scale (if sentences (str (format "%,d" (long sentences)) " sentences")
                                     (human-bytes (du d)))
                          :total sentences
                          :options corpus-options})
               :dump   (let [{:keys [sentences supports dialect index?]} (dump-scale d)]
                         {:blurb (str (if (= :pure dialect)
                                        "A vaelii export dump, in our own dialect"
                                        "An engine-dialect dump, re-canonicalized on the way in")
                                      (when supports
                                        (str " — " (format "%,d" (long supports))
                                             (if (= :pure dialect) " justifications" " deductions")))
                                      (when index? ", with its index")
                                      ".")
                          :dialect dialect
                          :index?  index?
                          :scale (if sentences (str (format "%,d" (long sentences)) " sentexes")
                                     (human-bytes (du d)))
                          :total sentences
                          :options dump-options})
               :store  {:blurb "An on-disk vaelii KB, opened in place — no import, no copy."
                        :scale (human-bytes (du d))
                        :options store-options})))))

(defn search-path
  "The directories discovery walks: `VAELII_KB_PATH` (`:`-separated) when set, else the
  `vaelii.kb.path` system property, else `./kbs` and `~/.vaelii/kbs`.  A path entry that
  *is* a KB directory counts as one source; otherwise its children are probed, one level
  down.  (The property mirrors `vaelii.disk.dir`, and is what a test sets — a JVM cannot
  change its own environment.)"
  []
  (if-let [p (or (System/getenv "VAELII_KB_PATH") (System/getProperty "vaelii.kb.path"))]
    (remove str/blank? (str/split p #":"))
    [(str (System/getProperty "user.dir") "/kbs")
     (str (System/getProperty "user.home") "/.vaelii/kbs")]))

(defn- catalog-file ^File []
  (io/file (or (System/getenv "VAELII_KB_CATALOG")
               (System/getProperty "vaelii.kb.catalog")
               (str (System/getProperty "user.home") "/.vaelii/catalog.edn"))))

(defn- configured-sources
  "Sources named by the catalog file: a vector of `{:id :name :path}` maps, each of which
  may state its `:kind` or leave it to be classified from what is at `:path`.  This is
  how a KB outside the search path is offered — and the only place a machine's own paths
  live, since the repo holds none."
  []
  (let [f (catalog-file)]
    (when-let [entries (readable-edn f)]
      (for [e entries
            :when (and (map? e) (:path e))
            :let  [d (io/file (:path e))
                   found (discovered-source d)]]
        (merge (or found {:id (str "missing:" (:path e))
                          :kind (:kind e :store)
                          :scale "not found"
                          :blurb (str "Nothing readable at " (:path e) ".")
                          :missing? true
                          :options []})
               (select-keys e [:id :name :blurb :kind :options :load]))))))

(defn sources
  "Every KB this process can load, built-ins first: the shipped ontologies and the
  generator, then whatever the catalog file names, then whatever the search path holds.
  Recomputed per call — dropping a corpus into a search-path directory makes it appear on
  the next page load, with no restart."
  []
  (let [found (for [p (search-path)
                    :let [d (io/file p)]
                    :when (.isDirectory d)
                    d2 (if (classify d) [d] (sort-by #(.getName ^File %) (.listFiles d)))
                    :let [s (discovered-source d2)]
                    :when s]
                s)]
    (into [] (->> (concat built-in (configured-sources) found)
                  (reduce (fn [[seen acc] s]                ; first spelling of an id wins
                            (if (contains? seen (:id s))
                              [seen acc]
                              [(conj seen (:id s)) (conj acc s)]))
                          [#{} []])
                  second))))

(defn source
  "The source with this id, or nil."
  [id]
  (first (filter #(= id (:id %)) (sources))))

;; ---- the registry --------------------------------------------------------
;;
;; One atom holds every loaded (and loading) KB, which of them is active, and the next
;; free memory space pair.  A memory-backed KB is keyed by space number for the life of
;; the JVM (`vaelii.impl.memory`), so two resident KBs must be given different ones —
;; and the numbers below start well clear of the block the test suite owns.

(def ^:private first-space 100)

(defonce ^:private state (atom {:active nil :entries {} :order [] :next-space first-space}))

(defn- now [] (System/currentTimeMillis))

(defn- claim-spaces!
  "The next free `[record-space index-space]` pair."
  []
  (let [s (:next-space (swap! state update :next-space + 2))]
    [(- s 2) (- s 1)]))

(defn- put-entry! [key f]
  (swap! state update-in [:entries key] f)
  key)

(defn entry
  "One entry, whole (`:kb` included) — for a caller that wants the KB itself."
  [key]
  (get-in @state [:entries key]))

(defn- view
  "An entry as something safe to render or send: the KB, the thread and the cancel flag
  dropped, elapsed time filled in.

  `:kb?` survives the dropping because it is what decides whether an entry can be read
  at all — a load registers before it opens anything, and until then there is no KB to
  activate however healthy the entry looks."
  [e]
  (when e
    (-> (dissoc e :kb :future :cancel)
        (assoc :elapsed-ms (- (or (:finished e) (now)) (:started e))
               :kb?        (some? (:kb e))))))

(defn entries
  "Every entry, in load order, as views."
  []
  (let [{:keys [entries order]} @state]
    (into [] (keep #(view (get entries %))) order)))

(defn active
  "The key of the active entry, or nil."
  []
  (:active @state))

(defn active-entry [] (view (entry (active))))

(defn in-process?
  "Does entry `key` hold a KB in *this* JVM?  A KB is a map with a record store in it; an
  attached daemon is registered as an entry too, and its KB is somewhere else — which is
  why `stats` and `footprint` have nothing to say about one, and why an export of one is
  written on that daemon's host rather than here."
  [key]
  (boolean (:records (:kb (entry key)))))

(defn active-kb
  "The KB the browser should be reading, or nil when nothing is loaded."
  []
  (:kb (entry (active))))

(defn loading?
  "Is a load running?  One runs at a time: they are minutes long and memory-hungry, and
  two at once would make each other's timings meaningless."
  []
  (boolean (some #(= :loading (:status %)) (vals (:entries @state)))))

(defn holder
  "A deref-able that always yields the KB to read — the active entry's, or `fallback`
  when nothing is loaded.  This is what the browser is built against: `app` holds one of
  these instead of a KB, so activating another entry re-points every page at once."
  [fallback]
  (reify clojure.lang.IDeref
    (deref [_] (or (active-kb) fallback))))

;; ---- stats ---------------------------------------------------------------

(defn stats
  "The headline counts for a loaded KB.  `term-count` is one set-size read and the
  context sizes are one each, so this is cheap even on a corpus of millions — deliberately
  so, since it runs every time the page lists the entries.

  Nil for anything that is not an in-process KB (an attached daemon is registered as an
  entry too, and its counts are the daemon's to report)."
  [kb]
  (when (:records kb)
    (try
      {:contexts (count (v/contexts kb))
       :sentexes (v/sentex-count kb)
       :types    (count (v/types kb))
       :terms    (v/term-count kb)}
      (catch Exception e
        {:error (.getMessage e)}))))

;; ---- memory --------------------------------------------------------------
;;
;; Two different kinds of number, deliberately kept apart.  `heap` is a **measurement**
;; of the whole JVM — every KB in this process, the browser itself, and whatever garbage
;; has not been collected yet, in one figure that cannot be attributed to anybody.
;; `footprint` is an **estimate** for one KB, and the only way to attribute anything: the
;; alternative is to unload it and diff the heap, which is not a thing a page can do to a
;; KB somebody is reading.

(def resident-bytes-per-sentex
  "What one stored sentex costs in RAM, per resident component — the coefficients
  `footprint` multiplies out.  Measured on a real-assert load through `bench-scale` and
  `bench-memory`; resident size is linear in
  the sentex count (one record, one index path and one node per sentex, and trie prefix
  sharing only *reduces* the per-sentex cost), which is what makes a single coefficient
  the right shape for an estimate.

  Shape-dependent, and that is the estimate's main error term: a fact of arity 2 with no
  compound arguments indexes at ~1,549 B while a richer one measured ~2,158 B.  The
  leaner figure is used, so a corpus of fat sentences reads low."
  {:index   1549
   :records 279
   :tms     467})

(defn heap
  "What this JVM's heap is doing **right now** — `{:used :committed :max}` in bytes, read
  off the memory MX bean.

  A measurement, not an estimate, but a coarse one: `:used` includes garbage that has not
  been collected, so it drifts up between collections and drops without anything being
  freed.  Read it as the shape of the curve, not as a number to subtract KBs from."
  []
  (let [u (.getHeapMemoryUsage (java.lang.management.ManagementFactory/getMemoryMXBean))]
    {:used      (.getUsed u)
     :committed (.getCommitted u)
     :max       (let [m (.getMax u)] (when (pos? m) m))}))

(defn footprint
  "An estimate of what the KB in entry `key` costs in RAM, by component:
  `{:sentexes :index :records :tms :total :estimated? true}` (bytes), or nil for an entry
  with no in-process KB.

  Cheap by construction, because this runs on every render of a page that polls: the
  sentex count is the trie's own root count (O(1)) and the belief check is one `first`
  over the network's datums.  Nothing is walked, and nothing is measured — see
  `resident-bytes-per-sentex` for where the coefficients come from and how wrong they
  can be.

  Two adjustments make it a statement about *this* KB rather than about a generic one:
  a `:disk` KB pages its records, so the record term is dropped (what stays resident is
  the bounded hot-record LRU, which does not grow with the corpus), and a KB loaded
  without belief — an import with `:belief? false`, a store opened without `:recover?` —
  has no truth-maintenance network at all, so that term goes too.

  Nil for an entry that is not an in-process KB, as `stats` is: an attached daemon holds
  its corpus in *another* process, so nothing here is about this one's memory — and asking
  it would be a round trip per render."
  [key]
  (let [e  (entry key)
        kb (:kb e)]
    (when-let [n (when (:records kb) (try (v/sentex-count kb) (catch Exception _ nil)))]
      (let [paged?   (= :disk (:backend (:where e)))
            belief?  (boolean (first (jtms/datums (:tms kb))))
            {:keys [index records tms]} resident-bytes-per-sentex
            parts    {:index   (* n index)
                      :records (if paged? 0 (* n records))
                      :tms     (if belief? (* n tms) 0)}]
        (assoc parts
               :sentexes   n
               :paged?     paged?
               :belief?    belief?
               :estimated? true
               :total      (reduce + 0 (vals parts)))))))

(defn predicted-footprint
  "What a source would cost in RAM if it were loaded, in bytes — its own count of what it
  holds put through the same coefficients — or nil for a source that does not know how
  big it is (the generator, whose size is whatever the sliders say).

  A load builds belief and holds its records in RAM unless a directory is named, so this
  is the full three-component figure: the ceiling, not the floor."
  [{:keys [total]}]
  (when (and (number? total) (pos? total))
    (long (* total (reduce + 0 (vals resident-bytes-per-sentex))))))

(defn memory
  "The memory picture the browser shows: the JVM heap as measured, every loaded entry's
  estimated footprint, and their sum."
  []
  (let [fps (into [] (keep (fn [k]
                             (when-let [f (footprint k)]
                               (assoc f :key k :name (:name (entry k)))))
                           (:order @state)))]
    {:heap    (heap)
     :entries fps
     :total   (reduce + 0 (map :total fps))}))

;; ---- loading -------------------------------------------------------------

(def ^:private cancelled ::cancelled)

(defn- progress-fn
  "The `:on-progress` callback handed to a loader: record where the load is, and throw
  when the entry has been asked to stop.  Throwing is the whole cancellation mechanism —
  a loader is a tight assert loop with no other point at which stopping is safe."
  [key cancel]
  (fn [p]
    (when @cancel (throw (ex-info "load cancelled" {:type cancelled})))
    (swap! state update-in [:entries key :progress]
           (fn [old] (merge old (assoc p :at (now)))))
    nil))

(defn- open-kb-for
  "The KB an entry loads into: an in-memory one over a freshly claimed space pair, or —
  when the params name a directory — a durable `:disk` one there.  Returns
  `[kb where]`, `where` being what `unload!` needs to take it down again."
  [{:keys [dir]}]
  (if (str/blank? (str dir))
    (let [[r i] (claim-spaces!)]
      [(v/open-kb {:backend :memory :record-space r :index-space i :recover? false})
       {:backend :memory :spaces [r i]}])
    [(v/open-kb {:backend :disk :dir (str dir) :recover? false})
     {:backend :disk :dir (str dir)}]))

(defn- check-readable!
  "Refuse a store whose records do not come back as sentexes.

  A record is frozen with its class name in it, so a store whose frames name a class this
  build does not resolve thaws to nippy's `{:nippy/unthawable …}` placeholder — every read
  succeeds and every answer is empty, the worst way for this to go wrong.  One record is
  enough to tell, and an empty store is fine (there is nothing to disagree about)."
  [kb path]
  (when-let [h (first (p/sentex-ids (:records kb)))]
    (let [r (p/get-sentex (:records kb) h)]
      (when-not (:sentence r)
        (throw (ex-info (str "the store at " path " holds records this build cannot read"
                             " — they thaw as " (pr-str (some-> r keys vec))
                             ", not as sentexes.  It was written by a build whose record"
                             " classes differ; re-import it from a dump.")
                        {:type ::unreadable-store :path path}))))))

(defn- chain-asked
  "Forward-chain `kb` when the form asked for it, folding what it derived into `summary`.

  **After** loading, which is what the option says and the only shape that pays: chaining
  per assertion derives against a KB whose rules are half there, costs more, and reaches
  the same fixpoint — so every loader here asserts with `:chain? false` and a chained load
  is one pass at the end.  That is also the only point at which chaining can be *reported*,
  which is why it is a phase of its own, with no total: a fixpoint's agenda grows as it
  derives, so there is nothing for `done` to be a fraction of.

  `:max-derivations` bounds it.  A corpus-sized rule set has no layer count to bound a run
  by the way a generated KB does, so a cap is what stands between a chained load and one
  that never comes back — a truncated run says so in the summary."
  [kb params progress! summary]
  (if-not (:chain? params)
    summary
    (let [note (fn [pending] (if pending
                               (format "derived · %,d on the agenda" (long pending))
                               "forward chaining to a fixpoint"))
          _    (progress! {:phase :chaining :done 0 :total nil :note (note nil)})
          r    (v/forward-chain
                kb (cond-> {:on-progress (fn [{:keys [derived pending]}]
                                           (progress! {:phase :chaining :total nil
                                                       :done (or derived 0)
                                                       :note (note pending)}))}
                     (:max-derivations params) (assoc :max-derivations
                                                      (:max-derivations params))))]
      (assoc summary :derived (:derived r 0) :truncated? (boolean (:truncated? r))))))

(defn- run-load
  "Load `source` into a fresh KB under `params`, reporting through `progress!`.  Returns
  the loader's summary.

  `note-kb!` is called with `[kb where]` the moment the KB exists — *before* anything is
  loaded into it — so a load that then fails or is cancelled still leaves an entry that
  knows what it opened, and `unload!` can release it.  Without that, a cancelled corpus
  load would strand its memory spaces or its file lock with nothing pointing at them."
  [{:keys [kind path]} params progress! note-kb!]
  (let [open! (fn [] (let [[kb where] (open-kb-for params)] (note-kb! kb where) kb))]
    (case kind
      :core     (let [kb (open!)]
                  (progress! {:phase :vocabulary :done 0 :note "CoreContext"})
                  (core-context/load-into kb)
                  (chain-asked kb params progress! {}))
      :starter  (let [kb (open!)]
                  (progress! {:phase :ontology :done 0 :note "the shipped schema"})
                  (starter/load-into kb)
                  (chain-asked kb params progress! {}))
      :generated (generate/load-into (open!) params {:on-progress progress!})
      :corpus   (let [kb (open!)]
                  (progress! {:phase :vocabulary :done 0 :note "CoreContext"})
                  (core-context/load-into kb)
                  ;; the corpus reader ships as a plugin, so it is asked for rather
                  ;; than required (vaelii.impl.foreign).  Its own `:chain?` chains per
                  ;; assertion, which is not what the option offers — `chain-asked` says
                  ;; why the pass belongs at the end
                  (chain-asked
                   kb params progress!
                   ((:load-dir! (foreign/reader! :cyc-corpus))
                    kb path
                    {:profile     (keyword (or (:profile params) "full"))
                     :bulk?       (boolean (:bulk? params))
                     :chain?      false
                     :on-progress progress!})))
      :dump     (import/import-dump (open!) path {:belief?     (boolean (:belief? params))
                                                  :on-progress progress!})
      ;; a store is already a KB — opening it *is* the load.  Opening is not quick at
      ;; scale (the record log is scanned and the index map rebuilt in RAM) and it
      ;; reports nothing while it runs, so say what is happening before going in
      :store    (let [_  (progress! {:phase :open :done 0
                                     :note "scanning the record log and rebuilding the index"})
                      kb (v/open-kb {:backend :disk :dir path :recover? false})]
                  (note-kb! kb {:backend :disk :dir path :attached? true})
                  (check-readable! kb path)
                  (when (:recover? params)
                    (progress! {:phase :recover :done 0 :note "rebuilding belief"})
                    (v/recover kb))
                  {})
      (throw (ex-info (str "unknown KB source kind " (pr-str kind)) {:kind kind})))))

(defn- entry-key
  "The key an entry is filed under: the source id, suffixed when that source can be
  loaded more than once (the generator, at several shapes)."
  [{:keys [id repeat?]}]
  (if-not repeat?
    id
    (str id "#" (inc (count (filter #(str/starts-with? % (str id "#")) (:order @state)))))))

(defn load-source
  "Start loading the source with id `source-id` under `params`, on its own thread.
  Returns the entry key, or throws when another load is already running or the id names
  no source.

  The entry is registered `:loading` before this returns, so the caller can render it
  immediately; `entries` then reports its progress until it settles into `:ready` (the KB
  is queryable, and activated when nothing else is) or `:failed` / `:cancelled`."
  ([source-id] (load-source source-id {}))
  ([source-id params]
   (when (loading?)
     (throw (ex-info "a load is already running" {:type ::busy :active (active)})))
   (let [src (or (source source-id)
                 (throw (ex-info (str "no KB source " (pr-str source-id)) {:type ::unknown-source})))
         key (entry-key src)
         _   (when (entry key)
               (throw (ex-info (str (:name src) " is already loaded — unload it first")
                               {:type ::already-loaded :key key})))
         cancel (atom false)
         started (now)]
     (swap! state (fn [s]
                    (-> s
                        (assoc-in [:entries key]
                                  {:key key :source (dissoc src :options) :name (:name src)
                                   :params params :status :loading :started started
                                   :progress {:phase :starting :done 0 :total (:total src)}
                                   :cancel cancel})
                        (update :order #(vec (distinct (conj % key)))))))
     (let [progress! (progress-fn key cancel)
           note-kb!  (fn [kb where] (put-entry! key #(assoc % :kb kb :where where)))
           f (future
               (try
                 (let [summary (run-load src params progress! note-kb!)
                       kb      (:kb (entry key))]
                   (put-entry! key #(assoc % :status :ready
                                           :summary summary :finished (now)
                                           :stats (stats kb)
                                           :progress (assoc (:progress %) :phase :done)))
                   (swap! state (fn [s] (cond-> s (nil? (:active s)) (assoc :active key))))
                   (trove/log! {:level :info :id ::loaded
                                :msg (str "loaded KB " key) :data summary}))
                 (catch Throwable t
                   (let [c? (= cancelled (:type (ex-data t)))]
                     ;; a cancelled or failed load leaves whatever had landed in its
                     ;; stores; `unload!` is what takes those down
                     (put-entry! key #(assoc % :status (if c? :cancelled :failed)
                                             :error (or (.getMessage t) (str (class t)))
                                             :finished (now)))
                     (when-not c?
                       (trove/log! {:level :error :id ::load-failed
                                    :msg (str "loading KB " key " failed: " (.getMessage t))}))))))]
       (put-entry! key #(assoc % :future f))
       key))))

(defn cancel!
  "Ask a running load to stop at its next progress report.  `!` because what it leaves
  behind is a half-loaded KB — the loaders write as they go and none of them is a
  transaction."
  [key]
  (when-let [c (:cancel (entry key))]
    (reset! c true)
    true))

(defn unload!
  "Take an entry down: cancel it if it is still loading, drop it from the registry, and
  release what it held.

  **A memory-backed KB is cleared** — its stores are keyed by space number and would
  otherwise hold the corpus for the life of the JVM.  **A disk-backed one is closed, not
  cleared**: the file lock is released and the directory is left exactly as it was, so
  unloading an on-disk KB never destroys it.  The `!` is for the memory case, which does."
  [key]
  (when-let [e (entry key)]
    ;; A running load owns the stores this is about to clear or close, so nothing is
    ;; released until its thread has actually stopped.  Cancellation lands at the next
    ;; progress report, and a phase that reports none (opening a large store scans its
    ;; whole record log before it says anything) can outlast the wait — so say the entry
    ;; is still stopping and leave it whole rather than pulling the stores out from under
    ;; a live writer.
    (when (= :loading (:status e))
      (cancel! key)
      (when (and (:future e) (= ::timeout (deref (:future e) 30000 ::timeout)))
        (put-entry! key #(assoc % :status :cancelling
                                :error "still stopping — its loader has not reached a
                                        point at which it can be interrupted"))
        (throw (ex-info (str (:name e) " is still stopping; unload it again in a moment")
                        {:type ::still-stopping :key key}))))
    (let [{:keys [backend dir]} (:where (entry key))]
      (try
        (case backend
          :memory (when-let [kb (:kb (entry key))] (v/clear! kb))
          :disk   (disk/close-dir! dir)
          nil)
        (catch Exception ex
          (trove/log! {:level :warn :id ::unload-problem
                       :msg (str "releasing KB " key ": " (.getMessage ex))}))))
    (swap! state (fn [s]
                   (-> s
                       (update :entries dissoc key)
                       (update :order #(vec (remove #{key} %)))
                       (update :active #(when (not= % key) %)))))
    ;; nothing active but something loaded — fall to the most recent ready entry, so the
    ;; browser is never left pointing at nothing while a KB is sitting right there
    (swap! state (fn [s]
                   (if (:active s)
                     s
                     (assoc s :active (last (filter #(= :ready (:status (get-in s [:entries %])))
                                                    (:order s)))))))
    true))

(defn activate
  "Make entry `key` the one the browser reads.  Anything **holding a KB** can be
  activated, a load still running included; only an entry with no KB yet is refused,
  and that is a statement about there being nothing there rather than about the load.

  A half-loaded KB answers about what has landed, which is a *prefix* and not a wrong
  answer — the ordinary open-world condition this engine is built on, where an absent
  fact never means a false one.  Reading beside the loader is sound for the same reason
  a reader thread beside the writer is: one writer, and every store mutation lands
  atomically (docs/storage.md, the single-writer contract).  What a reader is owed is
  being *told*, which is `active-caveat`'s job and the browser's — not being refused."
  [key]
  (let [e (entry key)]
    (when (:kb e)
      (swap! state assoc :active key)
      true)))

(defn write-blocked?
  "Is `kb` one a loader is still **writing**?

  Reading beside a loader is sound; writing beside one is not.  A store mutation lands
  atomically, so a reader sees a consistent prefix — but two interleaved writers are not
  serializable at all, and this process's one writer is already spoken for while a load
  runs (docs/storage.md, the single-writer contract).  So activating a KB mid-load buys
  a reader everything except the right to change it.

  Asked of the **KB itself** rather than of the active entry, and by identity, because
  those are not the same question: loading a second KB in the background is no reason to
  stop writing to the one on screen, and a caller holding a KB the catalog never heard of
  (a test, an embedding, an `--attach`) is nobody's loader's business."
  [kb]
  (boolean (and kb
                (some (fn [e] (and (#{:loading :cancelling} (:status e))
                                   (identical? kb (:kb e))))
                      (vals (:entries @state))))))

(defn active-caveat
  "What is provisional about the KB the browser is reading, or nil when nothing is.
  `{:key :name :status :progress :belief?}`.

  Two independent reasons an answer can be less than the whole truth, and a reader is
  owed both:

  - the load is **still running** (or stopped part-way), so what is stored is a prefix
    of what was asked for;
  - **belief and the taxonomy are not built**, which `recover` builds together and
    `:belief? false` skips together.  That empties more than queries: with no JTMS every
    believed answer is empty, and with no genl/genlContext closures there is no type
    hierarchy either, so a fully stored KB renders as one with no types and no contexts
    at all.

  The second outlives the first: a store opened without `:recover?` is `:ready` and stays
  that way, and a `:dump` imported with `:belief? false` likewise.  That is why it is
  reported beside the status rather than folded into it — the dangerous case is the one
  that looks finished.  The TMS is what is probed, since the two are built as a pair.

  An empty KB is not beliefless, it is empty; and an entry that is not an in-process KB
  (an attached daemon) has nothing here to report, exactly as `stats` and `footprint`
  have nothing to say about it."
  []
  (let [key (active)
        e   (entry key)
        kb  (:kb e)]
    (when (:records kb)
      (let [n        (try (v/sentex-count kb) (catch Exception _ 0))
            belief?  (or (zero? n) (boolean (first (jtms/datums (:tms kb)))))
            settled? (= :ready (:status e))]
        (when-not (and settled? belief?)
          {:key key :name (:name e) :status (:status e)
           :progress (:progress e) :belief? belief?})))))

;; ---- exporting -----------------------------------------------------------
;;
;; The other direction of the same loop.  A dump this process writes is a *source* it can
;; discover, so exporting and reloading is a round trip that never leaves the browser —
;; which is the whole reason export is here rather than only in the CLI.
;;
;; It runs the way a load runs, and for the same reasons: its own thread (minutes, on a
;; corpus), progress recorded where the panel already looks for it, cancelled by the
;; progress callback throwing (`export!` calls it at each chunk boundary, and there is no
;; other point at which stopping leaves a directory rather than a file half-written).
;; What it is *not* is an entry: an export produces no KB, and filing it as one would put
;; a second handle on a KB somebody could then unload out from under the writer.

(defn export-job
  "The running — or last — export, as something safe to render: the cancel flag and the
  thread dropped, elapsed time filled in.  Nil until something has been exported.

  One slot, not a list.  An export is a job with a report, and the report worth keeping
  is the last one; a finished job stays visible until the next export replaces it, which
  is what lets the panel say where the dump went."
  []
  (when-let [j (:export @state)]
    (-> (dissoc j :cancel :future)
        (assoc :elapsed-ms (- (or (:finished j) (now)) (:started j))))))

(defn exporting?
  "Is an export running?  One at a time, as with loads."
  []
  (= :running (:status (:export @state))))

(defn- export-progress-fn
  "The `:on-progress` callback handed to `export!`: record where it has got to, and throw
  when it has been asked to stop."
  [cancel]
  (fn [p]
    (when @cancel (throw (ex-info "export cancelled" {:type cancelled})))
    (swap! state update-in [:export :progress] (fn [old] (merge old (assoc p :at (now)))))
    nil))

(defn export-entry!
  "Write the KB in entry `key` out as a dump in `dir`, on its own thread, and return the
  job.  `opts` are `vaelii.core/export!`'s (`:variant`, `:compression`).

  Three refusals, each about something an export cannot be correct in the face of:

  - **another export is running.**  One at a time, as with loads.  A *load* is not
    refused, and does not refuse this: a load fills some other KB, and blocking on it
    would be a rule about this process's busyness rather than about the dump.
  - **the entry is not an in-process KB.**  A daemon serves its KB from another host, and
    that is where its dump would be written — so the export belongs to that daemon's own
    surface, not to a form here that would name a path on the wrong machine.
  - **the KB is still loading.**  `export!` walks it record by record with no snapshot to
    walk instead, so a dump of a KB something is still writing is a dump of no single
    state.

  `!` for what a cancelled one leaves behind: a directory holding part of a dump.  It is
  not a *loadable* dump — `meta.edn` is written last and is what `classify` keys on — but
  it is bytes on disk that nothing here will clean up."
  [key dir opts]
  (when (str/blank? (str dir))
    (throw (ex-info "an export needs a destination directory" {:type ::no-destination})))
  (when (exporting?)
    (throw (ex-info "an export is already running" {:type ::export-busy})))
  (let [e  (entry key)
        kb (:kb e)]
    (when-not e
      (throw (ex-info (if key (str "no loaded KB " (pr-str key)) "nothing is loaded to export")
                      {:type ::unknown-entry :key key})))
    (when-not (in-process? key)
      (throw (ex-info (str (:name e) " is served by a daemon, so its dump is written on"
                           " that daemon's own host — export it from there")
                      {:type ::not-in-process :key key})))
    (when (write-blocked? kb)
      (throw (ex-info (str (:name e) " is still loading — a dump of a KB something is"
                           " still writing is a dump of no single state")
                      {:type ::still-loading :key key})))
    (let [cancel (atom false)]
      (swap! state assoc :export
             {:key key :name (:name e) :dir (str dir)
              :variant (:variant opts :records) :status :running :started (now)
              :progress {:phase :starting :done 0} :cancel cancel})
      (let [f (future
                (try
                  (let [summary (v/export! kb (str dir)
                                           (assoc opts :on-progress (export-progress-fn cancel)))]
                    (swap! state update :export merge
                           {:status :done :summary summary :finished (now)
                            :progress {:phase :done :done (:sentexes summary)
                                       :total (:sentexes summary)}})
                    (trove/log! {:level :info :id ::exported
                                 :msg (str "exported KB " key " to " (:dir summary))
                                 :data summary}))
                  (catch Throwable t
                    (let [c? (= cancelled (:type (ex-data t)))]
                      (swap! state update :export merge
                             {:status (if c? :cancelled :failed) :finished (now)
                              :error (or (.getMessage t) (str (class t)))})
                      (when-not c?
                        (trove/log! {:level :error :id ::export-failed
                                     :msg (str "exporting KB " key " failed: "
                                               (.getMessage t))}))))))]
        (swap! state update :export assoc :future f)
        (export-job)))))

(defn cancel-export!
  "Ask a running export to stop at its next chunk boundary.  `!` because what it leaves
  behind is a directory holding part of a dump."
  []
  (when-let [c (:cancel (:export @state))]
    (reset! c true)
    true))

(defn register!
  "File an already-built KB as a `:ready` entry and make it active if nothing else is —
  how the browser's own startup KB, and an attached daemon, get into the list beside the
  ones the catalog loads.

  `opts`: `:where` says what unloading it should release (nil for a KB this process does
  not own — an attached daemon is nobody's to close); `:source` names the source it came
  from, so a KB registered at startup shows as *loaded* rather than being offered again."
  ([key name kb] (register! key name kb nil))
  ([key name kb {:keys [where source]}]
   (swap! state (fn [s]
                  (-> s
                      (assoc-in [:entries key]
                                {:key key :name name :status :ready :kb kb :where where
                                 :source (or source {:kind :registered}) :started (now)
                                 :finished (now) :stats (stats kb) :progress {:phase :done}})
                      (update :order #(vec (distinct (conj % key))))
                      (update :active #(or % key)))))
   key))

(defn reset-registry!
  "Forget every entry, releasing each as `unload!` does, and stop a running export.  For
  a process shutting down and for tests; nothing in the browser calls it."
  []
  (cancel-export!)
  (doseq [k (:order @state)] (unload! k))
  (reset! state {:active nil :entries {} :order [] :next-space first-space}))

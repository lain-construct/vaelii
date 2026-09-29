;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.clasp
  "Subprocess wrapper around the clasp ASP solver.

   Consumes ASPIF text on stdin, returns parsed results as Clojure maps.
   clasp exit codes encode the solve outcome (10=sat, 20=unsat, 30=optimum,
   bitmask combinations) and are NOT error codes — we rely on the JSON
   `Result` field from `--outf=2` and only throw when clasp itself fails
   to run or produces no parseable output.

   The four modes are the ones `vaelii.impl.asp.edge` asks for:
   :label, :all-optima, :classify-true, :classify-supportable.

   Every run is single-threaded under a fixed seed and carries `--solve-limit` from
   `config/asp-solve-limit` when it is positive (`search-args`), so where a search stops
   is a function of the program.  `--time-limit` from `config/asp-time-limit` (0 lifts
   it) is the backstop, and a process still running at `deadline-ms` is killed.  A
   search stopped by either limit is read as `:interrupted` (`stopped-short?`).

   Ownership: `run-clasp` starts the process and is its only owner.  It returns only
   after the process has exited, and it kills the process and every descendant on the
   paths that leave it running: the deadline and a throw out of the wait (an interrupt)."
  (:require
   [cheshire.core :as json]
   [clojure.java.io :as io]
   [clojure.string :as str]
   [vaelii.impl.config :as config])
  (:import
   [java.lang ProcessHandle]
   [java.util.concurrent TimeUnit]))

(def ^{:dynamic true
       :doc "Name (or absolute path) of the clasp executable. Bind to point
   `solve` at a non-default install or a test stub."}
  *clasp-binary* "clasp")

(def ^:private mode-args
  "argv tails for each supported solve mode. The enumerating modes use --opt-mode=optN
   so that brave/cautious enumerations run over optimal models only — atoms present in
   models that pay extra contradiction cost never contaminate the supportable/true
   classification. `:label` uses --opt-mode=opt with -n 0 instead: it wants ONE labeling,
   but must stream every improving witness as the bound descends, so a run cut off by the
   time limit still leaves its best witness in the JSON (read back as `:best-effort`)
   rather than the nothing optN yields before it proves the optimum.  `-n 1` would stop at
   the first, un-optimized witness.  `:sat` is `-n 1`: a program with no objective has
   nothing to improve, and `-n 0` there enumerates every model — so `solve` runs a
   `:label` solve of such a program under `:sat`'s flags (`objective?`)."
  {:label                ["--opt-mode=opt"  "-n" "0"]
   :sat                  ["-n" "1"]
   :all-optima           ["--opt-mode=optN" "-n" "0"]
   :classify-true        ["--opt-mode=optN" "-e" "cautious" "-n" "0"]
   :classify-supportable ["--opt-mode=optN" "-e" "brave"    "-n" "0"]})

(defn- deadline-ms
  "Milliseconds the JVM waits on one clasp process before killing it: the time limit
   plus the larger of the time limit and 10 s, so 120 s at the default.  Nil when
   `config/asp-time-limit` is 0, which lifts both.  clasp stops itself at
   `--time-limit`, so this fires only on a process that did not."
  []
  (let [n (long (config/asp-time-limit))]
    (when (pos? n) (* 1000 (+ n (max n 10))))))

(defn- kill-tree!
  "Kill `p` and every process it started, then wait for `p` to exit.  The descendants
   are read first: once `p` is gone they are no longer its descendants."
  [^Process p]
  (run! #(.destroyForcibly ^ProcessHandle %) (iterator-seq (.iterator (.descendants p))))
  (.destroyForcibly p)
  (.waitFor p))

(defn- run-clasp
  "Run `*clasp-binary*` with `args` and `in` on stdin: `{:exit :out :err}`.

   The process is exec'd directly (no shell), so a missing binary is an IOException,
   never the shell's exit-127 convention.  Both are `:solver-unavailable`: a missing
   binary, and a process still running at `deadline-ms`, which is killed with its
   descendants first.  stdin is written and stdout and stderr read on their own
   threads, so a process that reads nothing or writes more than a pipe buffer cannot
   block the wait."
  [args ^String in]
  (let [^Process p (try
                     (.start (ProcessBuilder. ^java.util.List (into [*clasp-binary*] args)))
                     (catch java.io.IOException e
                       (throw (ex-info (str "clasp binary not found: " (pr-str *clasp-binary*)
                                            " — put clasp on PATH, or bind"
                                            " vaelii.impl.asp.clasp/*clasp-binary* to its path")
                                       {:type :solver-unavailable :binary *clasp-binary*} e))))
        out (future (slurp (.getInputStream p) :encoding "UTF-8"))
        err (future (slurp (.getErrorStream p) :encoding "UTF-8"))
        ms  (deadline-ms)]
    ;; a process that exits without reading all of stdin breaks the pipe; its answer is
    ;; on stdout, and the write has nothing to add
    (future (try (with-open [w (io/writer (.getOutputStream p) :encoding "UTF-8")]
                   (.write w in))
                 (catch java.io.IOException _ nil)))
    (let [exited? (try (if ms
                         (.waitFor p (long ms) TimeUnit/MILLISECONDS)
                         (do (.waitFor p) true))
                       (catch Throwable e (kill-tree! p) (throw e)))]
      (when-not exited?
        (kill-tree! p)
        (throw (ex-info (str "clasp did not exit within " ms " ms (VAELII_ASP_TIME_LIMIT"
                             " plus its grace) and was killed")
                        {:type :solver-unavailable :binary *clasp-binary* :deadline-ms ms})))
      {:exit (.exitValue p) :out @out :err @err})))

(defn- invoke-clasp
  "Run clasp with `argv` and `aspif-text` on stdin. Returns parsed JSON.
   Throws when clasp cannot be run or does not exit by its deadline (`run-clasp`), or
   produces unparseable output — UNSAT is a valid outcome, not an error."
  [argv aspif-text]
  (let [{:keys [exit out err]} (run-clasp (into ["--outf=2"] argv) aspif-text)]
    (if (str/blank? out)
      (throw (ex-info (str "clasp produced no output (exit " exit ") — a solve answers"
                           " JSON on stdout under --outf=2, so an empty body is clasp"
                           " failing to run; its stderr held "
                           (pr-str (str/trim (str err))))
                      {:type :solver-failed :exit exit :err err :argv argv}))
      (try
        (json/parse-string out true)
        (catch Exception e
          (throw (ex-info (str "clasp output does not parse as JSON — a solve runs under"
                               " --outf=2, so a non-JSON body comes from something"
                               " answering in clasp's place; exit " exit ", and the body"
                               " opens " (pr-str (subs out 0 (min 200 (count out)))))
                          {:type :solver-failed :exit exit :out out :err err} e)))))))

(defn- all-witnesses [parsed]
  (or (-> parsed :Call first :Witnesses) []))

(defn- stopped-short?
  "Did clasp stop before its search finished — the solve limit, the time limit, or a
   signal?  None of the three is in `Result`: a run that found a model before it stopped
   still says `SATISFIABLE`, and that model is not the answer the mode asked for.  The
   time limit and a signal are flags beside it; the solve limit sets neither and shows
   only as `More: yes`, a search that did not exhaust its space.  Under `-n 1` (`sat?`)
   a search stops at its first model on purpose and says `More: yes` too, so there it
   stopped short only when it has no model."
  [parsed sat?]
  (boolean (or (some #(= 1 (get parsed (keyword %))) ["TIME LIMIT" "INTERRUPTED"])
               (and (= "yes" (-> parsed :Models :More))
                    (not (and sat? (seq (all-witnesses parsed))))))))

(defn- status-of [parsed sat?]
  (if (stopped-short? parsed sat?)
    :interrupted
    (case (:Result parsed)
      "OPTIMUM FOUND" :optimum
      "SATISFIABLE"   :sat
      "UNSATISFIABLE" :unsat
      :unknown)))

(defn- time-limit-args
  "`--time-limit=N` for a positive `config/asp-time-limit`, nothing for 0."
  []
  (let [n (config/asp-time-limit)]
    (when (pos? n) [(str "--time-limit=" n)])))

(defn search-args
  "The flags under which a solve's search is a function of its program alone: one
   thread, clasp's own default seed (1) stated rather than assumed, and
   `--solve-limit=N` for a positive `config/asp-solve-limit`.  The limit counts
   conflicts, so it stops a search at the same point on any machine, where
   `--time-limit` stops it wherever the machine has got to.  In-process clingo's control
   takes the same flags (`vaelii.impl.asp.clingo`)."
  []
  (let [n (config/asp-solve-limit)]
    (cond-> ["--parallel-mode=1" "--seed=1"]
      (pos? n) (conj (str "--solve-limit=" n)))))

(defn- optimum-costs
  "Full optimum cost VECTOR reported by clasp — one entry per minimize
   priority level (e.g. `[pri1 pri0]`), highest priority first. A
   single-tier program reports `[c]`. Nil for programs with no minimize
   statement, or for UNSAT."
  [parsed]
  (-> parsed :Models :Costs))

(defn- optimum-cost
  "Top-level (highest-priority) optimum cost, or nil. Kept scalar for the
   single-tier common case and for backward compatibility of the public
   `:cost` field."
  [parsed]
  (first (optimum-costs parsed)))

(defn- value-of [witness]
  (vec (or (:Value witness) [])))

(defn- optimal-witnesses
  "Witnesses whose FULL cost vector equals the reported optimum. clasp may
   emit intermediate non-optimal witnesses during the search; we filter
   them. The whole `:Costs` vector is compared rather than its first level,
   because a multi-priority lexicographic program reports one cost per
   level: a single-level compare (`[cost]` against the witness's `:Costs`)
   matches no witness at all once more than one minimize tier is present,
   and `:label` / `:all-optima` then have none to read."
  [parsed]
  (let [costs (optimum-costs parsed)]
    (if (nil? costs)
      (all-witnesses parsed)
      (filter #(= costs (:Costs %)) (all-witnesses parsed)))))

(defn- objective?
  "Does `aspif-text` hold a minimize statement over at least one literal?  ASPIF writes
  one as `2 <priority> <n> <lit w>…`.  Without one every model costs the same, so a
  search for improving models has nothing to improve and enumerates them all."
  [aspif-text]
  (boolean (re-find #"(?m)^2 -?\d+ [1-9]" aspif-text)))

(defn solve
  "Run clasp on `aspif-text` in one of the supported modes.

   Modes:
     :label                — one minimum-cost witness (for labeling output)
     :sat                  — the first witness, for a program with no objective
     :all-optima           — every minimum-cost witness (for inspection)
     :classify-true        — atoms in every minimum-cost witness
     :classify-supportable — atoms in at least one minimum-cost witness

   Returns:
     :status    — :optimum | :sat | :best-effort | :unsat | :interrupted | :unknown
     :atoms     — vector of atom-name strings
     :cost      — optimum cost (nil if no minimize statement or unsat)
     :witnesses — vector of value vectors (only populated for :all-optima)
     :raw       — full parsed JSON (for diagnostics)

   A `:label` solve of a program with no objective runs under `:sat`'s flags: streaming
   improving models there would enumerate every model.

   `:interrupted` is the solve limit (`config/asp-solve-limit`), the time limit
   (`config/asp-time-limit`) or a signal with NO witness to show for it.  A `:label`
   run cut off *after* it had a witness is `:best-effort` instead — that model is a
   valid labeling, its optimality merely unproven — which the imperative `:one` caller
   takes over nothing (`asp.edge/kept-of`); the enumerating modes need a finished
   search, so they stay `:interrupted`."
  [aspif-text mode]
  (let [run    (if (and (= :label mode) (not (objective? aspif-text))) :sat mode)
        argv   (or (mode-args run)
                   (throw (ex-info (str "unknown clasp mode: " (pr-str mode) " — want one of "
                                        (pr-str (vec (sort (keys mode-args)))))
                                   {:type :unknown-option :mismatch :bad-value :mode mode :valid (keys mode-args)})))
        parsed (invoke-clasp (concat argv (search-args) (time-limit-args)) aspif-text)
        status (status-of parsed (= :sat run))]
    (case mode
      (:label :sat)
      (let [best (first (optimal-witnesses parsed))]
        ;; interrupted mid-optimization but a witness is in hand: that model is a valid
        ;; labeling (lowest cost seen, optimality unproven), so hand it back `:best-effort`
        ;; rather than discard it — mirrors the in-process clingo backend.
        {:status (if (and (= :interrupted status) best) :best-effort status)
         :atoms  (value-of best)
         :cost   (optimum-cost parsed)
         :raw    parsed})

      :all-optima
      {:status    status
       :atoms     (value-of (first (optimal-witnesses parsed)))
       :cost      (optimum-cost parsed)
       :witnesses (mapv value-of (optimal-witnesses parsed))
       :raw       parsed}

      (:classify-true :classify-supportable)
      ;; clasp streams intermediate approximations during brave/cautious
      ;; enumeration; the last witness is the converged answer.
      {:status status
       :atoms  (value-of (last (all-witnesses parsed)))
       :cost   (optimum-cost parsed)
       :raw    parsed})))

(defn available?
  "True if the clasp binary can be executed in the current environment.
   Used by tests to skip cleanly when clasp isn't installed."
  []
  (try
    (zero? (long (:exit (run-clasp ["--version"] ""))))
    (catch Exception _ false)))

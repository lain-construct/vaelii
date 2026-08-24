;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.clasp
  "Subprocess wrapper around the clasp ASP solver.

   Consumes ASPIF text on stdin, returns parsed results as Clojure maps.
   clasp exit codes encode the solve outcome (10=sat, 20=unsat, 30=optimum,
   bitmask combinations) and are NOT error codes — we rely on the JSON
   `Result` field from `--outf=2` and only throw when clasp itself fails
   to run or produces no parseable output.

   The four modes match the user-facing reason API in vaelii.impl.asp.reason:
   :label, :all-optima, :classify-true, :classify-supportable.

   Every run carries `--time-limit` from `config/asp-time-limit` (0 lifts it): a
   solve that hits it comes back `Result: UNKNOWN` with `TIME LIMIT: 1`, read here
   as `:interrupted`."
  (:require
   [cheshire.core :as json]
   [clojure.java.shell :as shell]
   [clojure.string :as str]
   [vaelii.impl.config :as config]))

(def ^{:dynamic true
       :doc "Name (or absolute path) of the clasp executable. Bind to point
   `solve` at a non-default install or a test stub."}
  *clasp-binary* "clasp")

(def ^:private mode-args
  "argv tails for each supported solve mode. All modes use --opt-mode=optN
   so that brave/cautious enumerations run over optimal models only — atoms
   present in models that pay extra contradiction cost never contaminate
   the supportable/true classification."
  {:label                ["--opt-mode=optN" "-n" "1"]
   :all-optima           ["--opt-mode=optN" "-n" "0"]
   :classify-true        ["--opt-mode=optN" "-e" "cautious" "-n" "0"]
   :classify-supportable ["--opt-mode=optN" "-e" "brave"    "-n" "0"]})

(defn- invoke-clasp
  "Run clasp with `argv` and `aspif-text` on stdin. Returns parsed JSON.
   Throws only when clasp cannot be run or produces unparseable output —
   UNSAT is a valid outcome, not an error."
  [argv aspif-text]
  (let [{:keys [exit out err]}
        ;; `shell/sh` execs directly (no shell), so a missing binary is an
        ;; IOException here, never the shell's exit-127 convention
        (try
          (apply shell/sh *clasp-binary* "--outf=2"
                 (concat argv [:in aspif-text]))
          (catch java.io.IOException e
            (throw (ex-info (str "clasp binary not found: " *clasp-binary*)
                            {:type :solver-unavailable :binary *clasp-binary*} e))))]
    (if (str/blank? out)
      (throw (ex-info (str "clasp produced no output (exit " exit ")")
                      {:type :solver-failed :exit exit :err err :argv argv}))
      (try
        (json/parse-string out true)
        (catch Exception e
          (throw (ex-info "failed to parse clasp JSON output"
                          {:type :solver-failed :exit exit :out out :err err} e)))))))

(defn- interrupted?
  "Did clasp stop before it finished — the time limit, or a signal?  Reported as flags
   beside `Result` rather than in it: a run that found a model before the limit still
   says `SATISFIABLE`, and that model is not the answer the mode asked for."
  [parsed]
  (boolean (some #(= 1 (get parsed (keyword %))) ["TIME LIMIT" "INTERRUPTED"])))

(defn- status-of [parsed]
  (if (interrupted? parsed)
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

(defn- all-witnesses [parsed]
  (or (-> parsed :Call first :Witnesses) []))

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

(defn solve
  "Run clasp on `aspif-text` in one of the supported modes.

   Modes:
     :label                — one minimum-cost witness (for labeling output)
     :all-optima           — every minimum-cost witness (for inspection)
     :classify-true        — atoms in every minimum-cost witness
     :classify-supportable — atoms in at least one minimum-cost witness

   Returns:
     :status    — :optimum | :sat | :unsat | :interrupted | :unknown
     :atoms     — vector of atom-name strings
     :cost      — optimum cost (nil if no minimize statement or unsat)
     :witnesses — vector of value vectors (only populated for :all-optima)
     :raw       — full parsed JSON (for diagnostics)

   `:interrupted` is the time limit (`config/asp-time-limit`) or a signal: whatever
   atoms ride beside it are a model found on the way, not the answer."
  [aspif-text mode]
  (let [argv (or (mode-args mode)
                 (throw (ex-info (str "unknown clasp mode: " mode)
                                 {:type :unknown-option :mode mode :valid (keys mode-args)})))
        parsed (invoke-clasp (concat argv (time-limit-args)) aspif-text)
        status (status-of parsed)]
    (case mode
      :label
      {:status status
       :atoms  (value-of (first (optimal-witnesses parsed)))
       :cost   (optimum-cost parsed)
       :raw    parsed}

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
    (zero? (:exit (shell/sh *clasp-binary* "--version")))
    (catch Exception _ false)))

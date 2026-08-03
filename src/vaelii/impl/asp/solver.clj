;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.solver
  "Backend selector for vaelii's ASP solver. Callers (reason.clj) use
   `solver/solve`/`solver/available?` so the engine can run the in-process
   clingo backend (default, when libclingo + JNA are present) or fall back to
   the clasp subprocess — without any caller change.

   The clingo backend is loaded LAZILY via requiring-resolve so JNA/libclingo
   stay optional: a plain build (without the `:with-clingo` profile) has no JNA
   on the classpath, the resolve fails cleanly, and the facade falls back to
   clasp. clasp is also the deliberate fallback for long-running daemons, since
   an in-process native crash takes down the whole JVM.

   Select explicitly with -Dvaelii.asp.solver or VAELII_ASP_SOLVER = clingo|clasp.
   Default is auto: prefer in-process clingo when it loads, else clasp."
  (:require
   [clojure.string :as str]
   [vaelii.impl.asp.clasp :as clasp]))

(defn- configured []
  (some-> (or (System/getProperty "vaelii.asp.solver")
              (System/getenv "VAELII_ASP_SOLVER"))
          str/trim str/lower-case keyword))

(defonce ^:private clingo-backend
  ;; {:solve <fn> :available? <fn>} when libclingo loads in this JVM, else nil.
  (delay (try
           (let [solve (requiring-resolve 'vaelii.impl.asp.clingo/solve)
                 cboth (requiring-resolve 'vaelii.impl.asp.clingo/classify-both)
                 avail (requiring-resolve 'vaelii.impl.asp.clingo/available?)]
             (when (avail) {:solve solve :classify-both cboth :available? avail}))
           (catch Throwable _ nil))))

(defonce ^:private clingo-max-program-bytes
  ;; AUTO-mode size cutoff: a plain-ASP ASPIF program longer than this routes to clasp
  ;; even when clingo is loadable, because the in-process win is a fixed saved fork while
  ;; the loss grows with program size. Override with VAELII_CLINGO_MAX_BYTES; an explicit
  ;; VAELII_ASP_SOLVER=clingo uses clingo whatever the size. The measurements, and why
  ;; byte length is the right proxy: docs/asp.md, "Why size picks the backend".
  (delay (or (some-> (System/getenv "VAELII_CLINGO_MAX_BYTES")
                     str/trim not-empty Long/parseLong)
             3000)))

(defn- backend
  "The backend to use ignoring program size: explicit config, else auto (clingo
   when loadable). What `available?` asks; the size-aware routing decision lives
   in `backend-for`."
  []
  (case (configured)
    :clasp  :clasp
    :clingo (if @clingo-backend :clingo :clasp)   ; fall back if unavailable
    (if @clingo-backend :clingo :clasp)))

(defn- choose-backend
  "Pure backend policy. Given the explicit `configured` choice
   (:clasp / :clingo / nil for auto), whether clingo is `available?`, the
   program `nbytes`, and the auto-mode `max-bytes` cutoff, return :clingo or
   :clasp. Explicit config is honored verbatim (clingo falls back to clasp when
   unavailable); AUTO mode picks clingo only for available + small programs.
   Split out from `backend-for` so the policy is unit-testable without a loaded
   libclingo or env juggling."
  [configured available? nbytes max-bytes]
  (case configured
    :clasp  :clasp
    :clingo (if available? :clingo :clasp)
    (if (and available? (<= (long nbytes) (long max-bytes)))
      :clingo
      :clasp)))

(defn- backend-for
  "Backend for a plain-ASP program of `nbytes` in the current environment —
   `choose-backend` applied to the live config, clingo availability, and cutoff.
   In AUTO mode small programs prefer in-process clingo (no fork) and large
   programs prefer clasp (clingo's per-solve slope regresses past the crossover —
   see `clingo-max-program-bytes`)."
  [nbytes]
  (choose-backend (configured) (some? @clingo-backend) nbytes @clingo-max-program-bytes))

(defn solve
  "Solve `aspif-text` in `mode` via the selected backend. Contract identical to
   clasp/solve and clingo/solve. In AUTO mode the backend is chosen per program
   size (`backend-for`): clingo for small programs, clasp for large."
  [aspif-text mode]
  (if (= :clingo (backend-for (count aspif-text)))
    ((:solve @clingo-backend) aspif-text mode)
    (clasp/solve aspif-text mode)))

(defn classify-both
  "Cautious + brave classification of `aspif-text` in one shot. On the clingo
   backend (AUTO routing) the program is loaded ONCE and `solve.enum_mode` is
   switched between the two enumerations; on clasp it is two separate solves.
   Returns `{:cautious <result> :brave <result>}` (each shaped like `solve`).
   Lets `reason/classify-context` avoid a redundant second control_new + load."
  [aspif-text]
  (if (= :clingo (backend-for (count aspif-text)))
    ((:classify-both @clingo-backend) aspif-text)
    {:cautious (clasp/solve aspif-text :classify-true)
     :brave    (clasp/solve aspif-text :classify-supportable)}))

(defn available?
  "True if the selected backend can solve in this environment."
  []
  (if (= :clingo (backend)) true (clasp/available?)))

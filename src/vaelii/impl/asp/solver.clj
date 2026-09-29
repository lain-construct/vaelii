;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.solver
  "Backend selector for vaelii's ASP solver. Callers (`asp.edge`, `asp.label` and
   `asp.solve-context`) use `solver/solve`/`solver/available?` so the engine can run
   the in-process clingo backend (default, when libclingo + JNA are present) or fall
   back to the clasp subprocess — without any caller change.

   The clingo backend is loaded LAZILY via requiring-resolve so JNA/libclingo
   stay optional: a plain build (without the `:with-clingo` profile) has no JNA
   on the classpath, the resolve fails cleanly, and the facade falls back to
   clasp. clasp is also the deliberate fallback for long-running daemons, since
   an in-process native crash takes down the whole JVM.

   Select explicitly with -Dvaelii.asp.solver or VAELII_ASP_SOLVER = clingo|clasp.
   Default is auto: prefer in-process clingo when it loads, else clasp."
  (:require
   [taoensso.trove :as trove]
   [vaelii.impl.asp.clasp :as clasp]
   [vaelii.impl.config :as config]))

(defn- configured [] (config/asp-solver))

(defn- load-clingo
  "`{:solve :classify-both :available?}` when libclingo loads and answers in this JVM,
  else nil."
  []
  (let [solve (requiring-resolve 'vaelii.impl.asp.clingo/solve)
        cboth (requiring-resolve 'vaelii.impl.asp.clingo/classify-both)
        avail (requiring-resolve 'vaelii.impl.asp.clingo/available?)]
    (when (avail) {:solve solve :classify-both cboth :available? avail})))

;; `load-clingo`'s answer once one is reached, else ::unknown.
(defonce ^:private clingo-verdict (atom ::unknown))

;; Whether a `VirtualMachineError` from `load-clingo` has been logged.
(defonce ^:private clingo-vm-error-logged? (atom false))

(defn- clingo-backend
  "`load-clingo`'s answer, memoized for the process.  A throw memoizes nil, logged at
  `:warn`: a namespace, a class or a native library that failed to load fails the same way
  for the life of the JVM.  A `VirtualMachineError` (out of memory, stack overflow) is a
  state of the JVM and not of the install, so it answers nil for this call only, memoizes
  nothing, and is logged the first time."
  []
  (let [v @clingo-verdict]
    (if (not= ::unknown v)
      v
      (locking clingo-verdict
        (let [v @clingo-verdict]
          (if (not= ::unknown v)
            v
            (try (reset! clingo-verdict (load-clingo))
                 (catch VirtualMachineError e
                   (when (compare-and-set! clingo-vm-error-logged? false true)
                     (trove/log! {:level :warn :id ::clingo-load-vm-error :error e
                                  :msg (str "the in-process clingo backend did not load: "
                                            (ex-message e) "; ASP solves go to clasp until"
                                            " a later call loads it")}))
                   nil)
                 (catch Throwable e
                   (trove/log! {:level :warn :id ::clingo-load-failed :error e
                                :msg (str "the in-process clingo backend did not load: "
                                          (ex-message e) "; ASP solves go to clasp")})
                   (reset! clingo-verdict nil)))))))))

;; AUTO-mode size cutoff: a plain-ASP ASPIF program longer than this routes to clasp even
;; when clingo is loadable, because the in-process win is a fixed saved fork while the loss
;; grows with program size. An explicit VAELII_ASP_SOLVER=clingo uses clingo whatever the
;; size. The measurements, and why byte length is the right proxy: docs/asp.md, "Why size
;; picks the backend". Read per call rather than held in a delay, so `config/check!`
;; refuses a bad value at `open-kb` instead of the first solve throwing from a cache.
(defn- clingo-max-program-bytes [] (config/clingo-max-program-bytes))

(defn- backend
  "The backend to use ignoring program size: explicit config, else auto (clingo
   when loadable). What `available?` asks; the size-aware routing decision lives
   in `backend-for`."
  []
  (case (configured)
    :clasp  :clasp
    :clingo (if (clingo-backend) :clingo :clasp)   ; fall back if unavailable
    (if (clingo-backend) :clingo :clasp)))

(defonce ^:private clasp-usable
  ;; probed once per JVM: the binary's presence does not flicker, and `clasp/available?`
  ;; forks a process to answer — a probe per routing decision would cost what the
  ;; routing exists to save
  (delay (clasp/available?)))

(defn- choose-backend
  "Pure backend policy. Given the explicit `configured` choice
   (:clasp / :clingo / nil for auto), whether clingo is `available?`, the
   program `nbytes`, the auto-mode `max-bytes` cutoff, and whether the clasp
   binary can run, return :clingo or :clasp. Explicit config is honored verbatim
   (clingo falls back to clasp when unavailable); AUTO mode picks clingo for
   available + small programs, and past the cutoff hands off to clasp only when
   clasp can actually run — a loadable clingo solving a large program is a cost
   regression, where routing to a binary the machine does not have is a refusal
   `available?` promised would not happen. Split out from `backend-for` so the
   policy is unit-testable without a loaded libclingo or env juggling."
  [configured available? nbytes max-bytes clasp-runs?]
  (case configured
    :clasp  :clasp
    :clingo (if available? :clingo :clasp)
    (if (and available?
             (or (<= (long nbytes) (long max-bytes)) (not clasp-runs?)))
      :clingo
      :clasp)))

(defn- backend-for
  "Backend for a plain-ASP program of `nbytes` in the current environment —
   `choose-backend` applied to the live config, clingo availability, and cutoff.
   In AUTO mode small programs prefer in-process clingo (no fork) and large
   programs prefer clasp (clingo's per-solve slope regresses past the crossover —
   see `clingo-max-program-bytes`)."
  [nbytes]
  (choose-backend (configured) (some? (clingo-backend)) nbytes (clingo-max-program-bytes)
                  @clasp-usable))

(defn solve
  "Solve translated program `{:aspif <text> :stmts <statements>}` in `mode` via the
   selected backend, returning the shape clasp/solve and clingo/solve share. In AUTO
   mode the backend is chosen per program size (`backend-for`, on the ASPIF byte
   length): clingo for small programs, clasp for large. clingo injects `:stmts`
   through the backend accessors; clasp consumes the `:aspif` text."
  [program mode]
  (if (= :clingo (backend-for (count (:aspif program))))
    ((:solve (clingo-backend)) program mode)
    (clasp/solve (:aspif program) mode)))

(defn classify-both
  "Cautious + brave classification of `aspif-text` in one shot. On the clingo
   backend (AUTO routing) the program is loaded ONCE and `solve.enum_mode` is
   switched between the two enumerations; on clasp it is two separate solves.
   Returns `{:cautious <result> :brave <result>}` (each shaped like `solve`).
   Lets `edge/classify-program` avoid a redundant second control_new + load."
  [aspif-text]
  (if (= :clingo (backend-for (count aspif-text)))
    ((:classify-both (clingo-backend)) aspif-text)
    {:cautious (clasp/solve aspif-text :classify-true)
     :brave    (clasp/solve aspif-text :classify-supportable)}))

(defn available?
  "True if the selected backend can solve in this environment.  The clasp answer is
  the once-per-JVM probe, not a fresh fork per ask — routing reads the same delay."
  []
  (if (= :clingo (backend)) true @clasp-usable))

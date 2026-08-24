;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.clingo
  "In-process ASP solver: a JNA binding to the native clingo C API (which
   embeds clasp). Drop-in for `vaelii.impl.asp.clasp/solve` — same
   `(solve aspif-text mode)` contract and return shape — but without the
   subprocess + JSON round-trip.

   Why in-process: it drops the per-solve fork and JSON round-trip the
   subprocess pays, which is the whole win on the small programs
   `vaelii.impl.asp.solver` routes here.

   The four modes map to clingo configuration passed as command-line arguments
   to clingo_control_new (clingo accepts clasp's flags): --opt-mode=optN so
   brave/cautious enumerate over optimal models only, --enum-mode=brave|cautious,
   --models=0|1. Shown atoms come back as the s/c/a label strings vaelii emits
   via ASPIF type-4 show statements; the lexicographic cost vector comes from
   clingo_model_cost.

   Native lib: a system libclingo (brew install clingo) reachable via
   jna.library.path, or an absolute path in -Dvaelii.clingo.lib. Crash isolation
   is lost vs the subprocess — every native return is checked, every solve handle
   is closed in a finally and every Control is freed in one; a malformed program
   throws rather than segfaults.

   The time limit (`config/asp-time-limit`) is not a flag here — libclingo's
   control takes solver options only and refuses `--time-limit` — so each solve runs
   async and is drained through `clingo_solve_handle_wait` with what remains of the
   budget; a solve still running when it runs out is cancelled and reports the
   interrupted bit, read as `:interrupted`."
  (:require [taoensso.trove :as trove]
            [vaelii.impl.config :as config])
  (:import [com.sun.jna NativeLibrary Function Pointer Memory Native]
           [com.sun.jna.ptr PointerByReference IntByReference LongByReference]))

(def ^:dynamic *clingo-lib*
  "Library name (resolved via jna.library.path) or absolute path to libclingo."
  (or (System/getProperty "vaelii.clingo.lib") "clingo"))

(defonce ^:private lib (delay (NativeLibrary/getInstance ^String *clingo-lib*)))

(defn- func ^Function [nm] (.getFunction ^NativeLibrary @lib nm))

(defn- ci [nm & a] (.invokeInt    (func nm) (object-array a)))

(defn- cv [nm & a] (.invokeVoid   (func nm) (object-array a)))

(defn- cp ^Pointer [nm & a] (.invokePointer (func nm) (object-array a)))

(defn- clingo-error []
  (try (when-let [p (cp "clingo_error_message")] (.getString p 0)) (catch Throwable _ nil)))

(defn- chk! [what r]
  (when (zero? r) (throw (ex-info (str "clingo " what " failed: " (clingo-error))
                                  {:type :solver-failed :op what})))
  r)

(defn- cstr ^Memory [s]
  (let [b (.getBytes (str s) "UTF-8") m (Memory. (long (inc (alength b))))]
    (.write m 0 b 0 (alength b)) (.setByte m (long (alength b)) (byte 0)) m))

(defn- ptr-array ^Memory [ptrs]
  (let [m (Memory. (long (* Native/POINTER_SIZE (count ptrs))))]
    (doseq [[i p] (map-indexed vector ptrs)] (.setPointer m (long (* i Native/POINTER_SIZE)) p))
    m))

(def ^:private show-shown   (Integer/valueOf 2))

;; `clingo_solve_mode_async | clingo_solve_mode_yield`: models are pulled one at a
;; time, and the search runs on clingo's own thread so a wait on it can time out.
(def ^:private mode-async-yield (Integer/valueOf 3))

(def ^:private result-sat   1)

(def ^:private result-unsat 2)

(def ^:private result-interrupted 8)

(defn- symbol->string [s]
  (let [sz (LongByReference.)]
    (chk! "symbol_to_string_size" (ci "clingo_symbol_to_string_size" (Long/valueOf (long s)) sz))
    (let [n (.getValue sz) buf (Memory. (long n))]
      (chk! "symbol_to_string" (ci "clingo_symbol_to_string" (Long/valueOf (long s)) buf (Long/valueOf (long n))))
      (.getString buf 0))))

(defn- model-symbols
  "The shown symbols of model `m` — the s/c/a label strings vaelii emits as ASPIF
   type-4 show statements — read back as strings."
  [m]
  (let [sz (LongByReference.)]
    (chk! "model_symbols_size" (ci "clingo_model_symbols_size" m show-shown sz))
    (let [n (.getValue sz)]
      (if (zero? n) []
          (let [buf (Memory. (long (* 8 n)))]
            (chk! "model_symbols" (ci "clingo_model_symbols" m show-shown buf (Long/valueOf n)))
            (mapv symbol->string (.getLongArray buf 0 (int n))))))))

(defn- model-cost [m]
  (let [sz (LongByReference.)]
    (chk! "model_cost_size" (ci "clingo_model_cost_size" m sz))
    (let [n (.getValue sz)]
      (if (zero? n) []
          (let [buf (Memory. (long (* 8 n)))]
            (chk! "model_cost" (ci "clingo_model_cost" m buf (Long/valueOf n)))
            (vec (.getLongArray buf 0 (int n))))))))

(defn- model-optimal? [m]
  (let [buf (Memory. 1)]
    (chk! "model_optimality_proven" (ci "clingo_model_optimality_proven" m buf))
    (not (zero? (.getByte buf 0)))))

(defn- read-model [m]
  {:atoms (model-symbols m) :cost (model-cost m) :optimal? (model-optimal? m)})

(defn- keep-model
  "Fold model `m` into `acc` (`{:models [..] :optimum cost-vec :any-optimal? bool}`)
   under a `retain` policy.  `:optimum` (the lexicographically least cost vector seen)
   and `:any-optimal?` (did any model come back optimality-proven) are tracked here
   rather than derived from `:models` afterwards, so a model `retain` drops still
   counts towards both.

   * `:optimal` — every model whose cost has not since been beaten.  A strictly better
     cost arriving discards what came before, because `finalize` keeps only the models
     at the proven optimum anyway; a search streams improving models, so this is the
     whole stream but the last plateau.
   * `:last` — the newest, and only the newest.  The brave and cautious enumerations
     stream converging approximations and `finalize` reads `(last models)`; every
     earlier one is read for its cost and then discarded."
  [{:keys [models optimum any-optimal?]} m retain]
  (let [c       (:cost m)
        better? (and (seq c) (or (nil? optimum) (neg? (compare (vec c) (vec optimum)))))]
    {:optimum      (if better? c optimum)
     :any-optimal? (or any-optimal? (boolean (:optimal? m)))
     :models       (case retain
                     :last    [m]
                     :optimal (if better? [m] (conj models m)))}))

(defn- drain-models
  "The models solve handle `h` yields that `retain` keeps, in order, read as each
   arrives — `{:models [..] :optimum cost-vec :any-optimal? bool}` (see `keep-model`).

   `limit` is the solve's budget in seconds (`config/asp-time-limit`; 0 is none).
   Each wait for the next model is bounded by what remains of it, and a search still
   running when nothing remains is cancelled — `clingo_solve_handle_get` then carries
   the interrupted bit, and the models read so far ride beside it for diagnostics.

   Retention matters because a search streams: a 400-node colouring at a two-second
   budget yields 618 models to a `:label` solve that reads one, and 184 to a cautious
   enumeration that reads the last.  Every one of them is a map of freshly marshaled
   atom-label strings, and holding all of them costs what none of them are worth."
  [h limit retain]
  (let [deadline (when (pos? limit) (+ (System/nanoTime) (long (* limit 1e9))))
        ready    (Memory. 1)]
    (loop [acc {:models [] :optimum nil :any-optimal? false}]
      (chk! "resume" (ci "clingo_solve_handle_resume" h))
      (let [remaining (if deadline (max 0.0 (/ (- deadline (System/nanoTime)) 1e9)) -1.0)]
        (cv "clingo_solve_handle_wait" h (Double/valueOf (double remaining)) ready)
        (if (zero? (.getByte ready 0))
          (do (chk! "cancel" (ci "clingo_solve_handle_cancel" h)) acc)
          (let [mr (PointerByReference.)]
            (chk! "model" (ci "clingo_solve_handle_model" h mr))
            (if-let [m (.getValue mr)]
              (recur (keep-model acc (read-model m) retain))
              acc)))))))

(defn- drain-handle
  "Drain and close the solve handle `hr` holds: `{:result <bitset> :models [...]
   :optimum cost-vec :any-optimal? bool}`, the models being what `retain` kept
   (see `drain-models`).

   The close is in a `finally` — freeing a control with a handle still open is
   undefined behaviour in libclingo, so a native failure inside the drain must not
   skip it — and the close itself is guarded, because a `finally` that throws
   *replaces* the exception on its way out.  The in-flight one is the informative
   one: `chk!` names the native call that failed in `:op`, and that is the only
   record of which one it was.  A close that fails on its own is logged and the
   drain's answer stands; there is nothing left to do about the handle either way.
   The sibling `delete-keep-temps!` guards its own cleanup for the same reason."
  [^PointerByReference hr limit retain]
  (let [h (.getValue hr)]
    (try
      (let [drained (drain-models h limit retain)
            res     (IntByReference.)]
        (chk! "get" (ci "clingo_solve_handle_get" h res))
        (assoc drained :result (.getValue res)))
      (finally
        (try (ci "clingo_solve_handle_close" h)
             (catch Throwable e
               (trove/log! {:level :warn :id ::close-failed
                            :msg  (str "closing the clingo solve handle failed: " (ex-message e))
                            :data {:op "clingo_solve_handle_close"}})))))))

(defn- run-solve
  "Solve `aspif-text` with clingo `arg-strs` (clasp-style flags), keeping the models
   `retain` keeps. Returns
   `{:result <bitset> :optimum [long] :any-optimal? bool
     :models [{:atoms [str] :cost [long] :optimal? bool} ...]}`."
  [arg-strs aspif-text retain]
  ;; the delete guards everything from creation on — a `spit` or `control_new` throw
  ;; must not leave the file behind — and no `deleteOnExit`, whose hook set retains
  ;; every path for the process's life; the finally below covers every exit
  (let [tmp (java.io.File/createTempFile "vaelii-aspif" ".aspif")]
    (try
      (spit tmp aspif-text)
      (let [argcs (mapv cstr arg-strs)                 ; retained through control_new
            argv  (if (seq argcs) (ptr-array argcs) Pointer/NULL)
            files (ptr-array [(cstr (.getPath tmp))])
            ctlr  (PointerByReference.)]
        (chk! "control_new" (ci "clingo_control_new" argv (Long/valueOf (count argcs))
                                Pointer/NULL Pointer/NULL (Integer/valueOf 20) ctlr))
        (let [ctl (.getValue ctlr)]
          (try
            (chk! "load_aspif" (ci "clingo_control_load_aspif" ctl files (Long/valueOf 1)))
            (let [hr (PointerByReference.)]
              (chk! "solve" (ci "clingo_control_solve" ctl mode-async-yield Pointer/NULL
                                (Long/valueOf 0) Pointer/NULL Pointer/NULL hr))
              (let [raw (drain-handle hr (config/asp-time-limit) retain)]
                (when (seq argcs) argcs)                 ; keep arg strings alive past the call
                raw))
            (finally
              (cv "clingo_control_free" ctl)))))
      (finally
        (.delete tmp)))))

(def ^:private mode-args
  {:label                ["--opt-mode=optN" "--models=1"]
   :all-optima           ["--opt-mode=optN" "--models=0"]
   :classify-true        ["--opt-mode=optN" "--enum-mode=cautious" "--models=0"]
   :classify-supportable ["--opt-mode=optN" "--enum-mode=brave"    "--models=0"]})

(def ^:private mode-retention
  "How many of a mode's streamed models `drain-models` has to keep.  `:label` and
   `:all-optima` read the models at the optimum, so every model still on the best
   cost is kept; the two classify modes read `(last models)` alone."
  {:label                :optimal
   :all-optima           :optimal
   :classify-true        :last
   :classify-supportable :last})

(defn- optimal-models [models opt]
  (if (nil? opt) models (filter #(= opt (:cost %)) models)))

(defn- mode-args-or-throw [mode]
  (or (mode-args mode)
      (throw (ex-info (str "unknown clingo mode: " mode)
                      {:type :unknown-option :mode mode :valid (keys mode-args)}))))

(defn- finalize
  "Shared post-processing for the raw drain of either solve path — one-shot
   `run-solve` or live-control `solve-control` — into the public contract
   (matches vaelii.impl.asp.clasp/solve):
     :status    :optimum | :sat | :unsat | :interrupted | :unknown
     :atoms     vector of label strings
     :cost      optimum cost (nil if no minimize / unsat)
     :witnesses vector of value vectors (only for :all-optima)
     :raw       the drain (diagnostics)

   `:optimum` and `:any-optimal?` come off the drain rather than out of `:models`,
   which holds only what the mode's retention kept (`keep-model`) — a model dropped
   for being off the best cost still had its say in both.

   `:interrupted` is the cancelled search (the time limit ran out); whatever models
   were yielded before it are not the answer the mode asked for."
  [{:keys [result models any-optimal?] opt :optimum :as raw} mode]
  (let [cost  (first opt)
        status (cond
                 (pos? (bit-and result result-interrupted)) :interrupted
                 (pos? (bit-and result result-unsat))       :unsat
                 (and opt any-optimal?)                     :optimum
                 (pos? (bit-and result result-sat))         :sat
                 :else                                       :unknown)]
    (case mode
      :label
      {:status status :atoms (vec (:atoms (first (optimal-models models opt)))) :cost cost :raw raw}

      :all-optima
      (let [opts (optimal-models models opt)]
        {:status status :atoms (vec (:atoms (first opts)))
         :cost cost :witnesses (mapv (comp vec :atoms) opts) :raw raw})

      (:classify-true :classify-supportable)
      ;; brave/cautious stream converging approximations; the LAST model is the
      ;; converged consequence set (matches clasp's last-witness semantics).
      {:status status :atoms (vec (:atoms (last models))) :cost cost :raw raw})))

(defn solve
  "Run clingo in-process on `aspif-text` (via load_aspif) in one of the supported
   modes. See `finalize` for the return contract."
  [aspif-text mode]
  (finalize (run-solve (mode-args-or-throw mode) aspif-text (mode-retention mode)) mode))

(defn- int-array-mem ^Memory [ints]
  (let [m (Memory. (long (* 4 (max 1 (count ints)))))]
    (doseq [[i v] (map-indexed vector ints)] (.setInt m (long (* i 4)) (int v)))
    m))

(defn- load-block!
  "Load the base ASPIF program into `ctl` via clingo_control_load_aspif. NOT
   additive: clingo rejects a second load_aspif (\"incremental aspif programs are
   not supported\"), so this is a one-shot base load for `open-control` — a live
   control solves the program it opened with, and nothing grows it in place.
   Returns the temp File (caller keeps it alive until the control is freed).

   No `deleteOnExit`: its hook set retains one path, unreclaimable, for the
   process's life — the very cost `delete-keep-temps!` exists to keep off a
   long-running daemon. The file is instead deleted here when the write or the
   load throws, since a caller that never receives it has nothing to hand that
   function."
  [ctl aspif-text]
  (let [tmp (java.io.File/createTempFile "vaelii-session" ".aspif")]
    (try
      (spit tmp aspif-text)
      (let [files (ptr-array [(cstr (.getPath tmp))])]
        (chk! "load_aspif" (ci "clingo_control_load_aspif" ctl files (Long/valueOf 1)))
        tmp)
      (catch Throwable e
        (.delete tmp)
        (throw e)))))

(defn open-control
  "Create a live Control with `arg-strs` flags and load the base `aspif-text`.
   Returns `{:ctl Pointer :keep [..]}` — `:keep` holds JNA buffers and temp
   files that must outlive the control (free it with `free-control!`).

   A load that throws frees the control on the way out: the caller is handed an
   exception rather than a handle, so nothing else can free it, and a leaked
   Control is native memory no GC reaches."
  [arg-strs aspif-text]
  (let [argcs (mapv cstr arg-strs)
        argv  (if (seq argcs) (ptr-array argcs) Pointer/NULL)
        ctlr  (PointerByReference.)]
    (chk! "control_new" (ci "clingo_control_new" argv (Long/valueOf (count argcs))
                            Pointer/NULL Pointer/NULL (Integer/valueOf 20) ctlr))
    (let [ctl (.getValue ctlr)]
      (try
        {:ctl ctl :keep [argcs (load-block! ctl aspif-text)]}
        (catch Throwable e
          (cv "clingo_control_free" ctl)
          (throw e))))))

(defn solve-control
  "Solve a live control under `assume-lits` (signed program literals assumed
   for THIS solve only), keeping the models `retain` keeps.  Returns the same drain
   shape as the one-shot path.  The mode flags are fixed at `open-control` time;
   witness symbols come off the output table, the same `show-shown` view `run-solve`
   reads."
  [ctl assume-lits retain]
  (let [amem (int-array-mem assume-lits)
        hr   (PointerByReference.)]
    (chk! "solve" (ci "clingo_control_solve" ctl mode-async-yield
                      (if (seq assume-lits) amem Pointer/NULL)
                      (Long/valueOf (count assume-lits))
                      Pointer/NULL Pointer/NULL hr))
    (let [raw (drain-handle hr (config/asp-time-limit) retain)]
      #_{:clj-kondo/ignore [:unused-value]}
      (identity amem)                                   ; keep the buffer alive past the call
      raw)))

(defn free-control!
  "Free a live control and let its keep-alive buffers/temps be reclaimed. Freeing
   twice is a native double free, so a caller frees exactly once — `classify-both`
   does it in a finally."
  [ctl]
  (cv "clingo_control_free" ctl))

(defn delete-keep-temps!
  "Delete every temp File in a control's `:keep` vector — the ASPIF file
   `load-block!`/`open-control` wrote. Call AFTER `free-control!`. Non-File
   keep entries (JNA buffers) are left for GC. `run-solve` .deletes its one-shot
   temp in its own finally; a live control outlives its solve, so `classify-both`
   calls this instead of leaning on deleteOnExit — which in a long-running daemon
   holds one .aspif file, and one never-GC'd JVM DeleteOnExitHook entry, per
   classify."
  [keep]
  (doseq [k keep :when (instance? java.io.File k)]
    (try (.delete ^java.io.File k) (catch Throwable _ nil))))

(defn- config-subkey ^long [conf parent-key name]
  (let [kr (IntByReference.)]
    (chk! "configuration_map_at"
          (ci "clingo_configuration_map_at" conf (Integer/valueOf (int parent-key)) (cstr name) kr))
    (.getValue kr)))

(defn- set-enum-mode!
  "Set clingo's `solve.enum_mode` (\"cautious\" | \"brave\" | \"auto\" | …) on a
   live control, read at the next solve."
  [ctl mode-str]
  (let [cr (PointerByReference.)]
    (chk! "control_configuration" (ci "clingo_control_configuration" ctl cr))
    (let [conf    (.getValue cr)
          root    (let [rr (IntByReference.)]
                    (chk! "configuration_root" (ci "clingo_configuration_root" conf rr))
                    (.getValue rr))
          solve-k (config-subkey conf root "solve")
          enum-k  (config-subkey conf solve-k "enum_mode")]
      (chk! "configuration_value_set"
            (ci "clingo_configuration_value_set" conf (Integer/valueOf (int enum-k)) (cstr mode-str))))))

(defn classify-both
  "Load `aspif-text` ONCE and run both classify enumerations over the one control,
   switching `solve.enum_mode` between them — avoiding the second control_new +
   load_aspif that two separate `solve` calls pay. Returns
   `{:cautious <result> :brave <result>}`, each shaped like `solve` for the
   corresponding classify mode."
  [aspif-text]
  (let [{:keys [ctl keep]} (open-control ["--opt-mode=optN" "--models=0"] aspif-text)]
    (try
      (let [run (fn [enum-mode]
                  (set-enum-mode! ctl enum-mode)
                  ;; both classify modes share finalize's post-processing (last model),
                  ;; and its retention with it
                  (finalize (solve-control ctl [] (mode-retention :classify-true))
                            :classify-true))
            cautious (run "cautious")
            brave    (run "brave")]
        #_{:clj-kondo/ignore [:unused-value]}
        (identity keep)                          ; retain open-control buffers past the solves
        {:cautious cautious :brave brave})
      (finally
        ;; the temps go even when the free throws.  `delete-keep-temps!` is the only
        ;; thing that removes them — there is no `deleteOnExit` to fall back on — so a
        ;; throw out of `free-control!` would leave one .aspif per classify behind in a
        ;; long-running daemon's tmpdir.
        (try (free-control! ctl)
             (finally (delete-keep-temps! keep)))))))

(defn available?
  "True if libclingo can be loaded and called in this JVM."
  []
  (try (cv "clingo_version" (IntByReference.) (IntByReference.) (IntByReference.)) true
       (catch Throwable _ false)))

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
   is lost vs the subprocess — every native return is checked and every Control
   is freed in a finally; a malformed program throws rather than segfaults."
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
  (when (zero? r) (throw (ex-info (str "clingo " what " failed: " (clingo-error)) {:op what})))
  r)

(defn- cstr ^Memory [s]
  (let [b (.getBytes (str s) "UTF-8") m (Memory. (long (inc (alength b))))]
    (.write m 0 b 0 (alength b)) (.setByte m (long (alength b)) (byte 0)) m))

(defn- ptr-array ^Memory [ptrs]
  (let [m (Memory. (long (* Native/POINTER_SIZE (count ptrs))))]
    (doseq [[i p] (map-indexed vector ptrs)] (.setPointer m (long (* i Native/POINTER_SIZE)) p))
    m))

(def ^:private show-shown   (Integer/valueOf 2))

(def ^:private mode-yield   (Integer/valueOf 2))

(def ^:private result-sat   1)

(def ^:private result-unsat 2)

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

(defn- run-solve
  "Solve `aspif-text` with clingo `arg-strs` (clasp-style flags). Returns
   {:result <bitset> :models [{:atoms [str] :cost [long] :optimal? bool} ...]}."
  [arg-strs aspif-text]
  (let [tmp   (doto (java.io.File/createTempFile "vaelii-aspif" ".aspif") .deleteOnExit)
        _     (spit tmp aspif-text)
        argcs (mapv cstr arg-strs)                 ; retained through control_new
        argv  (if (seq argcs) (ptr-array argcs) Pointer/NULL)
        files (ptr-array [(cstr (.getPath tmp))])
        ctlr  (PointerByReference.)]
    (chk! "control_new" (ci "clingo_control_new" argv (Long/valueOf (count argcs))
                            Pointer/NULL Pointer/NULL (Integer/valueOf 20) ctlr))
    (let [ctl (.getValue ctlr)]
      (try
        (chk! "load_aspif" (ci "clingo_control_load_aspif" ctl files (Long/valueOf 1)))
        (let [hr (PointerByReference.)]
          (chk! "solve" (ci "clingo_control_solve" ctl mode-yield Pointer/NULL (Long/valueOf 0)
                            Pointer/NULL Pointer/NULL hr))
          (let [h (.getValue hr)
                models (loop [acc []]
                         (chk! "resume" (ci "clingo_solve_handle_resume" h))
                         (let [mr (PointerByReference.)]
                           (chk! "model" (ci "clingo_solve_handle_model" h mr))
                           (if-let [m (.getValue mr)] (recur (conj acc (read-model m))) acc)))
                res (IntByReference.)]
            (chk! "get" (ci "clingo_solve_handle_get" h res))
            (ci "clingo_solve_handle_close" h)
            (when (seq argcs) argcs)                 ; keep arg strings alive past the call
            {:result (.getValue res) :models models}))
        (finally
          (cv "clingo_control_free" ctl)
          (.delete tmp))))))

(def ^:private mode-args
  {:label                ["--opt-mode=optN" "--models=1"]
   :all-optima           ["--opt-mode=optN" "--models=0"]
   :classify-true        ["--opt-mode=optN" "--enum-mode=cautious" "--models=0"]
   :classify-supportable ["--opt-mode=optN" "--enum-mode=brave"    "--models=0"]})

(defn- optimum-cost-vec
  "The proven optimum cost vector across `models` (lexicographically least), or
   nil when the program has no minimize statement (all cost vectors empty)."
  [models]
  (let [costs (remove empty? (map :cost models))]
    (when (seq costs)
      (first (sort (fn [a b] (compare (vec a) (vec b))) costs)))))

(defn- optimal-models [models opt]
  (if (nil? opt) models (filter #(= opt (:cost %)) models)))

(defn- mode-args-or-throw [mode]
  (or (mode-args mode)
      (throw (ex-info (str "unknown clingo mode: " mode) {:mode mode :valid (keys mode-args)}))))

(defn- finalize
  "Shared post-processing for the raw `{:result :models}` of either solve path —
   one-shot `run-solve` or live-control `solve-control` — into the public contract
   (matches vaelii.impl.asp.clasp/solve):
     :status    :optimum | :sat | :unsat | :unknown
     :atoms     vector of label strings
     :cost      optimum cost (nil if no minimize / unsat)
     :witnesses vector of value vectors (only for :all-optima)
     :raw       {:result :models} (diagnostics)"
  [{:keys [result models] :as raw} mode]
  (let [opt   (optimum-cost-vec models)
        cost  (first opt)
        status (cond
                 (pos? (bit-and result result-unsat)) :unsat
                 (and opt (some :optimal? models))    :optimum
                 (pos? (bit-and result result-sat))   :sat
                 :else                                 :unknown)]
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
  (finalize (run-solve (mode-args-or-throw mode) aspif-text) mode))

(defn- int-array-mem ^Memory [ints]
  (let [m (Memory. (long (* 4 (max 1 (count ints)))))]
    (doseq [[i v] (map-indexed vector ints)] (.setInt m (long (* i 4)) (int v)))
    m))

(defn- load-block!
  "Load the base ASPIF program into `ctl` via clingo_control_load_aspif. NOT
   additive: clingo rejects a second load_aspif (\"incremental aspif programs are
   not supported\"), so this is a one-shot base load for `open-control` — a live
   control solves the program it opened with, and nothing grows it in place.
   Returns the temp File (caller keeps it alive until the control is freed)."
  [ctl aspif-text]
  (let [tmp   (doto (java.io.File/createTempFile "vaelii-session" ".aspif") .deleteOnExit)
        _     (spit tmp aspif-text)
        files (ptr-array [(cstr (.getPath tmp))])]
    (chk! "load_aspif" (ci "clingo_control_load_aspif" ctl files (Long/valueOf 1)))
    tmp))

(defn open-control
  "Create a live Control with `arg-strs` flags and load the base `aspif-text`.
   Returns `{:ctl Pointer :keep [..]}` — `:keep` holds JNA buffers and temp
   files that must outlive the control (free it with `free-control!`)."
  [arg-strs aspif-text]
  (let [argcs (mapv cstr arg-strs)
        argv  (if (seq argcs) (ptr-array argcs) Pointer/NULL)
        ctlr  (PointerByReference.)]
    (chk! "control_new" (ci "clingo_control_new" argv (Long/valueOf (count argcs))
                            Pointer/NULL Pointer/NULL (Integer/valueOf 20) ctlr))
    (let [ctl (.getValue ctlr)
          tmp (load-block! ctl aspif-text)]
      {:ctl ctl :keep [argcs tmp]})))

(defn solve-control
  "Solve a live control under `assume-lits` (signed program literals assumed
   for THIS solve only). Drains every model. Returns `{:result :models}` like
   the one-shot path. The mode flags are fixed at `open-control` time; witness
   symbols come off the output table, the same `show-shown` view `run-solve` reads."
  [ctl assume-lits]
  (let [amem (int-array-mem assume-lits)
        hr   (PointerByReference.)]
    (chk! "solve" (ci "clingo_control_solve" ctl mode-yield
                      (if (seq assume-lits) amem Pointer/NULL)
                      (Long/valueOf (count assume-lits))
                      Pointer/NULL Pointer/NULL hr))
    (let [h      (.getValue hr)
          models (loop [acc []]
                   (chk! "resume" (ci "clingo_solve_handle_resume" h))
                   (let [mr (PointerByReference.)]
                     (chk! "model" (ci "clingo_solve_handle_model" h mr))
                     (if-let [m (.getValue mr)] (recur (conj acc (read-model m))) acc)))
          res    (IntByReference.)]
      (chk! "get" (ci "clingo_solve_handle_get" h res))
      (ci "clingo_solve_handle_close" h)
      #_{:clj-kondo/ignore [:unused-value]}
      (identity amem)                                   ; keep the buffer alive past the call
      {:result (.getValue res) :models models})))

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
                  ;; both classify modes share finalize's post-processing (last model)
                  (finalize (solve-control ctl []) :classify-true))
            cautious (run "cautious")
            brave    (run "brave")]
        #_{:clj-kondo/ignore [:unused-value]}
        (identity keep)                          ; retain open-control buffers past the solves
        {:cautious cautious :brave brave})
      (finally
        (free-control! ctl)
        (delete-keep-temps! keep)))))

(defn available?
  "True if libclingo can be loaded and called in this JVM."
  []
  (try (cv "clingo_version" (IntByReference.) (IntByReference.) (IntByReference.)) true
       (catch Throwable _ false)))

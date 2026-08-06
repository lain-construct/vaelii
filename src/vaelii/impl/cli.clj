;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.cli
  "A command-line driver for a KB — the shell dual of the in-process API, launched with
  `lein run -m vaelii.impl.cli <cmd> <args…>`.  It runs the engine in-process (no
  daemon); to talk to a running daemon use `vaelii.impl.client` instead.

    lein run -m vaelii.impl.cli assert  '(dog Fido)'  NaturalWorldContext --dir /tmp/kb
    lein run -m vaelii.impl.cli query   '(dog ?x)'    NaturalWorldContext --dir /tmp/kb
    lein run -m vaelii.impl.cli why     3                                 --dir /tmp/kb
    lein run -m vaelii.impl.cli export  /tmp/dump                         --dir /tmp/kb
    lein run -m vaelii.impl.cli repl --starter          # interactive, starter schema

  **Backend.**  `--dir <path>` uses the durable `:disk` backend (recovered on open, so
  a fact asserted in one invocation is there in the next); with no `--dir` the KB is
  in-memory and lives only for the process — useful for `repl` or a single compound
  session, pointless across one-shot commands.  `--starter` loads the shipped schema
  (types, contexts, relation rules) so you can explore the ontology.  `--strength
  monotonic` marks an `assert` known-true.  `export` takes `--variant
  records|records+index` and `--compression gzip|xz|none`.

  **One writer.**  A `--dir` KB takes the single-writer file lock (docs/storage.md), so
  the CLI and a daemon cannot own the same directory at once — by design."
  (:require [clojure.edn :as edn]
            [clojure.pprint :as pp]
            [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.impl.starter :as starter])
  (:import [java.io PushbackReader StringReader]))

;; ---- arg + option parsing ------------------------------------------------

(def ^:private value-flags
  "The value-taking flags any command may carry — the whole roster the commands
  below read.  A flag outside it is refused, not keywordized: `--strenght monotonic`
  accepted in silence would store known-true content at `:default` — the exact
  sentence the flag-with-no-value refusal beside it exists for, reached from the
  other side — and a misspelt `--dir` would open the in-memory KB, gone at exit."
  #{"--dir" "--strength" "--depth" "--variant" "--compression"})

(defn parse-opts
  "Split raw args into `[positionals opts]`.  `--k v` becomes `{:k v}`, a bare
  `--memory` / `--starter` becomes `{:flag true}`; everything else is a positional,
  in order.

  A value-taking flag with no value is refused (`:unknown-option`) rather than bound
  nil: `assert … --strength` with nothing after it would otherwise store at `:default`
  — the exact class the flag was written to escape — and `--dir` at the end of a line
  would open the in-memory KB, gone at process exit.  A flag the roster does not
  name is refused the same way."
  [args]
  (loop [as args, pos [], opts {}]
    (if (empty? as)
      [pos opts]
      (let [a (first as)]
        (cond
          (not (str/starts-with? a "--")) (recur (rest as) (conj pos a) opts)
          (#{"--memory" "--starter"} a)   (recur (rest as) pos (assoc opts (keyword (subs a 2)) true))
          (not (value-flags a))
          (throw (ex-info (str "unknown flag: " a) {:type :unknown-option :flag a}))
          :else (if-some [v (second as)]
                  (recur (drop 2 as) pos (assoc opts (keyword (subs a 2)) v))
                  (throw (ex-info (str a " needs a value and the line ends after it"
                                       " — write " a " <value>")
                                  {:type :unknown-option :flag a}))))))))

(defn read-arg
  "One argv string as data: the EDN it reads as — a sentence, a context symbol, a handle
  — and the **raw string** when it reads as none.

  That last case is what a filesystem path is.  `/var/lib/vaelii` is not a symbol (two
  slashes), so a command taking a path (`export`, `load`) would otherwise fail in the
  reader, before the command it belongs to had been looked at."
  [s]
  (try (edn/read-string s) (catch Exception _ s)))

(defn read-forms
  "Every EDN form in `s`, in order — how a REPL line's args (`(dog ?x) MyContext`) are
  parsed into data."
  [s]
  (let [r (PushbackReader. (StringReader. s))]
    (loop [acc []]
      (let [form (edn/read {:eof ::eof} r)]
        (if (= form ::eof) acc (recur (conj acc form)))))))

;; ---- the command table ---------------------------------------------------
;; `dispatch` takes args **already parsed to data** (a sentence is a list, a context a
;; symbol, a handle a long), so `-main` (which edn-reads each argv string) and the REPL
;; (which reads forms off the line) share one implementation.

(def commands
  "The command words `dispatch` knows, for the usage message and `unknown command`."
  ["assert" "assert-rule" "match" "query" "query?" "ask" "prove" "provable?" "retract"
   "why" "why-not" "in" "isa" "types-of" "handle-of" "types" "contexts" "conflicts"
   "contradictions" "load" "export" "repl"])

(defn dispatch
  "Run one command against `kb` and return its result (a handle, a seq of sentences /
  solutions, a proof tree, …).  `args` are data; `opts` is the parsed option map."
  [kb cmd args opts]
  (let [strength (when-let [s (:strength opts)] {:strength (keyword s)})
        ;; `--depth n` is how a command line says how far to expand rules.  Absent, the
        ;; read is whatever needs no rule — `query`'s contract, and there is deliberately
        ;; no default to supply here either.
        depth    (when-let [d (:depth opts)] {:max-depth (Long/parseLong (str d))})]
    (case cmd
      "assert"      (v/assert kb (nth args 0) (nth args 1) strength)
      "assert-rule" (v/assert-rule kb (nth args 0) (nth args 1) (nth args 2))
      "match"       (mapv :sentence (v/sentexes-matching kb (nth args 0) (nth args 1)))
      "query"       (vec (v/query kb (nth args 0) (nth args 1) depth))
      "query?"      (v/query? kb (nth args 0) (nth args 1) depth)
      "ask"         (vec (v/ask kb (nth args 0) (nth args 1)))
      "prove"       (v/prove kb (nth args 0) (nth args 1))
      "provable?"   (v/provable? kb (nth args 0) (nth args 1))
      "retract"     (v/retract! kb (nth args 0))
      "why"         (v/why kb (nth args 0))
      "why-not"     (if (= 1 (count args))
                      (v/why-not kb (nth args 0))
                      (v/why-not kb (nth args 0) (nth args 1)))
      "in"          (v/in? kb (nth args 0))
      "isa"         (apply v/isa? kb args)
      "types-of"    (apply v/types-of kb args)
      "handle-of"   (v/handle-of kb (nth args 0) (nth args 1))
      "types"       (sort (v/types kb))
      "contexts"    (sort (v/contexts kb))
      "conflicts"   (v/conflicts kb)
      "contradictions" (v/contradictions kb)
      ;; both numbers, because they differ exactly when the file repeats itself:
      ;; `assert` answers the existing handle for a sentence already stored, so the
      ;; distinct handles are the sentexes the load actually left in the KB, and a
      ;; file of N duplicates reports `:loaded N :stored 1` instead of "loaded N"
      "load"        (let [entries (edn/read-string (slurp (str (nth args 0))))
                          handles (v/with-deferred-settle kb
                                    (mapv (fn [[s ctx o]] (v/assert kb s ctx o)) entries))]
                      {:loaded (count entries)
                       ;; flatten: a rule concluding a conjunction answers a vector
                       :stored (count (distinct (flatten handles)))})
      ;; the one command whose argument is a **destination** rather than knowledge:
      ;; `--variant` and `--compression` arrive as strings and are the writer's own
      ;; keywords, so they are read as such rather than re-spelled here
      "export"      (v/export! kb (str (nth args 0))
                               (cond-> {}
                                 (:variant opts)     (assoc :variant (keyword (:variant opts)))
                                 (:compression opts) (assoc :compression (keyword (:compression opts)))))
      (throw (ex-info (str "unknown command: " cmd)
                      {:type :unknown-command :cmd cmd :commands commands})))))

;; ---- KB construction -----------------------------------------------------

(defn open-kb-from
  "Build the KB a run operates on from the parsed `opts`: `:dir` → durable disk
  (recovered), else in-memory — which `:memory` also names explicitly, so `--memory
  --dir <path>` is a contradiction and is refused rather than resolved by a guess.
  `:starter` loads the shipped schema."
  [{:keys [dir starter memory] :as _opts}]
  (when (and memory dir)
    (throw (ex-info (str "--memory and --dir " dir " contradict — a memory KB has no"
                         " directory.  Drop one: --dir for the durable KB, --memory"
                         " (or neither) for the in-process one.")
                    {:type :unknown-option :flags ["--memory" "--dir"]})))
  (let [kb (if dir
             (v/open-kb {:backend :disk :dir dir :recover? :auto})
             (v/open-kb {}))]
    (when starter (starter/load-into kb))
    kb))

;; ---- the shell -----------------------------------------------------------

(defn- show [x] (if (coll? x) (pp/pprint x) (println x)))

(defn- repl-loop
  "Interactive loop: each line is `<cmd> <edn-forms…>` (no `--flags` — options are
  fixed at repl start).  Holds `kb` in-process, so a memory KB accumulates for the
  session.  Ends on `exit` / `quit` / EOF."
  [kb opts]
  (println "vaelii repl —" (str/join " " commands) "— or exit")
  (loop []
    (print "vaelii> ") (flush)
    (when-let [line (read-line)]
      (let [line (str/trim line)]
        (cond
          (#{"exit" "quit"} line) (println "bye")
          (str/blank? line)       (recur)
          ;; `Throwable`, as the browser's untrusted-EDN reads: a deeply nested line
          ;; raises `StackOverflowError` out of `read-forms`, and the loop dying on a
          ;; line of input is the one thing a shell must not do
          :else (do (try
                      (let [cmd  (re-find #"^\S+" line)
                            rest* (str/triml (subs line (count cmd)))]
                        (if (= cmd "repl")
                          (println "already in a repl")
                          (show (dispatch kb cmd (read-forms rest*) opts))))
                      (catch Throwable e
                        (println "error:" (or (.getMessage e)
                                              (.. e getClass getSimpleName)))))
                    (recur)))))))

(defn -main
  "Parse argv, open the KB, run the command, and print the result.  With `repl` (or no
  command) it drops into the interactive loop."
  [& argv]
  ;; a refused flag or an opts contradiction is the operator's mistake in the shell's
  ;; own vocabulary — one line and exit 1, the same courtesy the command arm extends
  (let [[positionals opts] (try (parse-opts argv)
                                (catch clojure.lang.ExceptionInfo e
                                  (println "error:" (.getMessage e))
                                  (System/exit 1)))
        [cmd & args] positionals
        kb (try (open-kb-from opts)
                (catch clojure.lang.ExceptionInfo e
                  (println "error:" (.getMessage e))
                  (System/exit 1)))]
    (cond
      (or (nil? cmd) (= cmd "repl"))
      (repl-loop kb opts)

      (some #{cmd} commands)
      ;; a refusal — a bad name, a non-empty export destination, a disjointness clash —
      ;; is an operator's mistake, not a crash: print what the engine said and leave with
      ;; a status, so a shell script can tell.  The message is the engine's own, which is
      ;; what makes the CLI, the daemon and the browser refuse a thing in the same words.
      ;; `Throwable`, not `ExceptionInfo`: `dispatch` reaches into `args` with `nth` and
      ;; parses numbers with `Long/parseLong`, so a missing argument or a non-numeric
      ;; `--depth` raises `IndexOutOfBoundsException` / `NumberFormatException` — a stack
      ;; trace where the same mistake in engine vocabulary prints one line and exits 1.
      ;; A missing file for `load` is the same shape — and so, past `Exception`, is a
      ;; deeply nested EDN argument or `load` file, whose read raises
      ;; `StackOverflowError` (the browser's untrusted-EDN reads make the same catch).
      (try (show (dispatch kb cmd (mapv read-arg args) opts))
           (catch clojure.lang.ExceptionInfo e
             (println "error:" (.getMessage e))
             (System/exit 1))
           (catch Throwable e
             (println "error:" (or (.getMessage e) (.. e getClass getSimpleName)))
             (System/exit 1)))

      :else
      (do (println "unknown command:" cmd)
          (println "commands:" (str/join " " commands))
          (System/exit 2)))))

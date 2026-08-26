;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.cli
  "A command-line driver for a KB — the shell dual of the in-process API, launched with
  `lein run -m vaelii.impl.cli <cmd> <args…>`.  It runs the engine in-process (no
  daemon); to talk to a running daemon use `vaelii.impl.client` instead.

    lein run -m vaelii.impl.cli assert  '(dog Muffet)'  CxNaturalWorld --dir /tmp/kb
    lein run -m vaelii.impl.cli query   '(dog ?x)'    CxNaturalWorld --dir /tmp/kb
    lein run -m vaelii.impl.cli why     3                                 --dir /tmp/kb
    lein run -m vaelii.impl.cli export  /tmp/dump                         --dir /tmp/kb
    lein run -m vaelii.impl.cli repl --starter          # interactive, starter schema
    lein cli help                                      # every command and what it takes

  `help` is a word rather than only a flag because Leiningen answers `lein cli --help`
  itself, printing the alias expansion — the flag never reaches this namespace through
  the alias, though it does through the full `lein run -m vaelii.impl.cli --help`.

  **Backend.**  `--dir <path>` uses the durable `:disk-log` backend (recovered on open, so
  a fact asserted in one invocation is there in the next); with no `--dir` the KB is
  in-memory and lives only for the process — useful for `repl` or a single compound
  session, pointless across one-shot commands.  `--starter` loads the shipped schema
  (types, contexts, relation rules) so you can explore the ontology.  `--strength
  monotonic` marks an `assert` or `assert-rule` known-true.  `export` takes `--variant
  records|records+index` and `--compression gzip|xz|none`.

  **A flag belongs to the commands that read it** (`command-flags`), and one carried by
  a command that does not is refused rather than dropped — those three are the driver's
  and go anywhere, the rest do not.

  **One writer.**  A `--dir` KB takes the single-writer file lock (docs/storage.md), so
  the CLI and a daemon cannot own the same directory at once — by design."
  (:require [clojure.edn :as edn]
            [clojure.pprint :as pp]
            [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.starter :as starter])
  (:import [java.io PushbackReader StringReader]))

;; ---- arg + option parsing ------------------------------------------------

(def ^:private value-flags
  "Every value-taking flag spelling the driver knows — what `parse-opts` will bind at
  all, as against which command may carry which, that being `command-flags`' answer
  one door further in.  A flag outside it is refused, not keywordized: `--strenght monotonic`
  accepted in silence would store known-true content at `:default` — the exact
  sentence the flag-with-no-value refusal beside it exists for, reached from the
  other side — and a misspelt `--dir` would open the in-memory KB, gone at exit."
  #{"--dir" "--strength" "--depth" "--variant" "--compression" "--format"
    "--context" "--nearest"})

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
          (#{"--help" "--memory" "--starter"} a)
          (recur (rest as) pos (assoc opts (keyword (subs a 2)) true))
          (not (value-flags a))
          (throw (ex-info (str "unknown flag: " a " — the driver reads "
                               (str/join ", " (sort (into #{"--help" "--memory" "--starter"}
                                                          value-flags)))
                               ", and a command reads only its own of those")
                          {:type :unknown-option :flag a}))
          :else (let [v (second as)]
                  ;; a following flag is not a value: `--dir --starter` otherwise opens
                  ;; a directory literally named `--starter` and never loads the schema
                  (if (and (some? v) (not (str/starts-with? v "--")))
                    (recur (drop 2 as) pos (assoc opts (keyword (subs a 2)) v))
                    (throw (ex-info (str a " needs a value and "
                                         (if v (str "the next word is the flag " v)
                                             "the line ends after it")
                                         " — write " a " <value>")
                                    {:type :unknown-option :flag a})))))))))

(defn read-arg
  "One argv string as data: the EDN it reads as — a sentence, a context symbol, a handle
  — and the **raw string** when it reads as none.

  That last case is what a filesystem path is.  `/var/lib/vaelii` is not a symbol (two
  slashes), so a command taking a path (`export`, `load`) would otherwise fail in the
  reader, before the command it belongs to had been looked at."
  [s]
  (try (edn/read-string s) (catch Exception _ s)))

(defn read-forms
  "Every EDN form in `s`, in order — how a REPL line's args (`(dog ?x) CxMy`) are
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

(def command-table
  "Every command word, in the order `--help` prints it: `[min max operands gloss]`.

  `max` is nil for a command whose last operand is optional.  One table rather than
  two, because the arity a command *takes* and the arity `--help` *advertises* going
  out of step is how a usage message starts lying — and `dispatch` reaches into `args`
  with `nth`, so an unchecked short line raises `IndexOutOfBoundsException`, whose
  message is the class name and names neither the command nor the argument."
  [["assert"      2 2   "'<sentence>' <CxName>"        "store a fact"]
   ["assert-rule" 3 3   "'[<antecedents>]' '<consequent>' <CxName>" "store a rule"]
   ["match"       2 2   "'<pattern>' <CxName>"         "stored, believed literals, in content order"]
   ["query"       2 2   "'<goal>' <CxName>"            "the default read, in content order (--depth N to expand rules)"]
   ["query?"      2 2   "'<goal>' <CxName>"            "the same, as a boolean"]
   ["ask"         2 2   "'<goal>' <CxName>"            "the prover registry, in content order; no rule expansion"]
   ["prove"       2 2   "'<goal>' <CxName>"            "backward chaining; one solution per derivation, in DFS order"]
   ["provable?"   2 2   "'<goal>' <CxName>"            "the same, as a boolean"]
   ["retract"     1 1   "<handle>"                      "remove a sentex and what it solely supported"]
   ["why"         1 1   "<handle>"                      "the proof tree behind a belief"]
   ["why-not"     1 2   "'<goal>' [<CxName>]"          "why a goal is not believed (--nearest N: the rules that nearly fired)"]
   ["in"          1 1   "<handle>"                      "is it believed?"]
   ["isa"         2 3   "<Individual> <type> [<CxName>]" "type membership, via genl"]
   ["types-of"    1 2   "<Individual> [<CxName>]"      "the types asserted of it, not their supertypes"]
   ["describe"    1 1   "<term>"                        "everything the KB holds about one term (--context C)"]
   ["handle-of"   2 2   "'<sentence>' <CxName>"        "the handle a sentence is stored under"]
   ["types"       0 0   ""                              "types in the genl hierarchy"]
   ["contexts"    0 0   ""                              "contexts in the genlCx hierarchy"]
   ["conflicts"   0 0   ""                              "irreducible :monotonic clashes, both still believed"]
   ["contradictions" 0 0 ""                             "coexisting P/¬P pairs at :default"]
   ["quality"     0 0   ""                              "a report on the knowledge: unfired rules, skew, depth, coverage"]
   ["load"        1 1   "<path>"                        "assert a text KB: a Cx*.txt file, or a directory of them"]
   ["export"      1 1   "<dest>"                        "write a dump (--variant, --compression), or a text KB (--format text)"]
   ["diff"        2 2   "<a> <b>"                       "what two text KBs disagree about, as content"]
   ["repl"        0 0   ""                              "the interactive loop"]])

(def commands
  "The command words `dispatch` knows, for the usage message and `unknown command`."
  (mapv first command-table))

(def ^:private arity-of
  "command word -> `[min max operands]`, for `check-arity!`."
  (into {} (map (fn [[c mn mx ops _]] [c [mn mx ops]])) command-table))

(defn check-arity!
  "Refuse a command line with the wrong number of operands, naming what the command
  takes and what it got.

  Without this the short line reaches `dispatch`, whose `nth` raises
  `IndexOutOfBoundsException` — caught and printed, so `lein cli assert '(dog Rex)'`
  answers `error: IndexOutOfBoundsException`: a true statement about a vector, and no
  help at all to someone who left off a context.  A *long* line is refused too, since
  the extra operand is otherwise dropped in silence — and a dropped context is a fact
  stored somewhere other than where it was meant to go."
  [cmd args]
  (when-some [[mn mx ops] (arity-of cmd)]
    (let [n (count args)]
      (when (or (< n mn) (and mx (> n mx)))
        (throw (ex-info (str cmd " takes " (if (and mx (= mn mx))
                                             (str mn " argument" (when (not= 1 mn) "s"))
                                             (str mn "–" (or mx "any") " arguments"))
                             ", given " n
                             "\n  usage: " cmd (when (seq ops) (str " " ops))
                             "\n  quote every argument: the shell eats ( ) [ ] and ?")
                        {:type :unknown-option :cmd cmd :given n :takes [mn mx]}))))))

(def ^:private driver-flags
  "The flags that say which KB to open rather than what a command does with it.  They
  apply to every command, so `check-flags!` admits them everywhere."
  #{:dir :memory :starter :help})

(def ^:private command-flags
  "The value flags each command reads, keyed by command word; a command absent from the
  map reads none.  This is `assert-opt-keys`' rule at the shell door (docs/api.md): an
  option is a request, and one the door cannot honour is refused rather than dropped.
  `match … --strength monotonic` accepted and ignored reads from the outside exactly
  like a strength that was applied.

  `repl` is the union on purpose — its options are fixed at session start and every
  line reuses them (`repl-loop`), so a flag there belongs to whichever line reads it."
  {"assert"      #{:strength}
   "assert-rule" #{:strength}
   "query"       #{:depth}
   "query?"      #{:depth}
   "export"      #{:variant :compression :format}
   "describe"    #{:context}
   "why-not"     #{:nearest}})

(defn- flag-names [ks] (str/join ", " (map #(str "--" (name %)) (sort ks))))

(defn check-flags!
  "Refuse a flag `cmd` does not read, naming what it does read.

  `-main` calls this rather than `dispatch`, and that placement is the whole of it: the
  REPL reuses one option map for every line it runs, so a session opened `--strength
  monotonic` must not have a later `match` line refused for carrying the session's
  flag.  The line naming `repl` is checked against the union instead, and the lines
  inside it against nothing.

  An unknown command word is left alone, as `check-arity!` leaves it — `-main` reports
  that as `:unknown-command`, which says more than a flag complaint about a command
  that does not exist."
  [cmd opts]
  (when (some #{cmd} commands)
    (let [allowed (if (= cmd "repl")
                    (reduce into #{} (vals command-flags))
                    (get command-flags cmd #{}))
          unread  (remove (into driver-flags allowed) (keys opts))]
      (when (seq unread)
        (throw (ex-info (str cmd " does not read " (flag-names unread) " — it reads "
                             (if (seq allowed) (flag-names allowed) "no options of its own")
                             ".  A flag a command cannot honour is dropped in silence"
                             " otherwise, which reads exactly like one that was applied.")
                        {:type :unknown-option :cmd cmd
                         :unread (mapv #(str "--" (name %)) (sort unread))
                         :reads  (mapv #(str "--" (name %)) (sort allowed))}))))))

(defn usage
  "The `--help` text: every command, its operands and a one-line gloss."
  []
  (let [w (apply max (map (fn [[c _ _ ops _]] (count (str c " " ops))) command-table))]
    (str "vaelii — a command-line driver for a KB\n\n"
         "  lein cli <command> [args…] [--dir <path>] [--starter] [--memory]\n\n"
         "Quote every argument. A shell eats parens, brackets and `?`:\n"
         "  lein cli assert '(dog Muffet)' CxNaturalWorld --dir /tmp/kb\n"
         "  lein cli match  '(dog ?x)'   CxNaturalWorld --dir /tmp/kb\n\n"
         "Commands:\n"
         (str/join "\n"
                   (for [[c _ _ ops gloss] command-table]
                     (str "  " (format (str "%-" w "s")
                                       (str c (when (seq ops) (str " " ops))))
                          "   " gloss)))
         "\n\nOptions.  The first three name the KB and go with any command; the rest"
         " belong to\nthe commands named beside them, and are refused elsewhere:\n"
         "  --dir <path>          the durable :disk-log KB (recovered on open); absent, in-memory\n"
         "  --memory              the in-memory KB, said explicitly\n"
         "  --starter             load the shipped starter schema\n"
         "  --strength <s>        assert, assert-rule: :monotonic instead of :default\n"
         "  --depth <n>           query, query?: how far to expand rules\n"
         "  --variant <v>         export: records | records+index\n"
         "  --compression <c>     export: gzip | xz | none\n"
         "  --format text         export: a text KB instead of a dump — one Cx<Name>.txt\n"
         "                        per context, the format `load` reads\n"
         "  --context <CxName>    describe: the vantage to read from; absent, every context\n"
         "  --nearest <n>         why-not: run a bounded search and name the n rules that\n"
         "                        came closest, with the antecedent each is missing\n"
         "  (repl takes all seven — its options are fixed at start and each line reuses them)\n")))

(defn- in-content-order
  "An answer **set**, in a printed content order.

  Three commands answer with one — `match`, `query` and `ask` — and a set has no order of
  its own, so what reached stdout was whichever order the retrieval enumerated: two loads
  of the same knowledge printed it differently, and a diff of the two outputs read as a
  change in the KB.  `types` and `contexts` in the same table are sorted for that reason,
  and these are held to it too.

  `prove` is deliberately **not** here.  It answers one solution per derivation in the
  order the DFS found them, and that order is part of what a proof says."
  [answers]
  (nm/sort-by-content-key nm/print-key compare answers))

(defn dispatch
  "Run one command against `kb` and return its result (a handle, a seq of sentences /
  solutions, a proof tree, …).  `args` are data; `opts` is the parsed option map.

  **A command that answers a set answers it sorted** (`in-content-order`): `match`,
  `query` and `ask` alongside `types` and `contexts`, so one KB prints the same output
  however its knowledge arrived.  `prove` keeps the DFS's order, which is a reading rather
  than an artifact."
  [kb cmd args opts]
  (check-arity! cmd args)
  (let [strength (when-let [s (:strength opts)] {:strength (keyword s)})
        ;; `--depth n` is how a command line says how far to expand rules.  Absent, the
        ;; read is whatever needs no rule — `query`'s contract, and there is deliberately
        ;; no default to supply here either.
        depth    (when-let [d (:depth opts)] {:max-depth (Long/parseLong (str d))})
        ;; `--context C` names the vantage a read takes; absent, `?ctx` reads every
        ;; context, which is the whole-KB view and what a shell line usually means
        ctx      (if-let [c (:context opts)] (symbol (str c)) '?ctx)
        nearest  (when-let [n (:nearest opts)] {:nearest (Long/parseLong (str n))})]
    (case cmd
      "assert"      (v/assert kb (nth args 0) (nth args 1) strength)
      "assert-rule" (v/assert-rule kb (nth args 0) (nth args 1) (nth args 2) strength)
      "match"       (in-content-order (map :sentence (v/sentexes-matching kb (nth args 0) (nth args 1))))
      "query"       (in-content-order (v/query kb (nth args 0) (nth args 1) depth))
      "query?"      (v/query? kb (nth args 0) (nth args 1) depth)
      "ask"         (in-content-order (v/ask kb (nth args 0) (nth args 1)))
      "prove"       (v/prove kb (nth args 0) (nth args 1))
      "provable?"   (v/provable? kb (nth args 0) (nth args 1))
      "retract"     (v/retract! kb (nth args 0))
      "why"         (v/why kb (nth args 0))
      ;; `--nearest N` is the one that costs a search, so it is a flag rather than the
      ;; default: it runs a bounded backward search and names the rules that came closest,
      ;; which is what a `:not-stored` answer cannot say on its own (docs/api.md).
      ;;
      ;; This command takes a **goal** or a **handle** — one integer operand is a handle,
      ;; as `why`'s is — and `--nearest` belongs to the goal alone: a stored handle is
      ;; stored, so `:not-stored` is not the answer it can get, and there are no near
      ;; misses to look for.  So the pairing is refused rather than dropped, which is
      ;; `check-flags!`'s rule one level in: a flag honoured for one operand shape and
      ;; ignored for the other reads identically from outside.
      "why-not"     (cond
                      (and nearest (integer? (nth args 0)))
                      (throw (ex-info (str "--nearest takes a goal, not a handle: handle "
                                           (nth args 0) " is stored, so :not-stored is not"
                                           " the answer it can get and there is no rule to"
                                           " look for.  Write the sentence and its context.")
                                      {:type :unknown-option :flag "--nearest"
                                       :handle (nth args 0)}))

                      nearest (v/why-not kb (nth args 0) (or (second args) '?ctx) nearest)
                      (= 1 (count args)) (v/why-not kb (nth args 0))
                      :else (v/why-not kb (nth args 0) (nth args 1)))
      "in"          (v/in? kb (nth args 0))
      "isa"         (apply v/isa? kb args)
      "types-of"    (apply v/types-of kb args)
      "handle-of"   (v/handle-of kb (nth args 0) (nth args 1))
      ;; everything the KB holds about one term, by the term's role — the shell spelling
      ;; of "what can I ask about this?" (docs/troubleshooting.md).  `--context` is what
      ;; scopes it: the argument declarations, the grants and the comments are each read
      ;; from that context's genlCx up-cone, so two vantages give two correct answers
      "describe"    (v/describe kb (nth args 0) ctx)
      ;; `by-print-key`, never bare `sort`: a type node may be a NAT, and a NAT keyed with
      ;; `str` collapses under an ambient print bound
      "types"       (nm/by-print-key (v/types kb))
      "contexts"    (sort (v/contexts kb))
      "conflicts"   (v/conflicts kb)
      "contradictions" (v/contradictions kb)
      ;; the one command that answers in prose rather than in data: the report is four
      ;; distributions and a pretty-printed map of them is not a reading anybody takes.
      ;; `show` prints a string as-is, so the Markdown arrives as written
      "quality"     (v/quality-report (v/kb-quality kb))
      ;; the text KB format — one `Cx<Name>.txt` per context, the file name naming it
      ;; — which is what `export --format text` writes and what the shipped ontology is
      ;; authored in.  One order-insensitive pass over the whole directory, so a
      ;; context resting on another's content loads whichever name sorts first.
      "load"        (dissoc (v/load-text! kb (str (nth args 0))) :elapsed-ms)
      ;; the one command whose argument is a **destination** rather than knowledge.
      ;; Two formats, and they are two doors rather than one with a flag (docs/api.md):
      ;; a dump is the KB's state at its own handles, a text KB is its premises in the
      ;; format an author edits.  So `--variant` / `--compression` describe a dump and
      ;; are refused beside `--format text` rather than ignored — accepted and dropped,
      ;; a compression flag reads from the outside exactly like one that was applied.
      ;; Both arrive as strings and are the writer's own keywords, so they are read as
      ;; such rather than re-spelled here.
      "export"      (if (= "text" (:format opts))
                      (do (when-let [ignored (seq (sort (filter opts [:variant :compression])))]
                            (throw (ex-info (str "--format text writes a text KB, which has no "
                                                 (str/join " and no " (map name ignored))
                                                 " — those describe an export dump")
                                            {:type :unknown-option :unknown (vec ignored)
                                             :options [:format]})))
                          (v/export-text! kb (str (nth args 0))))
                      (v/export! kb (str (nth args 0))
                                 (cond-> {}
                                   (:variant opts)     (assoc :variant (keyword (:variant opts)))
                                   (:compression opts) (assoc :compression (keyword (:compression opts))))))
      ;; the one command that reads **two** KBs and neither of them is the one the run
      ;; opened: both arguments are text KBs on disk, each read into an in-RAM KB of its
      ;; own.  Keyed on content, so two exports of one KB taken at different handles diff
      ;; empty and a `diff` of the output means something (docs/api.md)
      "diff"        (v/kb-diff (str (nth args 0)) (str (nth args 1)))
      (throw (ex-info (str "unknown command: " cmd " — want one of "
                           (str/join ", " commands))
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
             (v/open-kb {:backend :disk-log :dir dir :recover? :auto})
             (v/open-kb {}))]
    (when starter (starter/load-into kb))
    kb))

;; ---- the shell -----------------------------------------------------------

(defn- show [x] (if (coll? x) (pp/pprint x) (println x)))

(defn- err!
  "One diagnostic line on **stderr** — a refusal must not land inside the data a
  script is reading off stdout."
  [& parts]
  (binding [*out* *err*] (apply println parts)))

(defn- repl-loop
  "Interactive loop: each line is `<cmd> <edn-forms…>` (no `--flags` — options are
  fixed at repl start).  Holds `kb` in-process, so a memory KB accumulates for the
  session.  Ends on `exit` / `quit` / EOF."
  [kb opts]
  (println "vaelii repl —" (str/join " " commands) "— or help, or exit")
  (loop []
    (print "vaelii> ") (flush)
    (when-let [line (read-line)]
      (let [line (str/trim line)]
        (cond
          (#{"exit" "quit"} line) (println "bye")
          (str/blank? line)       (recur)
          (#{"help" "--help"} line) (do (println (usage)) (recur))
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
                        ;; stdout on purpose, alone among the error paths: the REPL is a
                        ;; conversation, and its errors belong in the transcript beside
                        ;; the line that caused them — nothing scripts this stream
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
                                  (err! "error:" (.getMessage e))
                                  (System/exit 1)))
        [cmd & args] positionals
        ;; before the KB is opened: `--help` should answer on a machine with no KB,
        ;; and should not take a `--dir` lock to print a page of text
        _  (when (or (:help opts) (= cmd "help"))
             (println (usage))
             (System/exit 0))
        ;; and before the KB too, for the help arm's reason: a flag this command cannot
        ;; honour is the operator's mistake, and answering it should not first take a
        ;; `--dir` lock on a durable KB
        _  (try (check-flags! cmd opts)
                (catch clojure.lang.ExceptionInfo e
                  (err! "error:" (.getMessage e))
                  (System/exit 1)))
        kb (try (open-kb-from opts)
                ;; Throwable, matching the command arm below: an unwritable --dir or a
                ;; corrupt log throws a plain IOException, and a stack trace is not the
                ;; one-line courtesy this door promises
                (catch Throwable e
                  (err! "error:" (or (ex-message e) (.getName (class e))))
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
             (err! "error:" (.getMessage e))
             (System/exit 1))
           (catch Throwable e
             (err! "error:" (or (.getMessage e) (.. e getClass getSimpleName)))
             (System/exit 1)))

      :else
      (do (err! "unknown command:" cmd)
          (err! "commands:" (str/join " " commands))
          (err! "`lein cli help` for what each one takes")
          (System/exit 2)))))

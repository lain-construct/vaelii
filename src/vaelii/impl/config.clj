;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.config
  "The build's switches — the `vaelii.*` JVM system properties and the `VAELII_*`
  environment variables — read in one place, each against a domain, and **refused when
  the value is outside it**.

  This is `kb/check-opts!`'s invariant one layer out: *an option that is not read is not
  an option*.  A switch read as a membership test or an equality against one spelling has
  no wrong value — every misspelling falls to the other branch — so under that reading
  `vaelii.disk.auto-compact=disabled` is compaction **on** and `vaelii.disk.fsync=always`
  is the three-second tick, which is the durability level the operator is trying to
  leave.  A process that reports itself configured and is not is the failure
  `check-opts!` exists to prevent, on the property that decides whether a crash loses
  data.  So no switch is read that way here.

  ## One vocabulary for the boolean switches

  `truthy` and `falsy` below, case-insensitively, and nothing else: every boolean switch
  reads the same words, so a spelling that works on one works on all of them and a
  spelling that works on none is an error rather than the opposite setting.  A blank
  value is *unset* — an exported-but-empty environment variable is the shell's way of
  saying nothing.

  ## Where a refusal lands

  Each switch is read **once at a door**, never on a worker:

  - `check!` reads every switch here at `kb/open-kb`, so a wrong value fails the open —
    before a record is written and while what the operator typed is still legible.  It
    checks the whole set rather than the ones this KB's backend reads, because gating
    the check on the configuration is how a wrong value in the configuration escapes it.
  - `durability/compact-dead-ratio` and `compact-min-interval-ms` are read **per fsync
    tick**, inside `fsync-all`'s `catch Throwable`, which logs an exception's class name
    and nothing else.  A throw there is an unattributable log line repeating every three
    seconds with auto-compaction silently dead, which is why the eager `check!` exists
    rather than trusting the reader at its call site.
  - `arbitrate-constraints?` and `web-dev?` are read at **namespace load**, because each
    is the root value of a var and a var root cannot be deferred.  They refuse there,
    naming themselves, for `guard/max-body-bytes`' reason: a silent fallback leaves an
    operator believing a setting they never made, and a raw parse failure out of a `def`
    reports as a namespace that would not load rather than as the typo it is.
  - `log-level` is read at namespace load too (`vaelii.impl.logging`), for a different
    reason: it is the one switch whose effect is an *install*, and the door it belongs
    at is the moment the engine is loaded rather than the moment a KB is opened.  A
    process asks for a level once and gets it before the first line it wanted.

  ## What is not checkable here

  Five switches name a path or a label with no domain to check — `vaelii.disk.dir`,
  `vaelii.kb.path`, `vaelii.kb.catalog`, `vaelii.build`, `vaelii.clingo.lib` — and two
  name a member of a registry that resolves them itself: `vaelii.asp.solver`
  (`asp.solver/configured`) and `vaelii.llm.provider` (`llm.provider/configured`).  The
  ceiling `VAELII_MAX_BODY_BYTES` refuses at `guard/max-body-bytes`, where both servers
  read it."
  (:require [clojure.string :as str]))

(def truthy
  "The spellings that mean **on**, for every boolean switch.  One vocabulary rather than
  one per switch: a word that works for one switch works for all of them, so nothing is
  learned about `vaelii.disk.tokens` that is false of `vaelii.disk.auto-compact`."
  #{"true" "1" "on" "yes"})

(def falsy
  "The spellings that mean **off**.  Wider than `\"false\"` because the disk switches
  document `0` / `off` / `no` as well, and removing an accepted spelling breaks a setup
  that works."
  #{"false" "0" "off" "no"})

(defn- raw
  "The value of `nm` — a system property when it is spelled like one, an environment
  variable when it is spelled in caps — trimmed, or nil when unset or blank.  The
  spelling picks the source so a call site reads as one line; nothing in the tree names
  a switch both ways."
  [^String nm]
  (let [v (if (re-find #"^[A-Z]" nm) (System/getenv nm) (System/getProperty nm))]
    (when-not (str/blank? v) (str/trim v))))

(defn- refuse!
  "The one refusal shape: the switch, the value it was given, and what it accepts —
  named in the message, because an operator reading a log has only the message.  `data`
  carries the domain in whatever shape the domain has."
  [nm value want data]
  (throw (ex-info (str nm "=" value " is not a value " nm " reads — want " want)
                  (merge {:type :unknown-option :property nm :value value} data))))

(defn- boolean-vocabulary [] (vec (concat (sort truthy) (sort falsy))))

(defn prop-bool
  "`nm` as a boolean, `default` when unset.  Anything outside `truthy` / `falsy` is
  refused rather than read as the falsy branch, which is where `=disabled` meaning
  *enabled* came from."
  [nm default]
  (if-let [v (raw nm)]
    (let [s (str/lower-case v)]
      (cond
        (truthy s) true
        (falsy s)  false
        :else      (refuse! nm v (str "one of " (str/join ", " (boolean-vocabulary)))
                            {:accepted (boolean-vocabulary)})))
    default))

(defn prop-enum
  "`nm` as the value `accepted` maps its (lower-cased) spelling to, `default` when unset.
  `want` is the prose the refusal offers instead — a roster alone answers *what is
  legal* and not *what the legal one does*, and the second is what the operator who
  typed the wrong one needs."
  [nm accepted default want]
  (if-let [v (raw nm)]
    (let [s (str/lower-case v)]
      (if (contains? accepted s)
        (get accepted s)
        (refuse! nm v want {:accepted (vec (sort (keys accepted)))})))
    default))

(defn- refuse-number!
  "A number outside its domain, refused with the domain spelled as a range rather than
  as a roster — `0 to 1` says what `[0 1]` does not."
  [nm v kind lo hi]
  (refuse! nm v (str kind (cond (and lo hi) (str " from " lo " to " hi)
                                lo          (str ", " lo " or more")
                                :else       ""))
           {:min lo :max hi}))

(defn- prop-number
  "`nm` parsed by `parse`, `default` when unset, refused outside `lo`/`hi`.  The body the
  two readers below share; `kind` is the noun the refusal spells, and it is the only
  thing besides the parser that ever differed between them.

  The bound test compares the parsed number rather than a coercion of it, so a whole
  number past a double's exact range is still bounded exactly — the values read here are
  capacities and byte caps, which is precisely where a caller can name one that large."
  [nm default lo hi kind parse]
  (if-let [v (raw nm)]
    (let [n (try (parse v)
                 (catch NumberFormatException _
                   (refuse-number! nm v kind lo hi)))]
      (when (or (and lo (< n lo)) (and hi (> n hi)))
        (refuse-number! nm v kind lo hi))
      n)
    default))

(defn prop-long
  "`nm` as a long, `default` when unset.  `lo`/`hi` bound it — every count read here is a
  duration or a capacity, so one below zero is a typo rather than a setting."
  [nm default lo hi]
  (prop-number nm default lo hi "a whole number" #(Long/parseLong ^String %)))

(defn prop-double
  "`nm` as a double, `default` when unset, bounded by `lo`/`hi` as `prop-long` is."
  [nm default lo hi]
  (prop-number nm default lo hi "a number" #(Double/parseDouble ^String %)))

;; ---- the switches -------------------------------------------------------
;; One accessor per switch, holding its domain and its default.  The call sites read
;; through these, so the domain a value is refused against is the same one the reader
;; honours — a second spelling of either is how the two drift apart.

(defn disk-auto-compact?
  "Is background and opportunistic compaction on (`vaelii.disk.auto-compact`, default
  on)?  Read by the fsync tick and by the close path — one knob, not two."
  []
  (prop-bool "vaelii.disk.auto-compact" true))

(defn disk-fsync-mode
  "`vaelii.disk.fsync`: `:dsync` opens every log `rwd`, so an append is durable when it
  returns; `:tick` (the default, and what unset means) leaves durability to the
  `vaelii.disk.sync-ms` daemon."
  []
  (prop-enum "vaelii.disk.fsync" {"dsync" :dsync} :tick
             (str "\"dsync\" (fsync every append) or unset (the vaelii.disk.sync-ms"
                  " tick)")))

(defn disk-compress
  "`vaelii.disk.compress`: `:zstd`, `:lz4`, or nil for uncompressed frames (the
  default).  A `case` with a nil default arm is what made `=gzip` and `=zstdd` read as
  no compression at all — a store written smaller than the operator asked for, with
  nothing to say so."
  []
  (prop-enum "vaelii.disk.compress"
             {"none" nil "off" nil "false" nil "zstd" :zstd "lz4" :lz4}
             nil
             "zstd, lz4, or none"))

(defn disk-tokens?
  "Are sentex bodies written as token ids (`vaelii.disk.tokens`, default off)?  Off
  because it is the one part of the record store that adds a durable ground truth, so a
  store opts in.  *Reading* is never gated on it — a frame carries its own tag."
  []
  (prop-bool "vaelii.disk.tokens" false))

(defn disk-cache-capacity
  "Hot records held per kind (`vaelii.disk.cache`, default 65536; 0 disables the cache).
  A count, so it is read at the record store's open rather than at namespace load: a
  `Long/parseLong` in a top-level `def` turns `=64k` into a namespace that will not
  load, which reports the typo as a broken build."
  []
  (prop-long "vaelii.disk.cache" 65536 0 nil))

(defn disk-sync-ms
  "The durability daemon's tick, in milliseconds (`vaelii.disk.sync-ms`, default 3000;
  0 disables the daemon)."
  []
  (prop-long "vaelii.disk.sync-ms" 3000 0 nil))

(defn disk-compact-dead-ratio
  "The dead ratio a log must reach to be worth compacting
  (`vaelii.disk.compact-dead-ratio`, default 0.5).  A ratio, so outside 0–1 it is a
  threshold that either never fires or fires on every tick."
  []
  (prop-double "vaelii.disk.compact-dead-ratio" 0.5 0 1))

(defn disk-compact-min-interval-ms
  "The floor between two auto-compactions of one backend
  (`vaelii.disk.compact-min-interval-ms`, default 300000)."
  []
  (prop-long "vaelii.disk.compact-min-interval-ms" 300000 0 nil))

(defn disk-lock?
  "Is the single-writer `FileLock` taken when a directory opens (`vaelii.disk.lock`,
  default on)?  Off is for a filesystem whose `FileLock` is unreliable, and it removes
  the enforcement rather than the contract."
  []
  (prop-bool "vaelii.disk.lock" true))

(defn index-snapshot?
  "Is the mapped index image written and read (`vaelii.index.snapshot`, default off)?
  `index-snapshot/enabled?` is what call sites read — it adds the platform guard."
  []
  (prop-bool "vaelii.index.snapshot" false))

(defn belief-snapshot?
  "Is the belief certificate written on a full recover and read on the next cold open
  (`vaelii.belief.snapshot`, default off)?  When on, a clean disk KB's cold open skips the
  closing settle's definitional-clash scan and rederives identical belief
  (`vaelii.impl.disk.belief-snapshot`).  Off is byte-identical to never having the file."
  []
  (prop-bool "vaelii.belief.snapshot" false))

(defn arbitrate-constraints?
  "Does the process default to arbitrating a definitional clash rather than refusing it
  (`VAELII_ARBITRATE_CONSTRAINTS`, default off)?  A KB naming a `:constraints` policy
  overrides it."
  []
  (prop-bool "VAELII_ARBITRATE_CONSTRAINTS" false))

(defn assertive-arg-types?
  "Do the argument constraints entail as well as constrain (`VAELII_ASSERTIVE_ARG_TYPES`,
  default off)?"
  []
  (prop-bool "VAELII_ASSERTIVE_ARG_TYPES" false))

(defn web-dev?
  "Is the browser a development server (`VAELII_DEV`, default off)?  A value, not mere
  presence: `VAELII_DEV=0` says off and read as presence it said on."
  []
  (prop-bool "VAELII_DEV" false))

(defn profiler?
  "Should the sampling profiler's UI be started with the browser (`VAELII_PROFILER`,
  default off)?

  Off by default and asked for explicitly, because starting it is not free and not
  private: the profiler attaches an agent to this JVM and serves flamegraphs on a second
  port with no authentication of its own.  A reader who wants one says so."
  []
  (prop-bool "VAELII_PROFILER" false))

(defn profiler-port
  "The port the profiler's UI binds (`VAELII_PROFILER_PORT`, default 8080).  Read only
  when `profiler?` says to start one."
  []
  (prop-long "VAELII_PROFILER_PORT" 8080 1 65535))

(def asp-solver-spellings
  "What the ASP backend switch reads, one spelling per backend.  Unset is **auto** —
  in-process clingo when it loads, else clasp — which is why the reader's default is nil
  rather than a backend: `auto` is the absence of a choice, not a third one to name."
  {"clingo" :clingo "clasp" :clasp})

(defn asp-solver
  "Which ASP backend solves (`vaelii.asp.solver`, else `VAELII_ASP_SOLVER`), or **nil**
  for auto.  The property is read first, and both spellings refuse a name outside the
  roster: read as a bare `(keyword …)` a misspelt backend became a keyword nothing
  matches and the selector's fallback arm ran **auto**, so a run pinned to clasp could
  silently use clingo and report a clean pass for a backend nothing exercised."
  []
  (or (prop-enum "vaelii.asp.solver" asp-solver-spellings nil "clingo or clasp")
      (prop-enum "VAELII_ASP_SOLVER" asp-solver-spellings nil "clingo or clasp")))

(defn clingo-max-program-bytes
  "The plain-ASP program size above which **auto** routes to clasp even where clingo
  loads (`VAELII_CLINGO_MAX_BYTES`, default 3000).  An explicit backend ignores it."
  []
  (prop-long "VAELII_CLINGO_MAX_BYTES" 3000 0 nil))

(defn asp-time-limit
  "The seconds **one ASP solve** may run before the backend is interrupted
  (`VAELII_ASP_TIME_LIMIT`, default 60; 0 lifts the limit).  Both backends honour it —
  clasp through `--time-limit`, in-process clingo by cancelling the solve handle — and
  an interrupted solve reports `:interrupted`, which no consumer reads as an answer
  (`asp.edge`): the edge solver decides nothing and an imperative refuses.

  A solve runs on the single writer, so an unbounded one holds every write behind it —
  but an **operation** makes as many solves as it needs, each with the whole budget: two
  for a classification, three for `do/labeling`, one per defeat round for a settle.
  docs/asp.md tabulates the multipliers, and a test pins the counts so the table cannot
  drift from them."
  []
  (prop-long "VAELII_ASP_TIME_LIMIT" 60 0 nil))

(def log-level-spellings
  "What `VAELII_LOG_LEVEL` reads, one spelling per level the dial takes.  A def rather
  than a literal inside the reader so that the environment and
  `vaelii.core/set-log-level` can be checked to admit the same five: two rosters for one
  dial is one of them wrong."
  {"error" :error "warn" :warn "info" :info "debug" :debug "trace" :trace})

(defn log-level
  "The level the engine's own logging prints at (`VAELII_LOG_LEVEL`), or **nil** when
  unset — and nil is a setting rather than a default: with it unset the engine installs
  no backend at all, leaving whatever the host application put in
  `taoensso.trove/*log-fn*` (`vaelii.impl.logging`).  So there is no default to name
  here, and `=verbose` is refused rather than read as the one there would have been."
  []
  (prop-enum "VAELII_LOG_LEVEL" log-level-spellings nil
             "error, warn, info, debug or trace"))

(defn check!
  "Read every switch once, refusing the first whose value is outside its domain.
  `kb/open-kb` calls it, which is the earliest door that exists for the properties the
  durability daemon would otherwise read on a tick.

  Every switch and not this KB's: a `:memory` KB with `vaelii.disk.fsync=always` set is
  a process one directory away from a durability guarantee it does not have, and the
  next open is not a better place to hear about it."
  []
  (disk-auto-compact?)
  (disk-fsync-mode)
  (disk-compress)
  (disk-tokens?)
  (disk-cache-capacity)
  (disk-sync-ms)
  (disk-compact-dead-ratio)
  (disk-compact-min-interval-ms)
  (disk-lock?)
  (index-snapshot?)
  (arbitrate-constraints?)
  (assertive-arg-types?)
  (web-dev?)
  (profiler?)
  (profiler-port)
  (log-level)
  (asp-solver)
  (clingo-max-program-bytes)
  (asp-time-limit)
  nil)

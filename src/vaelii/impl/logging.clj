;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.logging
  "The log dial: how much the engine's own `trove/log!` calls print, as a value a
  *running* process can change.

  Verbosity is otherwise decided before a process starts, and the process that most
  needs a different setting is the one nobody can restart — a daemon a week into a run,
  on a `:disk` KB that pays `recover` on the way back up.  So the level is an **atom**,
  read per call by the one backend installed here; turning the dial is a `reset!` and
  never a second install, and two dials wrapped around each other is a state this cannot
  reach.

  ## The engine installs nothing unasked

  `vaelii.core/set-log-level` and `VAELII_LOG_LEVEL` install a backend.  Nothing else
  does: opening a KB does not, and neither does loading this namespace with the variable
  unset.  A library that replaces `taoensso.trove/*log-fn*` because it was *loaded*
  takes over the logging of the application that loaded it — a worse failure than a
  quiet engine, since the host loses its own lines and has nothing left to correlate.
  The variable is read at load, which is also the ordering that keeps it true: a host
  installing its own backend does so after requiring the engine, and wins.

  ## A level check, not a backend

  The sink is Trove's console backend and the ranking below is the whole of what this
  puts in front of it.  The ranking covers Trove's seven levels rather than the five the
  dial takes, so a message at `:fatal` or `:report` sorts above `:error` and prints
  under every setting instead of falling to a rank of zero and being suppressed by all
  of them."
  (:require [clojure.string :as str]
            [taoensso.trove :as trove]
            [taoensso.trove.console :as console]
            [vaelii.impl.config :as config]))

(def levels
  "Trove's levels, ranked.  A level this map does not name — nil, or a typo in a `log!`
  — sorts at the bottom with `:trace` and therefore *prints*: a message the dial cannot
  rank is one the operator should see, not one it silently drops."
  {:trace 0 :debug 1 :info 2 :warn 3 :error 4 :fatal 5 :report 6})

(def dial-levels
  "What the dial takes, quietest first.  Five of Trove's seven: `:fatal` and `:report`
  rank above everything the engine emits, so setting the floor there is asking for
  silence with extra steps, and the two are honoured as *message* levels either way."
  [:error :warn :info :debug :trace])

(def ^:private settable (set dial-levels))

(def ^:private dial
  "The level, or nil for *the engine has installed nothing* — which is not the same as
  `:info`, and the difference is what `current-level` reports."
  (atom nil))

(defn current-level
  "The level the dial holds, or nil when the engine has installed no backend.  Nil says
  the level is whatever `taoensso.trove/*log-fn*` already was — Trove's own console
  backend at `:info`, unless the host application installed one of its own."
  []
  @dial)

(defn enabled?
  "Is a message at `level` at or above the dial?  The level check, read per call, so the
  dial is one `reset!` rather than a reinstalled backend per change.

  With the dial unset every level is enabled, which is a reading the installed backend
  never sees: nothing is installed until the dial holds a level."
  [level]
  (>= (long (get levels level 0)) (long (get levels @dial 0))))

(def ^:private sink
  "Trove's console backend, unfiltered — `enabled?` is the filter in front of it.  A
  delay because building it resolves a timestamp formatter, and a process that never
  turns the dial should not pay for one."
  (delay (console/get-log-fn {:min-level :trace})))

(def ^:private log-fn
  "The one value this namespace ever installs into `*log-fn*`: the level check, then the
  console backend.  One value, installed idempotently, so turning the dial twice leaves
  one backend rather than two."
  (delay (let [emit @sink]
           (fn vaelii-log-fn [ns coords level id payload]
             (when (enabled? level) (emit ns coords level id payload))))))

(defn set-level
  "Set the dial to `level` and install the console backend at the root of
  `taoensso.trove/*log-fn*`, returning the level.  `vaelii.core/set-log-level` is the
  public spelling.

  A level outside `dial-levels` is **refused by name** (`:type :unknown-option`) rather
  than defaulted: a dial that reads `:verbose` as `:info` is one an operator turns and
  believes, and the failure mode worth refusing is the one that leaves a process
  silent."
  [level]
  (when-not (settable level)
    (throw (ex-info (str "no such log level: " (pr-str level) " — want one of "
                         (str/join ", " (map pr-str dial-levels)))
                    {:type :unknown-option :level level :known dial-levels})))
  (reset! dial level)
  (alter-var-root #'trove/*log-fn* (constantly @log-fn))
  level)

;; The environment's one call, made at load rather than at `open-kb`: a level named in
;; the environment is the operator's explicit install, and opening a KB is not.  Unset,
;; this is the whole of what loading the engine does to `*log-fn*` — nothing.
(when-let [level (config/log-level)]
  (set-level level))

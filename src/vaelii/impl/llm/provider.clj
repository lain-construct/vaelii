;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.llm.provider
  "Which backend a turn runs against — the selection seam.

  Stands where `vaelii.impl.asp.solver` stands for the ASP backends: a keyword names a
  backend, the backend is **lazily resolved** so choosing one is what loads it, and an
  unreachable backend falls back to the deterministic default rather than throwing.
  `vaelii.impl.llm.stub` is that default, exactly as `vaelii.impl.solve/local-solver`
  is for contradictions — so a build with no credential, no Ollama and no network runs
  the whole pipeline and opens no socket.

  Three kinds:

    :stub       deterministic, offline, scriptable — the default
    :ollama     a local Ollama (`vaelii.impl.llm.ollama`), no credential
    :anthropic  the Messages API (`vaelii.impl.llm.anthropic`), credential required

  Select with `VAELII_LLM_PROVIDER` or `-Dvaelii.llm.provider`; a caller that already
  knows what it wants passes the kind (or a built provider) directly.

  Resolution is lazy for a reason beyond load time: `anthropic/available?` may shell
  out to the `ant` CLI, and `ollama/available?` opens a socket.  Neither should happen
  because a namespace was required."
  (:require [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.impl.llm.stub :as stub]))

(def kinds
  "The backends `provider` knows how to build, in the order `first-available` tries
  them: the local one before the remote one, since a model already on the machine is
  the one to prefer.  Not because asking is cheaper — `ollama/available?` is an HTTP
  GET that waits up to its two-second timeout on an unreachable host, where
  `anthropic/available?` is two `getenv` reads before it shells out at all.  The local
  probe is the slow one and goes first anyway, because what it decides is which model
  answers rather than how fast the decision is taken."
  [:stub :ollama :anthropic])

(def ^:private backend-ns
  {:ollama    'vaelii.impl.llm.ollama
   :anthropic 'vaelii.impl.llm.anthropic})

(defn configured
  "The backend named by `VAELII_LLM_PROVIDER` / `-Dvaelii.llm.provider`, or nil."
  []
  (some-> (or (System/getProperty "vaelii.llm.provider")
              (System/getenv "VAELII_LLM_PROVIDER"))
          str/trim str/lower-case not-empty keyword))

(defn- resolve-fn
  "A backend's var, or nil when the namespace does not load in this build."
  [kind sym]
  (when-let [ns-sym (backend-ns kind)]
    (try (requiring-resolve (symbol (name ns-sym) (name sym)))
         (catch Throwable _ nil))))

(defn available?
  "Can this backend actually serve a turn right now?  `:stub` always can; `:ollama`
  probes the host; `:anthropic` looks for a credential.  Never throws — an
  unreachable backend answers false."
  ([kind] (available? kind {}))
  ([kind opts]
   (case kind
     :stub true
     (boolean (when-let [f (resolve-fn kind 'available?)]
                (try (if (= :ollama kind) (f opts) (f))
                     (catch Throwable _ false)))))))

(defn- call-builder
  "Call one of a backend's constructors, or nil when the namespace does not load in this
  build (silent — a backend nobody compiled in is not a fault) or when the constructor
  throws (**logged**).  Logged, not swallowed: a caller reaches a constructor after
  `available?` has said yes, so a throw here means the backend is half-present, and
  falling quietly through to the stub answers with plausible fabricated text instead of
  a diagnosis.

  `opts` never reaches the log line: it may carry a credential."
  [kind sym opts]
  (when-let [f (resolve-fn kind sym)]
    (try (f opts)
         (catch Throwable t
           (trove/log! {:level :warn :id ::provider-build-failed :error t
                        :msg "backend probed available but would not build; using the stub"
                        :data {:kind kind}})
           nil))))

(defn build
  "Build the named backend, or nil when it cannot be built.  `opts` is handed to the
  backend's own `provider` constructor, and a constructor that throws is logged
  (`call-builder`) rather than swallowed."
  ([kind] (build kind {}))
  ([kind opts]
   (if (= :stub kind)
     (stub/provider opts)
     (call-builder kind 'provider opts))))

(defn provider
  "The `Provider` to run a turn against.

  With no `kind`, the configured one — and the stub when nothing is configured, when
  the configured backend is unreachable, or when it cannot be built.  **Falling back is
  the point**: an application that cannot reach its model degrades to a provider that
  proposes nothing rather than to an exception, which is how the ASP seam behaves and
  what makes the pipeline testable everywhere.

  Falling back is not the same as falling silent: a backend that probes available and
  then will not build is a broken backend, and it is logged where it happens
  (`call-builder`), because from the outside that is indistinguishable from a model that
  proposed nothing.

  Pass a kind to demand one; it still falls back, so a caller that must know asks
  `available?` first."
  ([] (provider (or (configured) :stub) {}))
  ([kind] (provider kind {}))
  ([kind opts]
   (or (when (available? kind opts) (build kind opts))
       (stub/provider {}))))

(defn active-kind
  "Which backend `(provider)` will hand back right now — for diagnostics, and for a
  UI that wants to say what it is talking to."
  ([] (active-kind {}))
  ([opts]
   (let [k (or (configured) :stub)]
     (if (and (available? k opts) (build k opts)) k :stub))))

(defn generation-provider
  "The provider for a **generation** turn (`vaelii.impl.llm.session/propose-page`) —
  `provider`, except that a backend naming a distinct generation model is built through
  that name instead.  Ollama does: editing shown lines and writing new knowledge are
  different jobs whose best models differ, and a page turn run on the edit model produces
  nothing usable.  A backend with no such split falls through to its ordinary
  constructor, and an unreachable one falls back to the stub, exactly as `provider` does.

  The reachability probe carries only `:host` from `opts`, never the turn's `:timeout-ms`
  — a probe is a health check and keeps its own short deadline, so a caller that allows a
  turn a minute does not thereby allow the gate a minute on a host that never answers."
  ([] (generation-provider (or (configured) :stub) {}))
  ([kind] (generation-provider kind {}))
  ([kind opts]
   (or (when (available? kind (select-keys opts [:host]))
         (if (resolve-fn kind 'generation-provider)
           (call-builder kind 'generation-provider opts)
           (build kind opts)))
       (stub/provider {}))))

(defn warm
  "Make a backend ready to answer fast, and hold it that way — what an application calls
  at start so a reader's first turn is not the one that pays for loading the weights.
  Returns whatever the backend reports, or nil when it has none to do (the stub is
  already warm, and a hosted API has no local model to load).  Never throws: warming is
  an optimization, and a host that is down is the ordinary case a fallback already
  covers."
  ([] (warm (or (configured) :stub)))
  ([kind]
   (when-let [f (resolve-fn kind 'warm)]
     (try (f) (catch Throwable _ nil)))))

(defn first-available
  "The first backend in `kinds` that can serve a turn — `:stub` at worst, since it
  always can.  For a caller with no preference that would still rather use a real
  model than propose nothing."
  ([] (first-available {}))
  ([opts] (or (first (filter #(and (not= :stub %) (available? % opts)) kinds)) :stub)))

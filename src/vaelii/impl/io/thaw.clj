;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.io.thaw
  "The class-name door on every nippy thaw the engine runs over a file.

  A frozen nippy value can **name a class** in three of its type ids, and reading one
  resolves that name and builds an instance of it: a record frame (`Class/forName`, then
  the static `create`), a deftype frame (`Class/forName`, then the first public
  constructor over the fields that follow), and a `Serializable` frame (an
  `ObjectInputStream` over the bytes that follow).  nippy 3.8.1 gates the third behind
  `*thaw-serializable-allowlist*` and the first two behind nothing at all.

  Every file the engine reads is **untrusted input** — a store directory or a dump
  arrives from wherever an operator copied it — so all three are gated here, and the
  gate is the tightest one there is:

  > **A vaelii frame never carries a class name.**

  That is already the export format's stated rule (`vaelii.impl.io.export`), and the
  disk codec writes a record's fields **positionally** for a size reason
  (`vaelii.impl.disk.codec`), so nothing the engine writes states a class either.  A
  frame that names one therefore came from somewhere else, and `allowed-classes` is
  empty: the name is refused (`:disallowed-class`) before the class is resolved.

  **The `Serializable` allowlist is pinned rather than inherited.**  nippy's default is
  a safe set, but it lives in a dynamic var an embedding application is invited to
  widen — nippy documents `allow-and-record-any-serializable-class-unsafe` for exactly
  that migration — and a host that widened it would widen the engine's file readers with
  it.  Binding it per read makes the door this namespace's rather than the host's.

  **How the first two are gated**, since nippy exposes no hook for them: the readers
  `taoensso.nippy.io` dispatches to are vars, and this namespace installs a checked
  reader in place of each.  A refusal is thrown from there, which is *before* nippy's own
  `try` — so it travels rather than becoming the `{:nippy/unthawable …}` placeholder a
  failed resolution otherwise reads as, and no class is loaded on the way.  The
  replacement calls straight through to the reader it replaced unless `with-guard` is in
  force, so a host application thawing its own records in this JVM is unaffected."
  (:require [taoensso.nippy :as nippy]
            [taoensso.nippy.io :as nippy-io]))

(def allowed-classes
  "The class names a file the engine wrote may state — **none**.

  Measured rather than asserted: a store built on each of the four durable backends and
  a dump written in each variant and codec drive nippy's three class-name readers zero
  times.  A dump frame is a field map, a log frame is a positional vector, and every
  leaf a sentence may carry is a type nippy has an id for (`vaelii.impl.checks`'
  `check-encodable` refuses the rest at the front door).  So the allowlist is empty, and
  a name is a name this engine did not write.

  A set rather than `false` because the refusal names the class either way, and because
  a format that one day carried one would add it here and nowhere else."
  #{})

(def ^:dynamic *guarding*
  "Is a thaw inside `with-guard`?  The checked readers below stand in for nippy's own
  process-wide, so this is what keeps the gate the engine's own: false — a host
  application's thaw — calls straight through."
  false)

(defn- refuse-class!
  "Refuse the class name a frame states, naming it and which reader met it."
  [reader ^String class-name]
  (throw (ex-info (str "a frame names the class " class-name
                       " — a vaelii dump or store never carries a class name (its frames"
                       " are field maps and positional vectors), so this file was written"
                       " by something else, and resolving the name would load and"
                       " instantiate it")
                  {:type :disallowed-class :class class-name :reader reader
                   :allowed allowed-classes})))

(defn- serializable-allowed?
  "The predicate nippy's `Serializable` reader asks before it opens an
  `ObjectInputStream` over the bytes a frame carries.  A predicate rather than a set
  because nippy calls one directly (`taoensso.nippy.impl/serializable-allowed?`), which
  is what lets the refusal name the class here instead of arriving as a quarantined
  placeholder the caller has to go looking for."
  [class-name]
  (or (contains? allowed-classes class-name)
      (refuse-class! :serializable class-name)))

;; ---- the two readers nippy gates behind nothing --------------------------
;; Installed once, at load.  `defonce` on the originals, so reloading this namespace in
;; a REPL does not wrap a wrapper: what is captured the first time is nippy's own.

(defonce ^:private original-read-record  nippy-io/read-record)
(defonce ^:private original-read-deftype nippy-io/read-deftype)

;; Read by nothing: the value is the install having happened, and requiring this
;; namespace is what runs it.  `defonce` rather than a bare `do`, so a REPL reload
;; replaces neither reader.
#_{:clj-kondo/ignore [:unused-private-var]}
(defonce ^:private installed
  (do
    (alter-var-root #'nippy-io/read-record
                    (constantly
                     (fn [ibr class-name]
                       (when (and *guarding* (not (contains? allowed-classes class-name)))
                         (refuse-class! :record class-name))
                       (original-read-record ibr class-name))))
    (alter-var-root #'nippy-io/read-deftype
                    (constantly
                     (fn [ibr class-name legacy?]
                       (when (and *guarding* (not (contains? allowed-classes class-name)))
                         (refuse-class! :deftype class-name))
                       (original-read-deftype ibr class-name legacy?))))
    true))

(defmacro ^:private with-guard
  "Run `body` with the class-name door closed: the two checked readers armed, and the
  `Serializable` allowlist pinned to this namespace's.  One binding frame, so a caller
  that opens the door once for a run of frames pays one push and one pop."
  [& body]
  `(binding [*guarding*                          true
             nippy/*thaw-serializable-allowlist* serializable-allowed?]
     ~@body))

(defn- refusal
  "The `:disallowed-class` refusal in `t`'s cause chain, or nil.  `nippy/thaw` catches
  what a reader throws and re-throws it as its own \"Thaw failed\" `ex-info` with the
  original as the cause — a fair report of a *damaged* file and the wrong one for a
  refusal, which is a claim about the file's content and carries the class name in its
  `ex-data`.  So the chain is walked and the refusal raised as itself."
  [^Throwable t]
  (loop [^Throwable e t]
    (cond
      (nil? e)                                     nil
      (= :disallowed-class (:type (ex-data e)))    e
      :else                                        (recur (.getCause e)))))

(defn guarded
  "Run `f` — a thunk that thaws — behind the door, raising a `:disallowed-class` refusal
  as itself rather than as whatever wrapped it.

  The entry point for a caller reading **many** frames off one stream
  (`vaelii.impl.io.frames`): the door is opened once for the run instead of once per
  frame, which is one binding frame for ten thousand of them."
  [f]
  (try (with-guard (f))
       (catch Throwable t (throw (or (refusal t) t)))))

(defn thaw
  "`nippy/thaw` of `bs` behind the door."
  [^bytes bs]
  (guarded (fn [] (nippy/thaw bs))))

(defn thaw-from-in!
  "`nippy/thaw-from-in!` from `in` behind the door."
  [^java.io.DataInput in]
  (guarded (fn [] (nippy/thaw-from-in! in))))

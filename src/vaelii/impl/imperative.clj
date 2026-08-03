;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.imperative
  "The `do/` imperatives — the one shape given to `assert` that is neither a fact nor
  a rule but an *instruction*: run a labeling / classification and return its result,
  storing nothing.  `assert` dispatches a `do/` form here (`run`) before any naming or
  well-formedness check, since those expect a sentence.

  This is not part of the assertion write-path — it is a separate feature (answer-set
  labeling, docs/labeling.md) routed through `assert` for one entry point — so it lives
  outside `vaelii.core`.  The backing functions live under `vaelii.impl.asp.*`, which
  requires the engine, so they are resolved **lazily**: a static require would be
  circular, and the resolve keeps ASP optional (a build without a backend still loads,
  and the backend choice is made inside the resolved fn).  An unavailable build throws a
  legible error rather than failing to load the engine."
  (:require [clojure.string :as str]))

(defn- imperative-fn
  "Resolve the function backing a `do/` imperative, or throw naming the ones there are."
  [functor]
  (let [known {'do/labeling 'vaelii.impl.asp.label/label-dilemmas
               'do/label    'vaelii.impl.asp.solve-context/label
               'do/classify 'vaelii.impl.asp.solve-context/classify}]
    (if-let [sym (known functor)]
      (or (requiring-resolve sym)
          (throw (ex-info (str "imperative " functor " is unavailable in this build")
                          {:type :not-assertible :form functor :wanted sym})))
      (throw (ex-info (str "unknown imperative " functor
                           "; known: " (str/join ", " (sort (map str (keys known)))))
                      {:type :not-assertible :form functor :known (set (keys known))})))))

(defn run
  "Run a `do/` imperative and return **its result**, not a handle.

  `assert` returns a handle because asserting stores something; an imperative stores
  nothing, so there is no handle to return and the useful answer is what it did.  A
  `do/` form is already outside the assertion contract — like `ist`, it is a form given
  to `assert` that is not a fact — so this is the third shape `assert` can return, and
  the one a caller asked for by writing an imperative.

  `(do/labeling Ctx)` classifies the dilemmas the KB currently holds and commits to one
  optimal labeling of them inside `Ctx` (docs/labeling.md).  `(do/label Base Into)`
  grounds the `assumptionRules` visible from `Base` and materializes one **inert**
  labeling context per optimal answer set; `(do/classify Into)` gathers brave/cautious
  over those labelings (docs/solving.md)."
  [kb sentence context]
  (let [[functor & args] sentence
        f (imperative-fn functor)
        ctx-arg? (fn [x] (and x (symbol? x)))]
    (case functor
      do/labeling (let [[ctx base] args]
                    (when-not (and (ctx-arg? ctx) (or (nil? base) (symbol? base))
                                   (<= (count args) 2))
                      (throw (ex-info "(do/labeling Ctx [Base]) wants context names"
                                      {:type :not-assertible :sentence sentence})))
                    (f kb ctx (or base context)))
      do/label    (let [[base into mode] args]
                    (when-not (and (ctx-arg? base) (ctx-arg? into)
                                   (or (= 2 (count args))
                                       (and (= 3 (count args)) (#{:one :sat :all} mode))))
                      (throw (ex-info "(do/label Base Into [:one|:sat|:all]) wants two context names and an optional mode"
                                      {:type :not-assertible :sentence sentence})))
                    (f kb base into (or mode :all)))
      do/classify (let [[into] args]
                    (when-not (and (ctx-arg? into) (= 1 (count args)))
                      (throw (ex-info "(do/classify Into) wants one context name"
                                      {:type :not-assertible :sentence sentence})))
                    (f kb into)))))

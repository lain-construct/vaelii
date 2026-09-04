;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.opts
  "The option-map entry point: a key nothing reads is refused, and so is an `opts` that is not
  a map.

  Nearly every public entry point that takes trailing options wants exactly this, and
  wants it for one reason: **an option nothing reads takes the default in silence.**
  That is the quietest failure the API has — `{:max-derivation 5}` for `:max-derivations`
  reads as no bound at all and the chain runs unbounded, `{:strengh :monotonic}` stores a
  default where known-true was meant, `{:varient :index}` writes a dump other than the one
  asked for.  Each returns a handle, a count, a summary that looks exactly right.

  So every such entry point runs one shape, identically bar the noun and one sentence, and this
  is that shape once.  What a caller supplies is the key set, the `subject` the
  message names, and the `consequence` — the clause saying what taking the default
  silently would have cost *here*, which is the sentence worth writing per entry point and the
  only part of the refusal that ever carried information the others did not.

  An entry point with further checks on the *values* of known keys keeps them; this is the key
  check, and it runs first because a misspelt key is not a bad value — it is a key that
  is not there."
  (:require [clojure.string :as str]))

(defn check!
  "Refuse a non-nil non-map `opts`, and any key outside `opt-keys` — `:unknown-option`
  both, carrying `:options` (the roster) and, for the second, `:unknown` (what was
  passed).  `subject` names the entry point in the message; `consequence` is the clause on what
  the silent default would have done, and may be nil where the roster speaks for itself.

  `opt-keys` is a set, used as the membership predicate and sorted for the message.

  The second `map?` is redundant to a reader and required to clj-kondo, which does
  not narrow a type through a `when` whose body throws: a bare `(keys opts)` below tells
  it `opts` is seqable, and it propagates that up through every caller to
  `vaelii.core/assert`'s own signature — where the suite's deliberate `:nope` becomes a
  type error.  The guard is the narrowing, so keep it."
  ([opts opt-keys subject] (check! opts opt-keys subject nil))
  ([opts opt-keys subject consequence]
   (when (and (some? opts) (not (map? opts)))
     (throw (ex-info (str subject " options must be a map, got " (pr-str opts))
                     {:type :unknown-option :mismatch :not-a-map :options (vec (sort opt-keys))})))
   (when-let [unknown (and (map? opts)
                           (seq (sort-by pr-str (remove opt-keys (keys opts)))))]
     (throw (ex-info (str "unknown " subject " option" (when (next unknown) "s") " "
                          (str/join ", " (map pr-str unknown))
                          " — " subject " reads "
                          (str/join ", " (map pr-str (sort opt-keys)))
                          (when consequence (str ".  " consequence)))
                     {:type :unknown-option :mismatch :unknown-key :unknown (vec unknown)
                      :options (vec (sort opt-keys))})))))

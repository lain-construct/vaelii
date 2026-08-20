;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.datetime
  "ISO 8601 datetime containment — the first time dimension for context NATs
  (docs/context-nat.md).

  A `DatetimeFn` is a **structural** (`unreifiableFunction`) constructor taking a
  reduced-precision ISO 8601 string that denotes an *interval*: `\"2000\"` is the year,
  `\"2000-01\"` its January, `\"2000-01-15\"` a day, `\"2000-01-15T13\"` an hour, and so on
  down through minute and second.  Because the string stays readable inside the context
  expression (an unreifiable NAT is never minted), the structural genlCx producer can read
  two `DatetimeFn` terms and decide containment from their shape alone.

  Containment is **field nesting**: a more-precise instant is inside a less-precise one
  whose fields it shares — `\"2000-01\" ⊆ \"2000\"`, `\"2000-01-15\" ⊆ \"2000-01\"`, while
  `\"2001\" ⊄ \"2000\"` (the year differs) and `\"2000\" ⊄ \"2000-01\"` (the year is the
  *coarser* interval, so it contains the month, not the other way).

  Everything here is a **pure, bounded** computation — parse two short strings and compare
  vectors — so the producer may call it inside the settle/relabel loop, where a prover
  search is forbidden (docs/naf.md).  Fields are compared by numeric value, so `\"2000-1\"`
  and `\"2000-01\"` denote the same month."
  (:require [clojure.string :as str]))

(def datetime-function
  "The structural constructor this namespace reads.  A `DatetimeFn` application is the
  time term inside a `(CxTimeFn <dimension> (DatetimeFn <iso>))` context."
  'DatetimeFn)

(defn- parse
  "The ISO string as a vector of integer fields `[year month day hour minute second]`,
  truncated at the string's own precision — or `nil` when it is not a well-formed
  reduced-precision ISO datetime.  Fields are numeric, so `\"2000-1\"` and `\"2000-01\"`
  parse equal."
  [s]
  (when (string? s)
    (let [[date time] (str/split s #"T" 2)
          parts (concat (str/split date #"-") (when time (str/split time #":")))]
      (when (and (<= 1 (count parts) 6)
                 (every? #(re-matches #"\d+" %) parts))
        (mapv #(Long/parseLong ^String %) parts)))))

(defn datetime-term?
  "True iff `form` is a `(DatetimeFn \"<iso>\")` term with a parseable ISO string."
  [form]
  (and (sequential? form) (= 2 (count form))
       (= datetime-function (first form))
       (some? (parse (second form)))))

(defn subinterval?
  "True iff datetime term `a` denotes an interval contained in `b`'s — `b`'s fields are a
  prefix of `a`'s and equal field-by-field (reflexive).  The interval reading of ISO
  reduced precision: fewer fields is a coarser, larger interval, and a finer interval
  sharing every coarser field sits inside it.  Returns `false` for anything that is not a
  pair of datetime terms, so a caller can hand it any two argument terms."
  [a b]
  (boolean
   (when (and (datetime-term? a) (datetime-term? b))
     (let [pa (parse (second a)) pb (parse (second b))]
       (and (<= (count pb) (count pa))
            (= pb (subvec pa 0 (count pb))))))))

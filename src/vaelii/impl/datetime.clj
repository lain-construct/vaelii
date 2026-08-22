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

(def ^:private field-ranges
  "The inclusive bounds of each field after the year, in field order: month, day, hour,
  minute, second.  Day is bounded at 31 whatever the month — the shape check is what the
  containment reading needs, not a calendar.  The year's own bound is its **width**
  (`year-pattern`), which is what ISO 8601 gives it."
  [[1 12] [1 31] [0 23] [0 59] [0 59]])

(def ^:private year-pattern
  "A year is one to four digits — ISO 8601's four-digit calendar year, with the
  zero-padding treated as optional the way every field after it is.

  The width is the bound, and it is load-bearing twice.  It is what refuses
  `\"20260821\"`, the **basic** ISO format: without a width the separator-less date reads
  as the year 20,260,821, so `\"20260821\"` and `\"2026-08-21\"` would name unrelated
  intervals while looking like the same day, and only one of them would nest under
  `\"2026\"`.  This namespace reads the extended format alone, so the basic one is
  refused rather than misread.  It is also what keeps the parse **bounded**: four digits
  fit a `Long`, so no input can make the read throw where the caller — the structural
  genlCx producer, inside the settle/relabel loop — has no way to handle one."
  #"\d{1,4}")

(def ^:private field-pattern
  "Every field after the year is one or two digits: `\"2000-1\"` and `\"2000-01\"` denote
  the same month, and `\"2000-001\"` denotes nothing.  Two digits also keep each field's
  read inside a `Long`, so the range check below is what refuses an out-of-range field
  rather than the parse throwing before it is reached."
  #"\d{1,2}")

(defn- parse
  "The ISO string as a vector of integer fields `[year month day hour minute second]`,
  truncated at the string's own precision — or `nil` when it is not a well-formed
  reduced-precision ISO datetime.  Fields are numeric, so `\"2000-1\"` and `\"2000-01\"`
  parse equal.

  Well-formed means the date and time halves are each bounded on their own — one to
  three `-`-separated date fields, and after a `T` one to three `:`-separated time
  fields, a time part admitted only behind a full date — every field is of its own
  width (`year-pattern` / `field-pattern`), and every field after the year is in range.
  Bounding only the total count would read `\"2000T13:00\"` as year-month-day and
  `\"2000-01-15-12\"` as a date with an hour, and `subinterval?` would then nest
  intervals the strings never named.

  **Total, and that is a contract rather than a convenience.**  Every rejection is a
  `nil`; nothing here throws on any string, however long or however shaped, because the
  producer that calls it runs inside the settle/relabel loop."
  [s]
  (when (string? s)
    (let [[date time] (str/split s #"T" 2)
          date-parts (str/split date #"-" -1)
          time-parts (when time (str/split time #":" -1))
          parts      (concat date-parts time-parts)]
      (when (and (<= 1 (count date-parts) 3)
                 (or (nil? time)
                     (and (= 3 (count date-parts)) (<= 1 (count time-parts) 3)))
                 (re-matches year-pattern (first parts))
                 (every? #(re-matches field-pattern %) (rest parts)))
        (let [fields (mapv #(Long/parseLong ^String %) parts)]
          (when (every? (fn [[v [lo hi]]] (<= lo v hi))
                        (map vector (rest fields) field-ranges))
            fields))))))

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

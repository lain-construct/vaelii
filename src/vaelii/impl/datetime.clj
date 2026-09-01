;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.datetime
  "Calendar containment — the first time dimension for context NATs
  (docs/context-nat.md), read off two spellings of the same interval.

  A `DatetimeFn` is a **structural** (`unreifiable_function`) constructor taking a
  reduced-precision ISO 8601 string that denotes an *interval*: `\"2000\"` is the year,
  `\"2000-01\"` its January, `\"2000-01-15\"` a day, `\"2000-01-15T13\"` an hour, and so on
  down through minute and second.  Because the string stays readable inside the context
  expression (an unreifiable NAT is never minted), the structural genlCx producer can read
  two such terms and decide containment from their shape alone.

  `YearFn` / `MonthFn` / `DayFn` are the **calendar constructors** over the same three
  coarsest fields, written as numbers instead of as a string: `(YearFn 2000)`,
  `(MonthFn 2000 1)`, `(DayFn 2000 1 15)`.  They are unreifiable for the same reason
  `DatetimeFn` is — the fields are what the ordering reads, and a minted constant would
  hide them — and each carries **one field per argument**, so the arity *is* the
  precision and there is no string to parse or mis-parse.  A calendar term and the ISO
  string naming the same interval read to the same fields, so the two spellings order
  against each other as readily as against themselves.

  Containment is **field nesting**: a more-precise interval is inside a less-precise one
  whose fields it shares — `(MonthFn 2000 1) ⊆ (YearFn 2000)`, `\"2000-01-15\" ⊆
  \"2000-01\"`, while `\"2001\" ⊄ \"2000\"` (the year differs) and `\"2000\" ⊄ \"2000-01\"`
  (the year is the *coarser* interval, so it contains the month, not the other way).
  Two sibling months nest neither way, which is what keeps January's facts out of
  February.

  `InstantFn` is the other half, and the one thing here that is about **moments** rather
  than stretches: `(InstantFn 2000 1 1 0 0 0)` is one instant, six integer fields wide,
  and `bounds` reads a calendar term to the two of them it lies between — half-open, so
  the end of 1999 and the start of 2000 are the *same* term.  `vaelii.impl.calendar`
  answers `startOf` / `endOf` and the orderings out of that (docs/time.md).

  Everything here is a **pure, bounded** computation — parse two short forms and compare
  vectors — so the producer may call it inside the settle/relabel loop, where a prover
  search is forbidden (docs/naf.md).  Fields are compared by numeric value, so `\"2000-1\"`
  and `\"2000-01\"` denote the same month, and so does `(MonthFn 2000 1)`."
  (:require [clojure.string :as str])
  (:import (java.time DateTimeException LocalDateTime)))

(def datetime-function
  "The structural ISO constructor this namespace reads.  A `DatetimeFn` application is one
  time term inside a `(CxTimeFn <dimension> (DatetimeFn <iso>))` context."
  'DatetimeFn)

(def calendar-functions
  "The structural **calendar** constructors, `functor → field count`.  Each takes one
  integer per calendar field, coarsest first, so its arity is its precision:
  `(YearFn 2000)`, `(MonthFn 2000 1)`, `(DayFn 2000 1 15)`.

  Three and not six.  A year, a month and a day are the granularities a context is keyed
  by — the ones somebody writes a holiday or a policy for — and each finer field is a
  spelling ISO already gives (`(DatetimeFn \"2000-01-15T13\")`), read to the same fields
  by the same comparator.  A constructor per clock field would add nothing the ordering
  can see."
  '{YearFn 1, MonthFn 2, DayFn 3})

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

(def ^:private year-range
  "The inclusive bounds of a **calendar constructor's** year argument.  The ISO year's
  bound is its width (`year-pattern`); a number has no width, so the width is restated
  here as the range it denotes.  Both spellings therefore admit exactly the same years,
  which is what lets `(YearFn 2000)` and `(DatetimeFn \"2000\")` name one interval."
  [0 9999])

(defn- fields-in-range?
  "Are numeric `fields` well formed — every one an integer, the year inside `year-range`
  and every later field inside its own?  The shape test both numeric readers run, the
  calendar constructors' below and `instant-fields`' further down, so the two admit
  exactly the same fields and a moment cannot be spelled where an interval cannot.
  Total, like everything else here."
  [fields]
  (and (every? integer? fields)
       (<= (first year-range) (long (first fields)) (second year-range))
       (every? (fn [[v [lo hi]]] (<= lo (long v) hi))
               (map vector (rest fields) field-ranges))))

(defn- calendar-fields
  "The fields of a calendar term `(YearFn Y)` / `(MonthFn Y M)` / `(DayFn Y M D)`, or nil
  for anything that is not one.  The functor fixes how many arguments there must be, every
  argument is an integer, and every one is in its field's range — so a malformed
  constructor denotes nothing rather than denoting an interval nobody wrote.

  **Total**, exactly as `parse` is: every rejection is a nil, because the caller runs
  inside the settle/relabel loop and has nowhere to put a throw."
  [form]
  (when (sequential? form)
    (when-let [n (get calendar-functions (first form))]
      (let [args (vec (rest form))]
        (when (and (= n (count args)) (fields-in-range? args))
          (mapv long args))))))

(defn- term-fields
  "The fields of a time term — a `(DatetimeFn \"<iso>\")` or one of the calendar
  constructors — or nil for anything that is neither.  Every reader below goes through
  this, so a term is read once per question rather than once to recognize it and again to
  read it, which matters because the caller is the structural genlCx producer, inside the
  settle/relabel loop.

  One field vector for both spellings is the whole of the bridge between them: the
  comparator never learns which constructor it was handed, so `(MonthFn 2000 1)` and
  `(DatetimeFn \"2000-01\")` are ordered against each other and against `(YearFn 2000)`
  by the one rule."
  [form]
  (when (sequential? form)
    (if (= datetime-function (first form))
      (when (= 2 (count form)) (parse (second form)))
      (calendar-fields form))))

(defn datetime-term?
  "True iff `form` is a `(DatetimeFn \"<iso>\")` term with a parseable ISO string."
  [form]
  (and (sequential? form) (= datetime-function (first form)) (some? (term-fields form))))

(defn calendar-term?
  "True iff `form` is a well-formed calendar term — `(YearFn 2000)`, `(MonthFn 2000 1)` or
  `(DayFn 2000 1 15)`."
  [form]
  (some? (calendar-fields form)))

(defn subinterval?
  "True iff time term `a` denotes an interval contained in `b`'s — `b`'s fields are a
  prefix of `a`'s and equal field-by-field (reflexive).  The interval reading of a
  reduced-precision calendar: fewer fields is a coarser, larger interval, and a finer
  interval sharing every coarser field sits inside it.  Returns `false` for anything that
  is not a pair of time terms, so a caller can hand it any two argument terms."
  [a b]
  (boolean
   (when-let [pa (term-fields a)]
     (when-let [pb (term-fields b)]
       (and (<= (count pb) (count pa))
            (= pb (subvec pa 0 (count pb))))))))

;; ---- the moments a calendar term lies between ----------------------------
;;
;; Everything above reads a calendar term as a *set of fields* and asks whether one set
;; nests inside another, which is all the context ordering needs.  Everything below reads
;; the same term as a **stretch between two moments**, which is what the point algebra
;; needs, and the two readings agree by construction: `b`'s fields are a prefix of `a`'s
;; exactly when `a`'s half-open bounds lie inside `b`'s.

(def instant-function
  "The structural constructor for a **moment**: `(InstantFn 2000 1 1 0 0 0)` is midnight
  at the start of 2000.  Six integer fields, always — year, month, day, hour, minute,
  second — so its arity is not its precision the way a calendar constructor's is, and
  every moment has exactly **one** spelling.  That is the whole reason it is not the
  reduced-precision `DatetimeFn` string: a term is identified by its shape, and
  `\"2000-01-01T00:00:00\"` and `\"2000-1-1T0:0:0\"` are two shapes for one moment where
  six integers are one.

  A `DatetimeFn` at full precision denotes the one-*second* interval, not the instant that
  opens it — the whole family names stretches — so the two constructors are kept apart:
  `YearFn` / `MonthFn` / `DayFn` / `DatetimeFn` are `temporal_thing`s, `InstantFn` is a
  `time_point`."
  'InstantFn)

(def ^:private instant-field-count 6)

(def ^:private field-defaults
  "What each field after the year is when a coarser term does not name it — the *first*
  moment of the stretch, so month and day are 1 and the clock fields 0."
  [1 1 0 0 0])

(defn- at
  "The `LocalDateTime` six fields name, or nil when the calendar has no such moment.

  This is the one place stricter than `field-ranges`, and deliberately: the range check
  bounds a day at 31 whatever the month, which is all the containment reading needs, while
  a *moment* has to exist before anything can be ordered against it.  So `(DayFn 2000 2
  30)` still nests inside February by fields and simply has no endpoints."
  ^LocalDateTime [[y mo d h mi s]]
  (try (LocalDateTime/of (int y) (int mo) (int d) (int h) (int mi) (int s))
       (catch DateTimeException _ nil)))

(defn- from
  "A `LocalDateTime` back as a six-field vector."
  [^LocalDateTime t]
  [(long (.getYear t)) (long (.getMonthValue t)) (long (.getDayOfMonth t))
   (long (.getHour t)) (long (.getMinute t)) (long (.getSecond t))])

(defn- one-later
  "The moment one unit of `n`-field precision after `t` — the next year, month, day, hour,
  minute or second — or nil when it falls outside `year-range`.

  `java.time` does the calendar, so February's length and the leap years are the
  platform's rather than a table here.  Leap seconds are not represented: a minute is
  sixty seconds, which is what a proleptic Gregorian calendar of six fields can say."
  [^LocalDateTime t n]
  (let [^LocalDateTime u (case (long n)
                           1 (.plusYears t 1)
                           2 (.plusMonths t 1)
                           3 (.plusDays t 1)
                           4 (.plusHours t 1)
                           5 (.plusMinutes t 1)
                           (.plusSeconds t 1))
        v (from u)]
    (when (<= (first year-range) (long (first v)) (second year-range)) v)))

(defn instant-fields
  "The six fields of an `(InstantFn Y M D h m s)` term, or nil for anything that is not
  one — a term of the wrong arity, a field out of range, or a date the calendar does not
  have.  **Total**, like every other reader here."
  [form]
  (when (sequential? form)
    (when (= instant-function (first form))
      (let [args (vec (rest form))]
        (when (and (= instant-field-count (count args))
                   (fields-in-range? args)
                   (some? (at args)))
          (mapv long args))))))

(defn instant-term
  "The `(InstantFn …)` term six fields name — a `PersistentList`, the shape
  `sentex/canon` normalizes a sentence's terms to, so a computed instant and one somebody
  typed are the same term."
  [fields]
  (apply list instant-function fields))

(defn instant-term?
  "True iff `form` is a well-formed `(InstantFn …)` term."
  [form]
  (some? (instant-fields form)))

(defn time-term?
  "True iff `form` is any term this namespace reads — a calendar constructor, a
  `DatetimeFn` string, or an `InstantFn` moment.

  What `provers/shadowing-channels` asks: a goal naming one of these can be decided from
  the term's own **structure**, which is a source no prover reading stored facts has, so
  no prover may answer such a goal alone."
  [form]
  (and (sequential? form)
       (boolean (or (some? (term-fields form)) (instant-term? form)))))

(defn bounds
  "The **half-open** `[start end]` a calendar term lies between, each a six-field vector,
  or nil for a term that is not a calendar one or names no moment.

  Half-open — `[start, end)` — and that is the convention the whole ordering rests on.
  The end of a term is the *first* moment of the next term at the same precision, so the
  end of 1999 and the start of 2000 are one field vector and so one term: an interval's
  two bounding instants can then be named without a smallest representable tick to sit
  just inside the closing end, and consecutive calendar terms **meet** rather than being
  separated by a gap whose width would depend on how finely the clock was read."
  [form]
  (when-let [fields (term-fields form)]
    (let [n     (count fields)
          start (into fields (subvec field-defaults (dec n)))]
      (when-let [^LocalDateTime t (at start)]
        (when-let [end (one-later t n)]
          [start end])))))

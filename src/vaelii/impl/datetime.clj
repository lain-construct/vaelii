;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.datetime
  "Reads the time terms — a `DatetimeFn` reduced-precision ISO string, the calendar
  constructors `YearFn` / `MonthFn` / `DayFn`, and the `InstantFn` moment — to integer
  field vectors.  Field nesting is calendar containment (`subinterval?`,
  docs/context-nat.md); `bounds` is the half-open `[start end)` the calendar clock reads
  (docs/time.md).  Every reader is pure and total, returning nil rather than throwing,
  because the structural genlCx producer calls it inside the settle/relabel loop."
  (:require [clojure.string :as str])
  (:import (java.time DateTimeException LocalDateTime)))

(def datetime-function
  "The structural ISO constructor this namespace reads."
  'DatetimeFn)

(def calendar-functions
  "The structural calendar constructors, `functor → field count`, one integer per field,
  coarsest first: `(YearFn 2000)`, `(MonthFn 2000 1)`, `(DayFn 2000 1 15)`."
  '{YearFn 1, MonthFn 2, DayFn 3})

(def ^:private field-ranges
  "The inclusive bounds of each field after the year, in field order: month, day, hour,
  minute, second.  Day is bounded at 31 whatever the month; `at` checks the calendar."
  [[1 12] [1 31] [0 23] [0 59] [0 59]])

(def ^:private year-pattern
  "A year is one to four digits, zero-padding optional.  The width refuses the basic ISO
  format, which would read `\"20260821\"` as the year 20,260,821, and keeps the read
  inside a `Long`."
  #"\d{1,4}")

(def ^:private field-pattern
  "Every field after the year is one or two digits, so `\"2000-1\"` and `\"2000-01\"` are
  one month, `\"2000-001\"` is nothing, and the read stays inside a `Long`."
  #"\d{1,2}")

(defn- parse
  "The ISO string as a vector of integer fields `[year month day hour minute second]`,
  truncated at the string's own precision, or nil when it is not well formed: one to three
  `-`-separated date fields, then optionally `T` and one to three `:`-separated time
  fields behind a full date, each field of its own width and in range.  Each half is
  bounded on its own, so `\"2000T13:00\"` and `\"2000-01-15-12\"` are refused."
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
  "The inclusive bounds of a numeric year: the range `year-pattern`'s width denotes, so a
  calendar constructor and an ISO string admit the same years."
  [0 9999])

(defn- fields-in-range?
  "Are numeric `fields` well formed — every one an integer, the year inside `year-range`
  and every later field inside its own?  Both numeric readers run this test."
  [fields]
  (and (every? integer? fields)
       (<= (first year-range) (long (first fields)) (second year-range))
       (every? (fn [[v [lo hi]]] (<= lo (long v) hi))
               (map vector (rest fields) field-ranges))))

(defn- calendar-fields
  "The fields of a calendar term `(YearFn Y)` / `(MonthFn Y M)` / `(DayFn Y M D)` of its
  functor's arity with every field in range, or nil."
  [form]
  (when (sequential? form)
    (when-let [n (get calendar-functions (first form))]
      (let [args (vec (rest form))]
        (when (and (= n (count args)) (fields-in-range? args))
          (mapv long args))))))

(defn- term-fields
  "The fields of a time term — a `(DatetimeFn \"<iso>\")` or one of the calendar
  constructors — or nil for anything that is neither.  Both spellings read to one field
  vector."
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
  "True iff time term `a` denotes an interval contained in `b`'s: `b`'s fields are a
  prefix of `a`'s (reflexive).  `false` for anything that is not a pair of time terms."
  [a b]
  (boolean
   (when-let [pa (term-fields a)]
     (when-let [pb (term-fields b)]
       (and (<= (count pb) (count pa))
            (= pb (subvec pa 0 (count pb))))))))

(def order-comparators
  "The registered pure comparators of an order, `{relation → (fn [a b] a-below-b?)}`.
  Each reads two terms' shape with no store read and no proof, and is total, returning
  `false` for terms it does not apply to.  `context-nat` reads one to order two context
  NATs, and the canonicalizer reads one to absorb a meet's argument (`res/meet-order`)."
  {'subintervalOf subinterval?})

;; ---- the moments a calendar term lies between ----------------------------

(def instant-function
  "The structural constructor for a moment, six integer fields always:
  `(InstantFn 2000 1 1 0 0 0)` is midnight at the start of 2000."
  'InstantFn)

(def ^:private instant-field-count 6)

(def ^:private field-defaults
  "Each field after the year at the first moment of a coarser term: month and day 1, the
  clock fields 0."
  [1 1 0 0 0])

(defn- at
  "The `LocalDateTime` six fields name, or nil when the calendar has no such moment."
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
  minute or second — or nil when it falls outside `year-range`.  `java.time` supplies
  month lengths and leap years."
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
  have."
  [form]
  (when (sequential? form)
    (when (= instant-function (first form))
      (let [args (vec (rest form))]
        (when (and (= instant-field-count (count args))
                   (fields-in-range? args)
                   (some? (at args)))
          (mapv long args))))))

(defn instant-term
  "The `(InstantFn …)` term six fields name, a `PersistentList` as `sentex/canon`
  normalizes a typed one to."
  [fields]
  (apply list instant-function fields))

(defn instant-term?
  "True iff `form` is a well-formed `(InstantFn …)` term."
  [form]
  (some? (instant-fields form)))

(defn time-term?
  "True iff `form` is any term this namespace reads — a calendar constructor, a
  `DatetimeFn` string, or an `InstantFn` moment.  The test behind
  `provers/shadowing-channels`' `:calendar`."
  [form]
  (and (sequential? form)
       (boolean (or (some? (term-fields form)) (instant-term? form)))))

(defn bounds
  "The half-open `[start end)` a calendar term lies between, each a six-field vector: the
  end is the first moment of the next term at the same precision.  Nil for a term that is
  not a calendar one or names no moment."
  [form]
  (when-let [fields (term-fields form)]
    (let [n     (count fields)
          start (into fields (subvec field-defaults (dec n)))]
      (when-let [^LocalDateTime t (at start)]
        (when-let [end (one-later t n)]
          [start end])))))

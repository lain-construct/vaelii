;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.datetime-test
  "ISO 8601 datetime containment — docs/context-nat.md.  A reduced-precision ISO string
  denotes an interval, and a finer instant is inside a coarser one it shares every field
  with.  Pure and total: `subinterval?` answers any two forms and declines non-datetimes."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.datetime :as dt]))

(defn- dtf [s] (list 'DatetimeFn s))

(deftest datetime-term-recognition
  (is (dt/datetime-term? (dtf "2000")))
  (is (dt/datetime-term? (dtf "2000-01-15T13:30:00")))
  (testing "not a datetime term"
    (is (not (dt/datetime-term? (dtf "not-a-date"))))
    (is (not (dt/datetime-term? '(QuantityFn 5 Meter))))
    (is (not (dt/datetime-term? (dtf "2000-13-xx"))))
    (is (not (dt/datetime-term? 'Foo)))))

(deftest containment-nests-by-field
  (testing "a finer interval is inside a coarser one it shares fields with"
    (is (dt/subinterval? (dtf "2000-01") (dtf "2000")))
    (is (dt/subinterval? (dtf "2000-01-15") (dtf "2000-01")))
    (is (dt/subinterval? (dtf "2000-01-15") (dtf "2000")))
    (is (dt/subinterval? (dtf "2000-01-15T13") (dtf "2000-01-15"))))
  (testing "reflexive"
    (is (dt/subinterval? (dtf "2000-01") (dtf "2000-01"))))
  (testing "field values are numeric, so zero-padding does not matter"
    (is (dt/subinterval? (dtf "2000-1") (dtf "2000-01")))
    (is (dt/subinterval? (dtf "2000-01") (dtf "2000-1")))))

(deftest non-containment
  (testing "a coarser interval is not inside a finer one"
    (is (not (dt/subinterval? (dtf "2000") (dtf "2000-01")))))
  (testing "different fields never nest"
    (is (not (dt/subinterval? (dtf "2001") (dtf "2000"))))
    (is (not (dt/subinterval? (dtf "2000-02") (dtf "2000-01"))))
    (is (not (dt/subinterval? (dtf "2000-01-16") (dtf "2000-01-15")))))
  (testing "non-datetime terms decline rather than throw"
    (is (not (dt/subinterval? (dtf "2000") '(QuantityFn 5 Meter))))
    (is (not (dt/subinterval? 'Foo (dtf "2000"))))))

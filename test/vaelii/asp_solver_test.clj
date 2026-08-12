;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.asp-solver-test
  "The backend facade's routing policy, pinned pure — what AUTO does at the size
  cutoff, and what it does when only one backend can run at all — plus the typed
  refusal a missing clasp binary earns.  No solve here needs libclingo or a real
  clasp: the policy fn takes its facts as arguments, and the refusal test points
  the binary var at a name nothing resolves."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.asp.clasp :as clasp]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.solve :as solve]))

(def ^:private choose #'solver/choose-backend)

(deftest auto-routes-on-size-and-degrades-on-availability
  (testing "small prefers in-process, large prefers the fork"
    (is (= :clingo (choose nil true 100 3000 true)))
    (is (= :clasp  (choose nil true 9000 3000 true))))
  (testing "past the cutoff clasp is preferred only when it can actually run"
    (is (= :clingo (choose nil true 9000 3000 false))
        "a loadable clingo on a large program is a cost regression; routing to a
        binary the machine does not have is a refusal available? promised away"))
  (testing "no clingo means clasp at any size"
    (is (= :clasp (choose nil false 100 3000 true)))
    (is (= :clasp (choose nil false 9000 3000 false))))
  (testing "explicit config is honored verbatim, clingo falling back when unloadable"
    (is (= :clasp  (choose :clasp true 100 3000 true)))
    (is (= :clingo (choose :clingo true 9000 3000 true)))
    (is (= :clasp  (choose :clingo false 100 3000 true)))))

(deftest a-missing-clasp-binary-is-a-typed-refusal
  ;; `shell/sh` execs directly — no shell, so no exit-127 convention — and the
  ;; IOException it throws comes back as the `:type` callers discriminate on
  (binding [clasp/*clasp-binary* "vaelii-no-such-binary"]
    (is (false? (clasp/available?)))
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (clasp/solve "asp 1 0 0\n0\n" :label)))]
      (is (= :solver-unavailable (:type (ex-data e)))))))

(deftest content-key-survives-an-ambient-print-length
  ;; the key decides which side of a tie gives way; under a REPL's *print-length*
  ;; two sentences sharing a prefix elided to one key, and the arbitration fell
  ;; back to arrival order — the exact dependence the key exists to remove
  (let [program {:content {1 {:sentence '(likes Ann Bo Cy Dee) :context 'C}
                           2 {:sentence '(likes Ann Bo Cy Eve) :context 'C}}}]
    (binding [*print-length* 2 *print-level* 1]
      (is (not= (solve/content-key program 1) (solve/content-key program 2))))))

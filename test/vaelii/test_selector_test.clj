;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.test-selector-test
  "`lein test-red`: `vaelii.ns-counts/install-verdicts!` prints one verdict per test, and
  `scripts/test-selector.sh :red` inverts them.

  The script runs from a copy in a scratch directory, with a `lein` on `PATH` that prints
  a canned run, so its log and ledger row land there and not in this checkout."
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as str]
            [clojure.test :as t :refer [deftest is testing]]
            [vaelii.ns-counts :as ns-counts]
            [vaelii.test-util :as tu])
  (:import [java.io ByteArrayOutputStream File PrintStream]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(defn- verdict-lines
  "The `TESTVERDICT` lines `install-verdicts!` prints for the report events `f` sends.
  `clojure.test/report` is a fresh multimethod for the call: under `lein test` the var
  holds leiningen's hook around the suite's own one."
  [f]
  (let [mf     (doto (clojure.lang.MultiFn. "report" :type :default #'clojure.core/global-hierarchy)
                 (.addMethod :default (fn [_])))
        buf    (ByteArrayOutputStream.)
        stdout System/out]
    (try (System/setOut (PrintStream. buf true))
         (with-redefs [t/report mf]
           (ns-counts/install-verdicts!)
           (binding [t/*report-counters* (ref t/*initial-report-counters*)]
             (f)))
         (finally (System/setOut stdout)))
    (filterv #(str/starts-with? % "TESTVERDICT") (str/split-lines (str buf)))))

(deftest a-test-var-fails-for-a-failure-reported-after-its-body-before-the-next-one
  (let [fails! #(dosync (commute t/*report-counters* update :fail (fnil inc 0)))]
    (is (= ["TESTVERDICT\tclojure.core/inc\tpass"
            "TESTVERDICT\tclojure.core/dec\tfail"
            "TESTVERDICT\tclojure.core/str\tfail"]
           (verdict-lines
            (fn []
              (t/report {:type :begin-test-var :var #'inc})
              (t/report {:type :end-test-var :var #'inc})
              (t/report {:type :begin-test-var :var #'dec})
              (t/report {:type :end-test-var :var #'dec})
              ;; an `:each` fixture's check, after the body's `:end-test-var`
              (fails!)
              (t/report {:type :begin-test-var :var #'str})
              (fails!)
              (t/report {:type :end-test-ns :ns *ns*})))))))

(defn- with-script
  "Call `f` with a scratch directory holding a copy of `scripts/test-selector.sh` and the
  libraries it sources, and a `lein` stub printing `<dir>/out` and exiting 1."
  [f]
  (tu/with-requirement @tu/host-bash? "the bash on PATH is WSL's, which sees neither this checkout nor the scratch directory"
    (let [dir (.toFile (Files/createTempDirectory "vaelii-test-red-" (into-array FileAttribute [])))]
      (try (doseq [p ["scripts/test-selector.sh" "scripts/lib/runlog.sh" "scripts/lib/revision.sh"]]
             (io/make-parents (io/file dir p))
             (io/copy (io/file p) (io/file dir p)))
           (io/make-parents (io/file dir "bin/lein"))
           (spit (io/file dir "bin/lein") "cat \"$STUB_OUT\"\nexit 1\n")
           (.setExecutable (io/file dir "bin/lein") true)
           (f dir)
           (finally (doseq [^File x (reverse (file-seq dir))] (.delete x)))))))

(defn- red-run
  "Exit and stdout of `test-selector.sh :red` over a `lein test` that prints `lines`."
  [^File dir lines]
  (spit (io/file dir "out") (str (str/join "\n" lines) "\n"))
  (let [env (into {} (System/getenv))
        env (assoc env
                   "PATH" (str (tu/posix-path (io/file dir "bin")) ":" (get env "PATH"))
                   "STUB_OUT" (tu/posix-path (io/file dir "out")))]
    (select-keys (shell/sh tu/bash "-c" (str "\"$BASH\" " (tu/posix-path (io/file dir "scripts/test-selector.sh")) " :red")
                           :dir dir :env env)
                 [:exit :out])))

(deftest a-red-test-run-fails-on-a-red-test-that-passes
  (with-script
    (fn [dir]
      (let [totals ["Ran 2 tests containing 3 assertions." "2 failures, 0 errors."]]
        (testing "every red test fails"
          (let [{:keys [exit out]} (red-run dir (into ["TESTVERDICT\ta.b-test/c\tfail"
                                                       "TESTVERDICT\ta.b-test/d\tfail"] totals))]
            (is (= 0 exit))
            (is (str/includes? out "all 2 red test(s) fail"))
            (is (not (str/includes? out "TESTVERDICT")) "the verdict lines stay off the terminal")))
        (testing "one red test passes"
          (let [{:keys [exit out]} (red-run dir (into ["TESTVERDICT\ta.b-test/c\tpass"
                                                       "TESTVERDICT\ta.b-test/d\tfail"] totals))]
            (is (= 1 exit))
            (is (str/includes? out "  lein test :only a.b-test/c\n"))
            (is (not (str/includes? out "a.b-test/d")))))
        (testing "a test without a verdict, and a run without totals"
          (is (= 2 (:exit (red-run dir (into ["TESTVERDICT\ta.b-test/c\tfail"] totals)))))
          (is (= 2 (:exit (red-run dir ["TESTVERDICT\ta.b-test/c\tfail"])))))))))

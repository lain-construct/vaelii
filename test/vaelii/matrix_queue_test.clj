;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.matrix-queue-test
  "The matrix's shared state in `scripts/lib/slots.sh`, and the refusal
  `scripts/test-matrix.sh` gives during the cooldown after a red run.

  Each test runs the shell in a scratch git repository of its own, so the lock, the
  queue and the `red` file it writes land in that repository's `.git/vaelii-matrix`
  and never in this checkout's, where a live matrix reads them."
  (:require [clojure.java.io :as io]
            [clojure.java.shell :as shell]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]])
  (:import [java.io File]
           [java.nio.file Files StandardCopyOption]
           [java.nio.file.attribute FileAttribute]))

(def ^:private checkout (.getCanonicalPath (io/file ".")))

(def ^:private env
  "This JVM's environment less the variables the scripts read, so a caller's session
  id, cooldown or git directory cannot reach the scratch repository."
  (apply dissoc (into {} (System/getenv))
         "EDIT_SESSION" "MATRIX_RED_COOLDOWN" "MATRIX_REQUESTED_BY" "MATRIX_OWED_MAX"
         "TEST_MATRIX_OUT" "GIT_DIR" "GIT_WORK_TREE" "GIT_INDEX_FILE"))

(defn- run [^File dir extra & args]
  (apply shell/sh (concat args [:dir dir :env (merge env extra)])))

(defn- git! [^File dir & args]
  (let [{:keys [exit err out]} (apply run dir {} "git" "-c" "user.name=t" "-c" "user.email=t@t"
                                      "-c" "commit.gpgsign=false" args)]
    (assert (zero? exit) err)
    (str/trim out)))

(defn- with-repo
  "Call `f` with a scratch repository holding two commits, and delete it after."
  [f]
  (let [dir (.toFile (Files/createTempDirectory "vaelii-matrix-" (into-array FileAttribute [])))]
    (try (git! dir "init" "-q")
         (git! dir "commit" "-q" "--allow-empty" "-m" "one")
         (git! dir "commit" "-q" "--allow-empty" "-m" "two")
         (f dir)
         (finally (doseq [^File x (reverse (file-seq dir))] (.delete x))))))

(defn- slots
  "Run `body` in `dir` with `scripts/lib/slots.sh` sourced; its trimmed stdout."
  ([dir body] (slots dir {} body))
  ([dir extra body]
   (let [{:keys [exit out err]} (run dir extra "bash" "-c"
                                     (str ". " checkout "/scripts/lib/slots.sh && " body))]
     (assert (zero? exit) err)
     (str/trim out))))

(deftest a-queue-take-merges-the-requests-and-empties-the-queue
  (with-repo
    (fn [dir]
      (let [one (git! dir "rev-parse" "HEAD~1")
            two (git! dir "rev-parse" "HEAD")]
        (testing "the commit every baseline descends from, the selector, the requesters joined"
          ;; a line queued before requesters were recorded has two fields, and adds none
          (slots dir (str "printf '%s :default\\n' " two " >>\"$(matrix_state_dir)/queue\""))
          (slots dir (str "matrix_queue_add " two " :default user:b"))
          (slots dir (str "matrix_queue_add " one " :default session:a"))
          (is (= (str one " :default session:a,user:b") (slots dir "matrix_queue_take"))))
        (testing "a take empties the queue"
          (is (= "" (slots dir "matrix_queue_take"))))
        (testing "requests under different selectors run at :all"
          (slots dir (str "matrix_queue_add " two " :default user:b"))
          (slots dir (str "matrix_queue_add " two " :slow user:b"))
          (is (= (str two " :all user:b") (slots dir "matrix_queue_take"))))))))

(deftest the-requester-is-the-session-else-the-login
  (with-repo
    (fn [dir]
      (is (= "session:s1" (slots dir {"EDIT_SESSION" "s1"} "matrix_requester")))
      (is (= "user:someone" (slots dir {"USER" "someone"} "matrix_requester"))))))

(deftest the-cooldown-holds-from-a-red-until-it-expires-or-a-green
  (with-repo
    (fn [dir]
      (let [red (fn [age] (slots dir (str "printf '%s /r\\n' $(( $(date +%s) - " age " ))"
                                          " >|\"$(matrix_state_dir)/red\"")))]
        (slots dir "matrix_red_mark /r")
        (is (str/ends-with? (slots dir "matrix_red_recent") " /r") "a red just marked holds")
        (is (= "" (slots dir {"MATRIX_RED_COOLDOWN" "0"} "matrix_red_recent"))
            "a cooldown of 0 turns it off")
        (red 1801)
        (is (= "" (slots dir "matrix_red_recent")) "past the default 1800 seconds it lapses")
        (is (not= "" (slots dir {"MATRIX_RED_COOLDOWN" "3600"} "matrix_red_recent"))
            "a longer cooldown still holds it")
        (red 0)
        (slots dir "matrix_red_clear")
        (is (= "" (slots dir "matrix_red_recent")) "a green clears it")))))

(defn- copy-scripts! [^File dir]
  (doseq [rel (cons "scripts/test-matrix.sh"
                    (for [^File f (.listFiles (io/file checkout "scripts/lib"))]
                      (str "scripts/lib/" (.getName f))))]
    (let [to (io/file dir rel)]
      (io/make-parents to)
      (Files/copy (.toPath (io/file checkout rel)) (.toPath to)
                  ^"[Ljava.nio.file.CopyOption;" (into-array [StandardCopyOption/REPLACE_EXISTING])))))

(deftest a-matrix-in-the-cooldown-refuses-and-names-the-red-run
  (with-repo
    (fn [^File dir]
      (copy-scripts! dir)
      (let [run-dir (io/file dir "logs/test-matrix/run-1")
            t       "vaelii.some-test/a-failing-test"]
        (.mkdirs run-dir)
        (spit (io/file run-dir "summary.tsv")
              (str "config\tkind\trevision\tstate\tseconds\tsummary\tcounts\n"
                   "rete\tsweep\tabc12345\tfailed\t60\t\t\n"
                   "disk-snapshot\tbackend\tabc12345\tfailed\t60\t\t\n"
                   "overlay\tbackend\tabc12345\tfailed\t60\t\t\n"))
        (spit (io/file run-dir "failures.tsv") (str t "\tdisk-snapshot\n" t "\trete\n"))
        (spit (io/file run-dir "requested-by") "session:s1\n")
        (spit (io/file run-dir "queue-dropped") "0123456789ab :default session:s2,user:u\n")
        (slots dir (str "matrix_red_mark " (.getPath run-dir)))
        (let [{:keys [exit out]} (run dir {} "bash" "scripts/test-matrix.sh" "--no-tty" "memory")]
          (is (= 75 exit) "the refusal is exit 75, the not-started status")
          (testing "the notice names the red run and whose it was"
            (is (str/includes? out (.getPath run-dir)))
            (is (str/includes? out "revision:   abc12345"))
            (is (str/includes? out "in charge:  session:s1")))
          (testing "the requests the red run dropped are named"
            (is (str/includes? out "session:s2, user:u (--owed=01234567 :default), not run")))
          (testing "each failing test with its configurations and a one-configuration re-run"
            (is (str/includes? out (str t " — disk-snapshot rete")))
            (is (str/includes? out (str "env VAELII_TEST_BACKEND=disk-snapshot lein test :only " t))))
          (testing "a configuration that failed without naming a test points at its log"
            (is (str/includes? out "overlay — no failing test named")))
          (is (not (.exists (io/file dir ".git/vaelii-matrix/lock"))) "no lock was taken"))))))

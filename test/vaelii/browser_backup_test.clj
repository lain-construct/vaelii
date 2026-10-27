;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.browser-backup-test
  "The backup of a `:pg-snapshot` store: its names and its command, the refusals, the
  card's button, and — when a Postgres server and `pg_dump` answer — a backup taken,
  restored by the steps `backup.edn` gives, and opened again."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.browser.backup :as backup]
            [vaelii.browser.catalog :as catalog]
            [vaelii.browser.web]
            [vaelii.core :as v])
  (:import [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]
           [java.time LocalDateTime]))

(deftest a-backup-goes-beside-its-store-named-for-the-time
  (is (= "/kb/legacy-pg-backup-20261020-163005"
         (backup/backup-dir "/kb/legacy-pg/" (LocalDateTime/of 2026 10 20 16 30 5)))))

(deftest the-dump-is-one-schema-in-the-custom-format
  (let [argv (backup/pg-dump-command {:host "localhost" :port 5432 :db "vaelii" :schema "legacy_x"}
                                     "/b/records.dump")]
    (is (= "legacy_x" (second (drop-while #(not= "--schema" %) argv))))
    (is (some #{"--format=custom"} argv))
    (is (= "/b/records.dump" (last argv)))))

(deftest a-store-directory-names-its-schema
  (let [dir (str (Files/createTempDirectory "vaelii-backup" (make-array FileAttribute 0)))]
    (is (nil? (backup/store-records dir)) "no records.edn, no schema")
    (io/make-parents (io/file dir "index" "records.edn"))
    (spit (io/file dir "index" "records.edn") (pr-str {:records ["localhost" 5432 "vaelii" "s_1"]}))
    (is (= {:host "localhost" :port 5432 :db "vaelii" :schema "s_1"} (backup/store-records dir)))))

(defn- rm-rf! [f]
  (let [f (io/file f)]
    (when (.isDirectory f) (run! rm-rf! (.listFiles f)))
    (.delete f)))

(deftest only-a-loaded-entry-is-backed-up
  (is (= :unknown-entry (:type (ex-data (backup/refusal "no-such-entry"))))))

(defn- refusal-for
  "The `:type` `refusal` answers for an in-process, loaded entry at `where`."
  [where]
  (with-redefs [catalog/entry          (fn [_] {:name "n" :kb ::kb :where where})
                catalog/in-process?    (constantly true)
                catalog/write-blocked? (constantly false)]
    (:type (ex-data (backup/refusal "k")))))

(deftest only-a-store-kept-in-postgres-is-backed-up
  (is (= :not-pg-snapshot (refusal-for {:backend :disk-snapshot :dir "/kb/x"})))
  (is (= :not-pg-snapshot (refusal-for {})) "a memory KB has no store at all"))

(deftest a-store-naming-no-schema-is-refused
  (let [dir (str (Files/createTempDirectory "vaelii-backup" (make-array FileAttribute 0)))]
    (is (= :no-records-location (refusal-for {:backend :pg-snapshot :dir dir})))))

(defn- failed-backup
  "Run `backup!` into a fresh `out` with `v/seal` answering `seal`, from the store
  directory `dir`; answer the refusal's `:type` and whether `out` was left behind."
  [seal dir]
  (let [root (str (Files/createTempDirectory "vaelii-backup" (make-array FileAttribute 0)))
        out  (str root "/store-backup")
        kb   (v/open-kb {:backend :memory})]
    (try
      (with-redefs [v/seal (fn [_] seal)]
        {:type (try (backup/backup! kb dir out (fn [_])) nil
                    (catch clojure.lang.ExceptionInfo e (:type (ex-data e))))
         :left? (.exists (io/file out))})
      (finally (v/close! kb) (rm-rf! root)))))

(deftest a-kb-that-does-not-seal-is-not-backed-up
  (is (= {:type :not-sealed :left? false}
         (failed-backup {:sealed false :reason :busy} "/nonexistent/store"))))

(deftest a-failed-backup-leaves-nothing-behind
  ;; the clone of a directory that does not exist fails, after `out` was made
  (is (= {:type :backup-failed :left? false}
         (failed-backup {:sealed true :generation 1 :watermark 0} "/nonexistent/store"))))

(defn- backup-into
  "Run `backup!` of store directory `dir` into `out`, with `v/seal` answering `seal` and
  `pg_dump` writing `dump` as its file; answer the directory written or the refusal's
  `:type`."
  [kb dir out seal dump]
  (let [cp @#'backup/run-process!]
    (with-redefs [v/seal                (fn [_] seal)
                  backup/run-process!   (fn [argv tick]
                                          (if (= "pg_dump" (first argv))
                                            (spit (last argv) dump)
                                            (cp argv tick)))]
      (try (:dir (backup/backup! kb dir out (fn [_])))
           (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))))

(deftest backups-in-one-second-write-distinct-directories-and-a-failure-deletes-only-its-own
  (let [root   (str (Files/createTempDirectory "vaelii-backup" (make-array FileAttribute 0)))
        store  (str root "/store")
        out    (backup/backup-dir store (LocalDateTime/of 2026 10 20 16 30 5))
        sealed {:sealed true :generation 1 :watermark 0}
        kb     (v/open-kb {:backend :memory})]
    (.mkdirs (io/file store))
    (spit (io/file store "x") "x")
    (try
      (let [a (backup-into kb store out sealed "dump a")]
        (is (= out a))
        (is (= :not-sealed (backup-into kb store out {:sealed false :reason :busy} "-")))
        (is (= :backup-failed (backup-into kb "/nonexistent/store" out sealed "-")))
        (let [b (backup-into kb store out sealed "dump b")]
          (is (= (str out "-2") b) "the failed backup deleted the -2 it created")
          (is (= "dump a" (slurp (io/file a "records.dump"))) "the first backup is intact")
          (is (= ["x"] (vec (.list (io/file a "store")))) "and its clone holds no second one")
          (is (= "dump b" (slurp (io/file b "records.dump"))))))
      (finally (v/close! kb) (rm-rf! root)))))

(deftest a-failed-backup-deletes-a-link-in-its-clone-and-not-what-it-names
  ;; the store copy keeps a link as a link; the dump fails after the copy
  (let [root  (str (Files/createTempDirectory "vaelii-backup" (make-array FileAttribute 0)))
        store (str root "/store")
        named (io/file root "named")
        out   (str root "/store-backup")
        kb    (v/open-kb {:backend :memory})]
    (.mkdirs (io/file store))
    (.mkdirs named)
    (spit (io/file named "kept") "kept")
    (Files/createSymbolicLink (.toPath (io/file store "link")) (.toPath named) (make-array FileAttribute 0))
    (try
      (with-redefs [v/seal              (fn [_] {:sealed true :generation 1 :watermark 0})
                    backup/run-process! (let [cp @#'backup/run-process!]
                                          (fn [argv tick]
                                            (if (= "pg_dump" (first argv))
                                              (throw (ex-info "pg_dump failed" {:type :backup-failed}))
                                              (cp argv tick))))]
        (is (= :backup-failed (try (backup/backup! kb store out (fn [_])) nil
                                   (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))))
      (is (not (.exists (io/file out))))
      (is (= "kept" (slurp (io/file named "kept"))))
      (finally (v/close! kb) (rm-rf! root)))))

(deftest the-progress-names-the-directory-the-backup-writes
  (let [root  (str (Files/createTempDirectory "vaelii-backup" (make-array FileAttribute 0)))
        store (str root "/store")
        out   (str root "/store-backup")
        notes (volatile! [])
        kb    (v/open-kb {:backend :memory})]
    (.mkdirs (io/file store))
    (.mkdirs (io/file out))
    (try
      (with-redefs [v/seal               (fn [_] {:sealed true :generation 1 :watermark 0})
                    backup/run-process!  (let [cp @#'backup/run-process!]
                                           (fn [argv tick]
                                             (if (= "pg_dump" (first argv)) (spit (last argv) "-") (cp argv tick))))]
        (is (= (str out "-2") (:dir (backup/backup! kb store out #(vswap! notes conj (:note %)))))))
      (is (some #(str/includes? (str %) (str out "-2")) @notes))
      (finally (v/close! kb) (rm-rf! root)))))

;; ---- end to end, against a server ----------------------------------------

(defn- sh
  "Run `argv`; answer its exit code and output."
  [& argv]
  (let [p   (-> (ProcessBuilder. ^java.util.List (vec argv)) (.redirectErrorStream true) (.start))
        out (slurp (.getInputStream p))]
    {:exit (.waitFor p) :out out}))

(defn- psql [sql]
  (sh "psql" "-h" "localhost" "-d" "vaelii" "-v" "ON_ERROR_STOP=1" "-Atc" sql))

(def ^:private server?
  ;; the suite must not need a server: without one, or without the adapter on the
  ;; classpath, the end-to-end test asserts nothing
  (delay (and (some? (try (requiring-resolve 'vaelii.postgres.record-store/pg-record-store)
                          (catch Exception _ nil)))
              (try (zero? (:exit (psql "SELECT 1"))) (catch Exception _ false))
              (try (zero? (:exit (sh "pg_dump" "--version"))) (catch Exception _ false)))))

(deftest a-backup-restores-to-the-state-it-was-taken-in
  (when @server?
    (let [schema "vaelii_browser_backup_e2e"
          root   (str (Files/createTempDirectory "vaelii-backup" (make-array FileAttribute 0)))
          dir    (str root "/store")
          out    (str root "/store-backup")
          opts   {:backend :pg-snapshot :dir dir :oplog? true
                  :pg {:jdbcUrl (str "jdbc:postgresql://localhost:5432/vaelii?user="
                                     (System/getProperty "user.name"))
                       :schema schema}}]
      (psql (str "DROP SCHEMA IF EXISTS " schema " CASCADE; DROP SCHEMA IF EXISTS "
                 schema "_replaced CASCADE"))
      (try
        (let [kb   (v/open-kb opts)
              _    (v/assert kb '(likes Ann Bob) 'CxBackupTest)
              info (backup/backup! kb dir out (fn [_]))]
          (testing "the backup holds the directory, the dump and how to restore"
            (is (.exists (io/file out "store" "index" "records.edn")))
            (is (not (.exists (io/file out "store" ".vaelii.lock"))) "the lock is left out")
            (is (pos? (:dump-bytes info)))
            (is (= 5 (count (:restore (read-string (slurp (io/file out "backup.edn"))))))))
          (v/assert kb '(likes Cy Dee) 'CxBackupTest)
          (v/close! kb))
        (testing "restored by backup.edn's steps, the KB is as it was at the backup"
          (is (zero? (:exit (psql (str "ALTER SCHEMA " schema " RENAME TO " schema "_replaced")))))
          (let [r (sh "pg_restore" "-h" "localhost" "-d" "vaelii" (str out "/records.dump"))]
            (is (zero? (:exit r)) (:out r)))
          (rm-rf! dir)
          (is (zero? (:exit (sh "cp" @#'backup/copy-flags (str out "/store") dir))))
          (let [kb (v/open-kb opts)]
            (try
              (is (seq (v/sentexes-matching kb '(likes Ann Bob) 'CxBackupTest))
                  "what was there at the backup is back")
              (is (empty? (v/sentexes-matching kb '(likes Cy Dee) 'CxBackupTest))
                  "and what was written after it is not")
              (finally (v/close! kb)))))
        (finally
          (psql (str "DROP SCHEMA IF EXISTS " schema " CASCADE; DROP SCHEMA IF EXISTS "
                     schema "_replaced CASCADE"))
          (rm-rf! root))))))

(deftest the-card-offers-a-backup-only-for-a-postgres-store
  (let [card @#'vaelii.browser.web/entry-card
        html (fn [e] (str (card (merge {:key "k" :name "n" :status :done :kb? true} e) false)))]
    (is (str/includes? (html {:where {:backend :pg-snapshot :dir "/kb/x"}}) "/kbs/backup"))
    (is (str/includes? (html {:where {:backend :pg-snapshot :dir "/kb/x"}}) "hx-confirm"))
    (is (not (str/includes? (html {:where {:backend :disk-snapshot :dir "/kb/x"}}) "/kbs/backup")))
    (is (not (str/includes? (html {}) "/kbs/backup")))))

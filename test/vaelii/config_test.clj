;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.config-test
  "The build's switches (`vaelii.impl.config`), held to the rule the options maps
  already keep: a switch that is read has a domain, and a value outside it is refused.

  Every test here asserts the **refusal**, not the behaviour it would have selected:
  `-Dvaelii.disk.auto-compact=disabled` throws, and what it must not do is compact.
  The other half — every documented spelling still reads, and no property set at all is
  the documented default — is what catches a domain drawn too tight, which would refuse
  a working operator's setup rather than a typo.

  Three switches read the *environment* (`VAELII_ARBITRATE_CONSTRAINTS`,
  `VAELII_ASSERTIVE_ARG_TYPES`, `VAELII_DEV`) and a JVM cannot set its own, so they are
  covered where the coverage is honest: through `prop-bool`, which is the whole of each
  accessor's body."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.config :as config]
            [vaelii.impl.disk.files :as f]))

(def ^:private switched
  "Every property `config/check!` reads, so a test can clear the lot and see the
  defaults — a run with nothing set must be indistinguishable from one with the
  properties absent."
  ["vaelii.disk.auto-compact" "vaelii.disk.fsync" "vaelii.disk.compress"
   "vaelii.disk.tokens" "vaelii.disk.cache" "vaelii.disk.sync-ms"
   "vaelii.disk.compact-dead-ratio" "vaelii.disk.compact-min-interval-ms"
   "vaelii.disk.lock" "vaelii.index.snapshot"])

(defn- with-properties*
  "Run `f` with each `[name value]` set (nil clears), restoring every one afterwards —
  including the ones the JVM was started with, since a `test-backends.sh` run sets some
  of these on the command line."
  [pairs f]
  (let [prev (mapv (fn [[nm _]] [nm (System/getProperty nm)]) pairs)]
    (doseq [[nm v] pairs]
      (if v (System/setProperty nm v) (System/clearProperty nm)))
    (try (f)
         (finally
           (doseq [[nm v] prev]
             (if v (System/setProperty nm v) (System/clearProperty nm)))))))

(defmacro ^:private with-property [nm value & body]
  `(with-properties* [[~nm ~value]] (fn [] ~@body)))

(defmacro ^:private with-nothing-set [& body]
  `(with-properties* (mapv (fn [nm#] [nm# nil]) switched) (fn [] ~@body)))

;; ---- one row per switch: the wrong value is an error, not the other branch ----

(def ^:private wrong-values
  "A plausible wrong value per switch, and what each one did when the read was a
  membership test: the comment is the reason the row exists."
  [;; negated membership — `=disabled` was compaction ON
   ["vaelii.disk.auto-compact" "disabled"]
   ["vaelii.disk.auto-compact" "never"]
   ;; membership in three spellings of one word — `=always` was the 3-second tick, which
   ;; is the durability level the operator was trying to leave
   ["vaelii.disk.fsync" "always"]
   ["vaelii.disk.fsync" "sync"]
   ["vaelii.disk.fsync" "true"]
   ;; a `case` whose default arm was nil — every misspelling was no compression at all
   ["vaelii.disk.compress" "gzip"]
   ["vaelii.disk.compress" "zstdd"]
   ;; `(= "true" …)` — everything else was off
   ["vaelii.disk.tokens" "enabled"]
   ["vaelii.index.snapshot" "enabled"]
   ;; `Long/parseLong` with no catch, in a top-level `def`
   ["vaelii.disk.cache" "64k"]
   ["vaelii.disk.cache" "-1"]
   ["vaelii.disk.sync-ms" "3s"]
   ["vaelii.disk.compact-min-interval-ms" "5m"]
   ;; a ratio outside 0–1 is a threshold that never fires or fires on every tick
   ["vaelii.disk.compact-dead-ratio" "half"]
   ["vaelii.disk.compact-dead-ratio" "2"]
   ;; `(= "false" …)` — the one that failed safe, and still says so
   ["vaelii.disk.lock" "no-thanks"]])

(deftest every-switch-refuses-the-value-nothing-reads
  (doseq [[nm value] wrong-values]
    (testing (str nm "=" value)
      (with-property nm value
        (let [e (is (thrown? clojure.lang.ExceptionInfo (config/check!))
                    (str nm "=" value " is refused"))
              d (ex-data e)]
          (is (= :unknown-option (:type d)))
          (is (= nm (:property d)) "the refusal names the switch")
          (is (= value (:value d)) "and the value it was given")
          (is (re-find (re-pattern (str nm "=" value)) (ex-message e))
              "the message names both, since a log line is all an operator has"))))))

(deftest a-switch-nothing-reads-fails-the-open
  (testing "the refusal lands at open-kb — the earliest door, before a record moves"
    (with-property "vaelii.disk.fsync" "always"
      (let [e (is (thrown? clojure.lang.ExceptionInfo
                           (v/open-kb {:record-space 88 :index-space 89 :recover? false})))]
        (is (= :unknown-option (:type (ex-data e))))
        (is (re-find #"dsync" (ex-message e)) "and names the mode there is")))
    (testing "on a RAM KB as much as a durable one: the process is one directory away"
      (with-property "vaelii.disk.compress" "gzip"
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/open-kb {:backend :memory :record-space 88 :index-space 89
                                 :recover? false}))))))
  (testing "and a KB whose switches are all legal still opens"
    (with-property "vaelii.disk.fsync" "dsync"
      (let [kb (v/open-kb {:record-space 88 :index-space 89 :recover? false})]
        (is (some? kb))
        (v/clear! kb)))))

;; ---- the other half: every documented spelling still reads ---------------

(deftest every-documented-spelling-still-reads
  (testing "one boolean vocabulary, whichever switch"
    (doseq [on ["true" "1" "on" "yes" "TRUE" "On"]]
      (with-property "vaelii.disk.tokens" on
        (is (true? (config/disk-tokens?)) on)))
    (doseq [off ["false" "0" "off" "no" "FALSE" "Off"]]
      (with-property "vaelii.disk.auto-compact" off
        (is (false? (config/disk-auto-compact?)) off))))
  (testing "the fsync mode, in the three spellings the write path already accepted"
    (doseq [s ["dsync" "DSYNC" "Dsync"]]
      (with-property "vaelii.disk.fsync" s
        (is (= :dsync (config/disk-fsync-mode)) s))))
  (testing "the compressors, and the three ways to ask for none"
    (with-property "vaelii.disk.compress" "zstd" (is (= :zstd (config/disk-compress))))
    (with-property "vaelii.disk.compress" "lz4"  (is (= :lz4  (config/disk-compress))))
    (doseq [none ["none" "off" "false"]]
      (with-property "vaelii.disk.compress" none
        (is (nil? (config/disk-compress)) none))))
  (testing "the counts, including the bounds themselves"
    (with-property "vaelii.disk.cache" "0"    (is (= 0 (config/disk-cache-capacity))))
    (with-property "vaelii.disk.cache" "1000" (is (= 1000 (config/disk-cache-capacity))))
    (with-property "vaelii.disk.sync-ms" "0"  (is (= 0 (config/disk-sync-ms))))
    (with-property "vaelii.disk.compact-min-interval-ms" "60000"
      (is (= 60000 (config/disk-compact-min-interval-ms))))
    (doseq [r ["0" "0.25" "1"]]
      (with-property "vaelii.disk.compact-dead-ratio" r
        (is (= (Double/parseDouble r) (config/disk-compact-dead-ratio)) r))))
  (testing "a blank value is unset, not a spelling: an exported-but-empty variable"
    (with-property "vaelii.disk.fsync" ""
      (is (= :tick (config/disk-fsync-mode))))))

(deftest nothing-set-is-the-documented-default
  (with-nothing-set
    (is (nil? (config/check!)) "a run with no switch set passes the door")
    (is (true?  (config/disk-auto-compact?)))
    (is (= :tick (config/disk-fsync-mode)))
    (is (nil?   (config/disk-compress)))
    (is (false? (config/disk-tokens?)))
    (is (= 65536 (config/disk-cache-capacity)))
    (is (= 3000  (config/disk-sync-ms)))
    (is (= 0.5   (config/disk-compact-dead-ratio)))
    (is (= 300000 (config/disk-compact-min-interval-ms)))
    (is (true?  (config/disk-lock?)))
    (is (false? (config/index-snapshot?)))))

(deftest the-environment-switches-read-the-one-vocabulary
  ;; `prop-bool` is the whole body of `arbitrate-constraints?`, `assertive-arg-types?`
  ;; and `web-dev?`; a JVM cannot set its own environment, so the reader is exercised
  ;; under a property name and the accessors are one line over it.
  (with-property "vaelii.test.bool" "1"
    (is (true? (config/prop-bool "vaelii.test.bool" false))
        "=1 is on — read as `(= \"1\" …)` it was off for VAELII_DEV's neighbours"))
  (with-property "vaelii.test.bool" "0"
    (is (false? (config/prop-bool "vaelii.test.bool" true))
        "=0 is off — read as mere presence it was on"))
  (with-property "vaelii.test.bool" "maybe"
    (is (thrown? clojure.lang.ExceptionInfo (config/prop-bool "vaelii.test.bool" false))))
  (with-property "vaelii.test.bool" nil
    (is (false? (config/prop-bool "vaelii.test.bool" false)) "unset is the default")
    (is (true? (config/prop-bool "vaelii.test.bool" true)))))

;; ---- the write path the fsync switch decides ----------------------------

(deftest the-dsync-reader-still-drives-the-write-path
  (testing "the log mode is decided by the same three spellings as before"
    (doseq [s ["dsync" "DSYNC" "Dsync"]]
      (with-property "vaelii.disk.fsync" s
        (is (true? (#'f/dsync?)) s)))
    (with-property "vaelii.disk.fsync" nil
      (is (false? (#'f/dsync?)) "unset is the tick, not the append"))
    (with-property "vaelii.disk.fsync" "always"
      (is (thrown? clojure.lang.ExceptionInfo (#'f/dsync?)))))
  (testing "and a record written under dsync reads back"
    (with-property "vaelii.disk.fsync" "dsync"
      (let [path (str (System/getProperty "java.io.tmpdir") "/vaelii-config-test-"
                      (System/nanoTime) ".log")
            raf  (f/open-log path)]
        (try
          (let [off (f/append-record! raf {:hello 'world})]
            (is (= {:hello 'world} (f/read-record raf off))))
          (finally (f/close! raf) (.delete (java.io.File. path))))))))

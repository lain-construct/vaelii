;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.belief-snapshot-test
  "The belief certificate (`vaelii.impl.disk.belief-snapshot`): a full recover of a *clean*
  disk KB leaves a `meta.edn` stamped against its records, and the next cold open reads
  that stamp, skips the closing settle's definitional-clash scan, and rederives identical
  belief.  An *unclean* KB — one whose scan defeated a member — is stamped so the open
  ignores it, and records that moved since the stamp fail its fingerprint.  All of it is
  behind `vaelii.belief.snapshot`, off by default; the fixture turns it on."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.disk.belief-snapshot :as bs]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p])
  (:import [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(def ^:private prop "vaelii.belief.snapshot")

(use-fixtures :each
  (fn [t]
    (let [prev (System/getProperty prop)]
      (System/setProperty prop "true")
      (try (t)
           (finally (if prev
                      (System/setProperty prop prev)
                      (System/clearProperty prop)))))))

(defn- tmpdir ^String []
  (str (Files/createTempDirectory "vaelii-belief-" (into-array FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (java.io.File. dir)))] (.delete ^java.io.File f)))

(defn- out-sentences
  "Belief's sparse complement: the sentences of the disbelieved sentexes, as a set."
  [kb]
  (let [tms (:tms kb) recs (:records kb)]
    (into #{} (comp (remove #(jtms/in? tms %))
                    (keep #(some-> (p/get-sentex recs %) :sentence)))
          (p/sentex-ids recs))))

(defn- clash-pair-count [kb]
  (count (:pairs (some-> (:clashes kb) deref))))

(defn- with-kb
  "Open a fresh disk KB over `dir` (unrecovered), pass it to `f`, and close it."
  [dir f]
  (let [kb (v/open-kb {:backend :disk :dir dir :recover? false})]
    (try (f kb) (finally (v/close! kb)))))

(deftest a-clean-dilemma-kb-writes-a-certificate-and-a-reopen-takes-the-fast-path
  ;; A definitional clash whose two members are equal-strength (both default): settle
  ;; reports it as a dilemma and disbelieves neither, so the KB is clean.  Memberships
  ;; first and `disjoint` last is the arrival order the live check admits (a later
  ;; declaration against defeasible content is arbitrated, not refused).
  (let [dir (tmpdir)]
    (try
      (with-kb dir
        (fn [kb]
          (v/assert kb '(dog Rex) 'CxUniverse {:strength :default})
          (v/assert kb '(cat Rex) 'CxUniverse {:strength :default})
          (v/assert kb '(disjoint dog cat) 'CxUniverse {:strength :default})
          (v/recover kb)
          (is (empty? (out-sentences kb)) "the dilemma disbelieves neither side")
          (is (= 1 (clash-pair-count kb)) "the full recover found the clash")))
      (testing "the certificate is written, clean, and stamped"
        (is (.exists (io/file dir "belief" "meta.edn")))
        (with-kb dir
          (fn [kb]
            (let [m (bs/read-meta (:records kb))]
              (is (true? (:clean? m)))
              (is (= 0 (:out-count m)))
              (is (= 1 (:clash-count m)))
              (is (= 0 (:clash-losers m)))
              (is (some? (:fingerprint m)))))))
      (testing "a cold reopen trusts the stamp, skips the scan, and reaches the same belief"
        (with-kb dir
          (fn [kb]
            (is (true? (bs/usable? (:records kb))) "the stamp matches the records")
            (v/recover kb)
            (is (empty? (out-sentences kb)) "belief is identical")
            (is (zero? (clash-pair-count kb))
                "the clash scan was skipped — the fast path derives no clash records"))))
      (finally (rm-rf! dir)))))

(deftest an-unclean-kb-with-a-clash-loser-is-not-trusted-and-recovers-in-full
  ;; The same clash, but strength-differentiated: `(dog Rex)` monotonic and the disjointness
  ;; monotonic defeat the defeasible `(cat Rex)`, which the scan takes OUT.  A loser whose
  ;; defeat cascades cannot be reproduced by a post-hoc force, so the certificate is stamped
  ;; unclean and the open pays the full scan.
  (let [dir (tmpdir)]
    (try
      (with-kb dir
        (fn [kb]
          (v/assert kb '(cat Rex) 'CxUniverse {:strength :default})
          (v/assert kb '(dog Rex) 'CxUniverse {:strength :monotonic})
          (v/assert kb '(disjoint dog cat) 'CxUniverse {:strength :monotonic})
          (v/recover kb)
          (is (= #{'(cat Rex)} (out-sentences kb)) "the defeasible member loses")))
      (testing "the stamp records the loser and refuses the fast path"
        (with-kb dir
          (fn [kb]
            (let [m (bs/read-meta (:records kb))]
              (is (false? (:clean? m)))
              (is (= 1 (:out-count m)))
              (is (= 1 (:clash-losers m))))
            (is (false? (bs/usable? (:records kb))) "unclean is never usable"))))
      (testing "the fallback full recover still reaches the right belief"
        (with-kb dir
          (fn [kb]
            (v/recover kb)
            (is (= #{'(cat Rex)} (out-sentences kb)))
            (is (= 1 (clash-pair-count kb)) "the full recover found the clash"))))
      (finally (rm-rf! dir)))))

(deftest a-write-after-the-certificate-moves-the-fingerprint-and-voids-it
  (let [dir (tmpdir)]
    (try
      (with-kb dir
        (fn [kb]
          (v/assert kb '(genl dog animal) 'CxUniverse {:strength :monotonic})
          (v/assert kb '(dog Rex) 'CxUniverse {:strength :default})
          (v/recover kb)))
      (with-kb dir
        (fn [kb]
          (is (true? (bs/usable? (:records kb))) "fresh certificate is usable")))
      (testing "one more record moves the slot fingerprint"
        (with-kb dir
          (fn [kb]
            (v/recover kb)
            (v/assert kb '(dog Muffet) 'CxUniverse {:strength :default})))
        (with-kb dir
          (fn [kb]
            (is (false? (bs/usable? (:records kb)))
                "the stamp no longer matches the records"))))
      (finally (rm-rf! dir)))))

(deftest with-the-switch-off-nothing-is-written-and-nothing-is-trusted
  (let [dir (tmpdir)]
    (try
      (System/clearProperty prop)
      (with-kb dir
        (fn [kb]
          (v/assert kb '(dog Rex) 'CxUniverse {:strength :default})
          (v/recover kb)
          (is (not (.exists (io/file dir "belief" "meta.edn")))
              "the slow recover writes no certificate when the switch is off")
          (is (false? (bs/usable? (:records kb)))
              "and an open never trusts one")))
      (finally
        (System/setProperty prop "true")
        (rm-rf! dir)))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.removed-test
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [vaelii.browser.removed :as removed])
  (:import (java.nio.file Files)
           (java.nio.file.attribute FileAttribute)))

(defn- with-dir [f]
  (let [d (.toFile (Files/createTempDirectory "vaelii-removed" (make-array FileAttribute 0)))]
    (try (with-redefs [removed/dir (constantly d)] (f d))
         (finally (doseq [x (reverse (file-seq d))] (io/delete-file x true))))))

(deftest the-list-keeps-the-newest-removals-per-kb
  (with-dir
    (fn [_]
      (doseq [i (range (+ 5 removed/max-kept))]
        (removed/note! "kb one" :retract [{:sentence (str "(p a" i ")") :context "Cx" :strength :default}]))
      (removed/note! "kb/two" :edit [{:sentence "(q b)" :context "Cx" :strength :monotonic}])
      (let [es (removed/entries "kb one")]
        (is (= removed/max-kept (count es)))
        (is (= (str "(p a" (+ 4 removed/max-kept) ")") (:sentence (first es))) "newest first")
        (is (= "(p a5)" (:sentence (last es))) "the oldest dropped"))
      (testing "a KB's name names its own file, whatever it is spelled with"
        (is (= ["(q b)"] (map :sentence (removed/entries "kb/two"))))))))

(deftest owners-differing-in-one-character-or-in-case-keep-two-lists
  (with-dir
    (fn [_]
      (let [owners ["a/b" "a_b" "Kb" "kb"]]
        (doseq [o owners]
          (removed/note! o :retract [{:sentence (str "(p " o ")") :context "Cx"}]))
        (is (= (map #(vector (str "(p " % ")")) owners)
               (map #(mapv :sentence (removed/entries %)) owners)))))))

(deftest a-list-owned-by-a-value-other-than-a-string-is-held-in-memory
  (with-dir
    (fn [d]
      (let [a (atom nil) b (atom nil)]
        (removed/note! a :retract [{:sentence "(p a)" :context "Cx"}])
        (is (= [["(p a)"] []] [(mapv :sentence (removed/entries a)) (removed/entries b)]))
        (is (= [d] (vec (file-seq d))) "no file is written")))))

(deftest forget-drops-one-entry
  (with-dir
    (fn [_]
      (let [[a b] (removed/note! "k" :retract [{:sentence "(p a)" :context "Cx"}
                                               {:sentence "(p b)" :context "Cx"}])]
        (is (= a (removed/entry "k" (:id a))))
        (removed/forget! "k" (:id a))
        (is (nil? (removed/entry "k" (:id a))))
        (is (= [(:id b)] (map :id (removed/entries "k"))))))))

(deftest an-unreadable-list-reads-as-empty
  (with-dir
    (fn [_]
      (spit (#'removed/file-for "k") "[{:id")
      (is (= [] (removed/entries "k"))))))

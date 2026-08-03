;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.cli-test
  "The command-line driver (`vaelii.impl.cli`).  `dispatch` takes data args and is the
  whole engine surface the shell and REPL both call, so testing it (plus the arg/option
  parsing that feeds it) covers the CLI without spawning a process."
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.catalog :as catalog]
            [vaelii.impl.cli :as cli]
            [vaelii.impl.io.import :as imp]
            [vaelii.test-util :as tu])
  (:import [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(deftest parse-opts-splits-positionals-and-flags
  (testing "--k v pairs and bare --flags, positionals kept in order"
    (is (= [["assert" "(dog Fido)" "Ctx"] {:dir "/tmp/kb" :strength "monotonic"}]
           (cli/parse-opts ["assert" "(dog Fido)" "--dir" "/tmp/kb" "Ctx" "--strength" "monotonic"]))))
  (testing "--memory / --starter are boolean flags"
    (is (= [[] {:memory true :starter true}] (cli/parse-opts ["--memory" "--starter"])))))

(deftest read-forms-parses-a-line-of-edn
  (is (= [(list 'dog '?x) 'MyContext] (cli/read-forms "(dog ?x) MyContext")))
  (is (= [] (cli/read-forms "   "))))

(tu/deftest-kb dispatch-runs-the-core-commands
  (tu/with-terms [dog animal Fido CliContext]
    (testing "assert returns a handle; query returns the matching sentences"
      (is (nat-int? (cli/dispatch kb "assert" [(list dog Fido) CliContext] {})))
      (is (= [(list dog Fido)] (cli/dispatch kb "match" [(list dog '?x) CliContext] {}))))
    (testing "assert-rule / genl feed ask and provable? (specificity)"
      (cli/dispatch kb "assert" [(list 'genl dog animal) CliContext] {})
      (is (true? (cli/dispatch kb "provable?" [(list animal Fido) CliContext] {})))
      (is (some #(= Fido (get % '?x)) (cli/dispatch kb "ask" [(list animal '?x) CliContext] {}))))
    (testing "handle-of + why give a proof tree"
      (let [h (cli/dispatch kb "handle-of" [(list dog Fido) CliContext] {})]
        (is (nat-int? h))
        (is (map? (cli/dispatch kb "why" [h] {})))
        (is (true? (cli/dispatch kb "in" [h] {})))))
    (testing "types lists the genl hierarchy nodes (dog is one after the genl edge)"
      (is (contains? (set (cli/dispatch kb "types" [] {})) dog))
      (is (coll? (cli/dispatch kb "contexts" [] {}))))
    (testing "an unknown command throws with the command list"
      (is (thrown? clojure.lang.ExceptionInfo (cli/dispatch kb "frobnicate" [] {}))))
    (testing "retract tears the fact down"
      (let [h (cli/dispatch kb "handle-of" [(list dog Fido) CliContext] {})]
        (cli/dispatch kb "retract" [h] {})
        (is (empty? (cli/dispatch kb "match" [(list dog Fido) CliContext] {})))))))

(tu/deftest-kb strength-option-marks-an-assert-monotonic
  (tu/with-terms [cat Felix CliContext]
    (cli/dispatch kb "assert" [(list cat Felix) CliContext] {:strength "monotonic"})
    (is (= :monotonic (v/defeat-class kb (v/handle-of kb (list cat Felix) CliContext))))))

(deftest read-arg-keeps-a-path-a-path
  (testing "an argv string that reads as EDN is data — a sentence, a context, a handle"
    (is (= (list 'dog 'Fido) (cli/read-arg "(dog Fido)")))
    (is (= 'NaturalWorldContext (cli/read-arg "NaturalWorldContext")))
    (is (= 3 (cli/read-arg "3"))))
  (testing "and one that reads as none is the string it already was, which is what an
            absolute filesystem path is: /var/lib/vaelii has two slashes and is no symbol"
    (is (= "/var/lib/vaelii" (cli/read-arg "/var/lib/vaelii"))))
  (testing "a path the reader *does* accept comes back as a symbol, so a command taking
            one reads it as text either way — which is why the path arms coerce"
    (is (= "./kbs/a-dump" (str (cli/read-arg "./kbs/a-dump"))))))

(tu/deftest-kb export-writes-a-dump-the-catalog-offers-and-the-importer-reads
  (let [root (.toFile (Files/createTempDirectory "vaelii-cli-export-"
                                                 (into-array FileAttribute [])))
        dump (io/file root "a-dump")]
    (try
      (tu/with-terms [dog Fido ExportContext]
        (cli/dispatch kb "assert" [(list dog Fido) ExportContext] {})
        (let [summary (cli/dispatch kb "export" [(.getPath dump)] {:compression "none"})]
          (testing "the command answers with the writer's own summary"
            (is (= :records (:variant summary)))
            (is (= (v/sentex-count kb) (:sentexes summary)))
            (is (pos? (:bytes summary))))
          (testing "what it wrote is a dump — the marker the catalog keys on"
            (is (= :dump (catalog/classify dump)))
            (is (= :vaelii/export (:format (imp/read-meta dump)))))
          (testing "and the importer reads it back whole"
            ;; its own space pair: the suite's scratch block is this KB's, and clearing it
            ;; from under a running test is what the block exists to prevent
            (let [target (v/open-kb {:backend :memory :record-space 66 :index-space 67
                                     :recover? false})]
              (try
                (imp/import-dump target (.getPath dump) {:belief? false})
                (is (= (v/sentex-count kb) (v/sentex-count target)))
                (is (some? (v/handle-of target (list dog Fido) ExportContext)))
                (finally (v/clear! target)))))
          (testing "--variant and --compression are the writer's own keywords, read from
                    the strings a shell hands over"
            (let [with-index (io/file root "with-index")
                  s (cli/dispatch kb "export" [(.getPath with-index)]
                                  {:variant "records+index" :compression "none"})]
              (is (= :records+index (:variant s)))
              (is (pos? (:index-entries s)))))
          (testing "exporting into a directory that already holds one is refused, in the
                    writer's words — the same message every surface reports"
            (is (thrown-with-msg? clojure.lang.ExceptionInfo #"is not empty"
                                  (cli/dispatch kb "export" [(.getPath dump)] {}))))))
      (finally (doseq [^File f (reverse (file-seq root))] (.delete f))))))

(tu/deftest-kb load-reads-edn-entries-and-asserts-them-in-one-batch
  (tu/with-terms [dog cat Fido Felix LoadContext]
    (let [f (File/createTempFile "vaelii-cli-load" ".edn")]
      (try
        (spit f (pr-str [[(list dog Fido) LoadContext] [(list cat Felix) LoadContext]]))
        (is (= {:loaded 2} (cli/dispatch kb "load" [(.getPath f)] {})))
        (is (seq (v/sentexes-matching kb (list dog Fido) LoadContext)))
        (is (seq (v/sentexes-matching kb (list cat Felix) LoadContext)))
        (finally (.delete f))))))

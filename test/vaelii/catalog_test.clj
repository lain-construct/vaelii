;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.catalog-test
  "The KB catalog: what it offers, what a load does to the registry, and the two
  properties an operator's tool has to get right — unloading releases what it held, and
  unloading an on-disk KB does not destroy it."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.browser.catalog :as cat]
            [vaelii.browser.jobs :as jobs]
            [vaelii.catalog-fixture :as cf :refer [wait-for]]
            [vaelii.core :as v]
            [vaelii.host.core-context :as core-context]
            [vaelii.impl.io.import :as import]
            [vaelii.test-util :as tu]))

(use-fixtures :each cf/empty-registry)

;; ---- sources -------------------------------------------------------------

(deftest the-shipped-sources-are-always-offered
  (let [by-id (into {} (map (juxt :id identity)) (cat/sources))]
    (is (contains? by-id "core"))
    (is (contains? by-id "starter"))
    (is (contains? by-id "generated"))
    (testing "a source describes its own form controls, so the page renders from data"
      (is (seq (:options (by-id "generated"))))
      (is (some #(= :types (:key %)) (:options (by-id "generated"))))
      (is (some #(= :seed  (:key %)) (:options (by-id "generated")))))
    (testing "ids are unique — the registry keys entries by them"
      (is (apply distinct? (map :id (cat/sources)))))))

(deftest a-source-nothing-offers-is-refused-by-its-id
  ;; The refusal is for a caller naming a KB this machine does not have — a bookmarked
  ;; key, a catalog entry whose directory moved.  Registered as an entry that then loads
  ;; nothing, it would sit in the list saying `:running` with no loader behind it.
  (let [e (is (thrown? clojure.lang.ExceptionInfo (cat/load-source "no-such-source")))]
    (is (= :unknown-source (:type (ex-data e)))))
  (is (empty? (cat/entries)) "and no entry was registered for it")
  (testing "and the loader's own arm, for a source whose kind nothing here reads: the
            key is claimed by the time `run-load` is reached, so the refusal has to be
            one the entry can be dropped on"
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (#'cat/run-load {:kind :not-a-kind :path "/nowhere"} {}
                                         (fn [_] nil) (fn [_ _] nil))))]
      (is (= :unknown-source (:type (ex-data e))))
      (is (= :not-a-kind (:kind (ex-data e))) "and it names the kind it could not read"))))

(deftest a-directory-is-classified-by-the-marker-its-writer-left
  (let [root (io/file (System/getProperty "java.io.tmpdir")
                      (str "vaelii-catalog-test-" (System/nanoTime)))]
    (try
      (let [corpus  (io/file root "a-corpus")
            dump    (io/file root "a-dump")
            store   (io/file root "a-store")
            derived (io/file root "a-derived-index-store")
            bare    (io/file root "records-but-no-store")
            plain   (io/file root "not-a-kb")]
        (doseq [^java.io.File d [corpus dump store derived bare plain]] (.mkdirs d))
        (spit (io/file corpus "meta.edn") (pr-str {:context-order '[CxOne]}))
        (spit (io/file dump "meta.edn")   (pr-str {:format-version 8 :sentex-count 42}))
        (.mkdirs (io/file store "records"))
        (.mkdirs (io/file store "index"))
        (spit (io/file store "records" "format.edn") (pr-str {:format-version 1}))
        (is (= :corpus (cat/classify corpus)))
        (is (= :dump   (cat/classify dump)))
        (is (= :store  (cat/classify store)))
        (is (nil? (cat/classify plain)))
        (testing "a store whose index is DERIVED writes no index/ at all and is a store
                  all the same — :disk-columnar, :disk-dense and :disk-memory each look
                  like this, which is every backend a corpus past a few million records
                  is loaded into"
          (.mkdirs (io/file derived "records"))
          (spit (io/file derived "records" "format.edn") (pr-str {:format-version 1}))
          (is (= :store (cat/classify derived))))
        (testing "and the marker is the record writer's own format file rather than the
                  directory's name, so an empty records/ is still nothing"
          (.mkdirs (io/file bare "records"))
          (is (nil? (cat/classify bare))))
        (testing "a KB whose records are on a server keeps no records/ here, and its
                  index's records identity is the marker"
          (let [served (io/file root "records-on-a-server")]
            (.mkdirs (io/file served "index"))
            (spit (io/file served "index" "records.edn")
                  (pr-str {:records ["localhost" 5432 "vaelii" "kb_one"]}))
            (is (= :store (cat/classify served)))))
        (testing "an unreadable meta.edn makes a directory no KB rather than an error"
          (spit (io/file plain "meta.edn") "{not edn")
          (is (nil? (cat/classify plain)))))
      (finally
        (doseq [f (reverse (file-seq root))] (.delete ^java.io.File f))))))

(deftest a-blank-search-path-is-unset-rather-than-no-directories-at-all
  ;; A blank value is *unset* everywhere else this build reads a switch
  ;; (`vaelii.impl.config`, `guard/api-token`).  Read as a value here it splits to
  ;; nothing and discovery walks **no** directory at all, so `/kbs` offers the built-ins
  ;; and reports nothing found — which a reader takes for a machine holding no KBs rather than for
  ;; a variable somebody exported empty.  The catalog file's name is the same shape: a
  ;; blank one named the empty path, which is no file, so every entry in it went missing.
  (let [path (System/getProperty "vaelii.kb.path")
        cat  (System/getProperty "vaelii.kb.catalog")]
    (try
      (System/setProperty "vaelii.kb.path" "  ")
      (System/setProperty "vaelii.kb.catalog" "")
      (let [env (System/getenv "VAELII_KB_PATH")]
        (is (= (if (str/blank? env)
                 [(str (System/getProperty "user.dir") "/kbs")
                  (str (System/getProperty "user.home") "/.vaelii/kbs")]
                 (remove str/blank? (str/split env #":")))
               (cat/search-path))
            "a blank value falls through, so discovery still has somewhere to walk"))
      (is (not-any? str/blank? (cat/search-path))
          "and no entry of what it walks is the empty path")
      (is (not (str/blank? (str (#'cat/catalog-file))))
          "the catalog file falls through to a name rather than to the empty path")
      (finally
        (if path
          (System/setProperty "vaelii.kb.path" path)
          (System/clearProperty "vaelii.kb.path"))
        (if cat
          (System/setProperty "vaelii.kb.catalog" cat)
          (System/clearProperty "vaelii.kb.catalog"))))))

(deftest a-misspelt-belief-choice-reaches-the-importer-rather-than-defaulting
  ;; The form speaks in verbs and `import-dump` speaks in `true` / `:stored` / `false`,
  ;; so the catalog widens one into the other.  What it must not do is *swallow* the
  ;; importer's own refusal: defaulted here, `{:belief? :store}` — one letter off
  ;; `:stored` — is treated as the records-only load, which never opens the justification
  ;; stream, so what the typo dropped is dropped for good and nothing says so.
  (let [mode #'cat/belief-mode]
    (testing "the three verbs, and the importer's own vocabulary, translate"
      (is (= true    (mode :rebuild)))
      (is (= :stored (mode :stored)))
      (is (false?    (mode :skip)))
      (is (= true    (mode true)))
      (is (false?    (mode false)))
      (is (false?    (mode nil)) "no choice submitted is the form's own default")
      (is (every? #(contains? import/belief-modes (mode %))
                  [:rebuild :stored :skip true false nil])))
    (testing "and anything else is handed on, so import-dump refuses it by name"
      (is (= :store (mode :store)))
      (is (not (contains? import/belief-modes (mode :store)))))))

(deftest a-corpus-loaded-with-no-profile-takes-the-profile-the-card-offers
  ;; `load-dir`'s params are the kind's options, and the corpus kind declares
  ;; `:default "ontology"` for `:profile`, which the card's form fills in.  A caller that
  ;; names no profile — `load-dir` or `load-source` with `{}` — gets the card's load.
  (let [asked   (atom [])
        offered (:default (first (filter #(= :profile (:key %)) @#'cat/corpus-options)))]
    (with-redefs-fn {#'cat/open-kb-for       (fn [_] [::kb {:backend :memory}])
                     #'core-context/load-into (fn [_] nil)
                     #'v/load-foreign!        (fn [_ _ _ opts] (swap! asked conj (:profile opts)) {})}
      (fn []
        (doseq [params [{} {:profile "full"}]]
          (#'cat/run-load {:kind :corpus :path "/nowhere"} params (fn [_] nil) (fn [_ _] nil)))))
    (is (= "ontology" offered) "the card offers the ontology profile first")
    (is (= [:ontology :full] @asked)
        "an absent profile loads the one the card offers, and a named one is kept")))

;; ---- the lifecycle -------------------------------------------------------

(deftest loading-registers-an-entry-and-activates-the-first-one
  (let [key (cat/load-source "core")]
    (is (some #(= key (:key %)) (cat/entries)))
    (is (wait-for))
    (let [e (first (filter #(= key (:key %)) (cat/entries)))]
      (is (= :done (:status e)))
      (is (= :done (get-in e [:progress :phase])))
      (testing "the entry carries the counts the page shows"
        (is (= (v/sentex-count (cat/active-kb)) (:sentexes (:stats e))))
        (is (= (v/term-count (cat/active-kb)) (:terms (:stats e)))))
      (testing "the first KB loaded becomes the one the browser reads"
        (is (= key (cat/active)))
        (is (some? (cat/active-kb)))))))

(deftest a-public-entry-is-safe-to-render-and-send
  (cat/load-source "core")
  (wait-for)
  (let [e (first (cat/entries))]
    (testing "the KB itself stays out of the public entry, and the thread and the cancel flag are
              not the entry's to hold in the first place — they belong to its job"
      (is (not (contains? e :kb)))
      (is (not (contains? e :future)))
      (is (not (contains? e :cancel))))
    (testing "the status, the progress and the elapsed time are read off that job, so the
              panel and the loader cannot tell two stories"
      (is (string? (:job e)))
      (is (= :done (:status e)))
      (is (= :done (:status (jobs/job (:job e))))))
    (is (number? (:elapsed-ms e)))))

(deftest an-entry-outlives-its-jobs-report-and-still-says-what-became-of-it
  ;; A settled job ages out of the registry after an hour, and the entry stays — so the
  ;; status the entry keeps *of its own* has to be the settled one.  While it was still the
  ;; placeholder a load registered with, an hour was all it took for a finished KB to become
  ;; permanently unwritable (`write-blocked?`) and permanently un-unloadable
  ;; (`:still-stopping`), with nothing running and no job to point at.
  (let [key (cat/load-source "core")]
    (is (wait-for))
    (let [kb (:kb (cat/entry key))]
      ;; the sweep, without the hour: the registry forgets, the entry does not
      (jobs/reset-registry!)
      (is (nil? (jobs/job (:job (cat/entry key)))) "the job's report is gone")
      (let [e (cat/entry key)]
        (is (= :done (:status e)) "and the entry answers for itself")
        (is (= :done (get-in e [:progress :phase])))
        (is (number? (:finished e)) "so elapsed time stops growing"))
      (is (false? (cat/write-blocked? kb)) "the KB is writable, as it was an hour ago")
      (is (true? (cat/unload! key)) "and it can still be taken down"))))

(deftest ^:slow one-load-at-a-time
  (cat/load-source "generated" {:types 200 :individuals 4000 :facts 20000 :rules 100})
  (testing "a second load while one is running is refused, not queued: two at once make
            each other's timings meaningless and each other's memory unpredictable"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"already running"
                          (cat/load-source "core"))))
  (is (wait-for)))

(deftest a-source-is-not-loaded-twice-over
  (cat/load-source "core")
  (wait-for)
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"already loaded" (cat/load-source "core")))
  (testing "unless it is one a second copy makes sense of — the generator, at another shape"
    (let [a (cat/load-source "generated" {:types 5 :individuals 5 :facts 5 :rules 1})]
      (wait-for)
      (let [b (cat/load-source "generated" {:types 6 :individuals 6 :facts 6 :rules 1 :seed 2})]
        (wait-for)
        (is (not= a b))
        (is (= 3 (count (cat/entries))))))))

(deftest a-key-the-registry-already-holds-is-not-loaded-over
  ;; The refusal is for a second load under one key.  It would open a second set of
  ;; stores, file them over the first, and leave that one resident for the life of the
  ;; JVM with nothing pointing at it.  A KB `register!` filed under a source's own id is
  ;; that key taken — how a browser started on one files it — so asking for the source
  ;; is asking for it twice.
  (tu/with-cleared-kb [kb tu/fresh]
    (cat/register! "core" "My KB" kb {:source (cat/source "core")})
    (let [e (is (thrown? clojure.lang.ExceptionInfo (cat/load-source "core")))]
      (is (= :already-loaded (:type (ex-data e))))
      (is (= "core" (:key (ex-data e))) "the refusal names the entry that is in the way"))
    (is (= 1 (count (cat/entries))) "and nothing was registered beside it")
    (is (false? (cat/loading?)) "nor was a loader started")
    (cat/unload! "core")))

(deftest a-load-past-the-entry-cap-is-refused-and-evicts-nothing
  (let [cap  @#'cat/max-entries
        held (mapv #(str "remote#" %) (range cap))]
    ;; remote handles, as `--attach` files a daemon: an entry with no stores to release
    (doseq [k held] (cat/register! k k {:mode :remote :conn ::stub}))
    (let [e (is (thrown? clojure.lang.ExceptionInfo (cat/load-source "generated" {:types 2})))]
      (is (= :too-many-kbs (:type (ex-data e))))
      (is (= held (:entries (ex-data e))) "the refusal names the entries in the way"))
    (is (= held (mapv :key (cat/entries))) "and every entry is still there")
    (is (false? (cat/loading?)) "nor was a loader started")
    (cat/unload! (first held))
    (testing "an unload makes room"
      (is (string? (cat/load-source "core")))
      (is (wait-for)))))

(deftest live-kbs-lists-in-process-kbs-and-omits-a-remote-handle
  ;; The memory-pressure guard trims per-KB caches, so catalog/install-memory-guard! feeds it
  ;; the KBs open in this JVM.  A KB is one with a record store (:records); an attached
  ;; daemon's entry holds a remote handle with none, and the guard would trim nothing on a
  ;; name that has no local cache, so live-kbs leaves it out.
  (tu/with-cleared-kb [kb tu/fresh]
    (cat/register! "base" "Base KB" kb {:source (cat/source "core")})
    (is (= [kb] (cat/live-kbs)) "the in-process KB is listed")
    (cat/register! "far" "A daemon" {:daemon "http://elsewhere:3000"}
                   {:source (cat/source "core")})
    (is (= [kb] (cat/live-kbs))
        "and a remote handle with no :records is left off")))

(deftest activating-switches-what-the-holder-yields
  (let [a (cat/load-source "core")
        _ (wait-for)
        b (cat/load-source "generated" {:types 8 :individuals 8 :facts 8 :rules 2})
        _ (wait-for)
        holder (cat/holder ::fallback)]
    (is (= a (cat/active)))
    (is (= (:kb (cat/entry a)) @holder))
    (is (cat/activate b))
    (is (= (:kb (cat/entry b)) @holder))
    (testing "an entry that holds no KB is the one thing activate refuses"
      (is (nil? (cat/activate "no-such-entry")))
      (is (= b (cat/active))))
    (testing "the holder falls back when nothing is loaded at all"
      (cat/reset-registry!)
      (is (= ::fallback @holder)))))

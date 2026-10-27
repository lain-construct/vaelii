;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.settle-hour-test
  "`settle-record-edits!` on a full-size store, timed by phase and held to an hour.

  The maintainer's bound: a settle of the full KB takes an hour at most.  `lein perf`'s
  `:settle` checks hold each phase per unit on a memory KB at the full KB's shape
  (`vaelii.bench.perf/settle-hour` has the arithmetic), which is necessary for the hour and
  not sufficient: a postgres or disk store pays a fetch a memory KB does not.  This is the
  sufficient half, on the store itself.

  **`^:full-kb`, and opt-in beyond that.**  It opens the store under `VAELII_FULL_KB_DIR`
  (the disposable clone `lein test-full-kb` makes) without belief, which is the state
  `edit-records!` leaves, removes `VAELII_SETTLE_REMOVE` stored premises (default 0) through
  `edit-records!`, and settles: the rebuild, the sweep with the releases its settle draws,
  and the `record-arg-types` pass.  It runs only with `VAELII_SETTLE_HOUR=1`, because the
  probes of `full_kb_test` open the same clone with belief, and two full-size KBs do not
  fit one heap:

      VAELII_SETTLE_HOUR=1 lein test-full-kb <store> :only vaelii.settle-hour-test

  The phases print as a table, minutes each, and the test fails when they sum past 60.
  The clone shares the store's blocks and is deleted after, so the store itself is not
  written.  A postgres store has no clone (its schema is the server's), so one is refused.

  The unmarked twin runs the same harness on a few hundred records, so a phase the timer
  stops finding fails at `:default` rather than on the next full-size run."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.record-edit :as record-edit]
            [vaelii.impl.special :as special]
            [vaelii.test-util :as tu]))

(def ^:private hour-ms (* 60 60 1000))

(defn- timed
  "`f` wrapped to add its wall milliseconds under `k` in the volatile `acc`."
  [acc k f]
  (fn [& args]
    (let [t (System/nanoTime)]
      (try (apply f args)
           (finally (vswap! acc update k (fnil + 0.0) (/ (- (System/nanoTime) t) 1e6)))))))

(defn settle-phases
  "Settle `kb` (a KB without belief) after removing `removed` handles, timing each phase:
  `{:answer settle-record-edits!'s answer, :ms {phase ms}}`.  `:rebuild` is `reindex` or
  `recover`, `:sweep` the sweep less the releases its settle draws, `:release` every
  release, the sweep's and those the rebuild or the pass draw (`special/withheld-releases`), `:pass` `record-arg-types`, `:edit` the `edit-records!`
  before them, and `:total` the settle."
  [kb removed]
  (let [acc     (volatile! {})
        inside  (volatile! false)
        reindex v/reindex
        recover v/recover
        sweep   record-edit/sweep!
        release special/withheld-releases
        pass    v/record-arg-types
        r       (when (seq removed)
                  ((timed acc :edit v/edit-records!) kb {:remove removed}))
        t       (System/nanoTime)
        answer  (with-redefs [v/reindex                  (timed acc :rebuild reindex)
                              v/recover                  (timed acc :rebuild recover)
                              record-edit/sweep!         (fn [& args]
                                                           (vreset! inside true)
                                                           (try (apply (timed acc :sweep sweep) args)
                                                                (finally (vreset! inside false))))
                              special/withheld-releases  (fn [& args]
                                                           (let [k (if @inside :release-in-sweep :release-out)]
                                                             (apply (timed acc k release) args)))
                              v/record-arg-types         (timed acc :pass pass)]
                  (v/settle-record-edits! kb {:seeds (:seeds r)}))
        ms      (assoc @acc :total (/ (- (System/nanoTime) t) 1e6))
        in-sw   (get ms :release-in-sweep 0.0)]
    {:answer answer
     ;; a release drawn by the sweep's settle is timed inside the sweep as well, so it is
     ;; taken out of the sweep's figure; one drawn elsewhere (the rebuild's settle, the
     ;; pass) is not inside it
     :ms     (cond-> (-> ms
                         (dissoc :release-in-sweep :release-out)
                         (assoc :release (+ in-sw (get ms :release-out 0.0))))
               (:sweep ms) (update :sweep - in-sw))}))

(defn- table
  "The phases of `settle-phases` as a table of minutes."
  [ms]
  (str/join "\n"
            (cons (format "  %-10s %10s" "phase" "minutes")
                  (for [k [:edit :rebuild :sweep :release :pass :total]
                        :when (contains? ms k)]
                    (format "  %-10s %10.2f" (name k) (/ (double (ms k)) 60000.0))))))

(defn- premises-to-remove
  "Up to `n` stored premises of `kb` naming no `except`, `defeat` or `exceptWhen`, which
  `edit-records!` refuses."
  [kb n]
  (let [recs (:records kb)]
    (into [] (comp (keep #(p/get-sentex recs %))
                   (remove #(let [s (:sentence %)]
                              (and (seq? s) (contains? '#{except defeat exceptWhen} (first s)))))
                   (map :id)
                   (take n))
          (when (pos? n) (p/premise-ids recs)))))

(deftest ^:full-kb settle-of-the-full-kb-within-an-hour
  (let [dir (System/getenv "VAELII_FULL_KB_DIR")]
    (if-not (= "1" (System/getenv "VAELII_SETTLE_HOUR"))
      (println "settle-hour: skipped — VAELII_SETTLE_HOUR=1 runs it (it opens the full KB without belief)")
      (do
        (is (some? dir) "VAELII_FULL_KB_DIR names the clone — run `lein test-full-kb`")
        (when dir
          (let [backend (v/store-backend dir)
                pg?     (str/starts-with? (name (or backend :none)) "pg")]
            (is (not pg?) "a postgres store's clone shares the server schema: settle a disk store")
            (when-not pg?
              (binding [argument/*assertive-arg-types?* true]
                (let [kb (v/open-kb {:backend backend :dir dir :recover? false :naming :warn})
                      n  (parse-long (or (System/getenv "VAELII_SETTLE_REMOVE") "0"))
                      {:keys [answer ms]} (settle-phases kb (premises-to-remove kb n))]
                  (println (str "settle-record-edits! on " dir ", "
                                (count (p/sentex-ids (:records kb))) " records:\n" (table ms)
                                "\n  " (pr-str answer)))
                  (is (<= (- (:total ms) (get ms :edit 0.0)) hour-ms)
                      (str "the settle took " (format "%.1f" (/ (:total ms) 60000.0))
                           " minutes, over the hour")))))))))))

(deftest the-settle-phases-are-timed
  ;; the twin: a forward chain whose premise is removed, a mint withheld by the
  ;; membership the removal sweeps, and the pass that draws it again
  (binding [argument/*assertive-arg-types?* true]
    (let [kb (tu/fresh)
          M  {:strength :monotonic}
          C  'CxUniverse]
      (v/with-deferred-settle kb
        (v/assert kb '(genl sh_animal thing) C M)
        (v/assert kb '(genl sh_dog sh_animal) C M)
        (v/assert kb '(arg shOwns 1 sh_animal) C M)
        (v/assert-rule kb '[(sh_s ?x)] '(sh_dog ?x) C {:direction :forward})
        (dotimes [i 50]
          (let [x (symbol (str "ShX" i))]
            (v/assert kb (list 'sh_s x) C {})
            (v/assert kb (list 'shOwns x 'ShHome) C {}))))
      (let [removed (mapv #(v/handle-of kb (list 'sh_s (symbol (str "ShX" %))) C) (range 10))
            kb2     (tu/test-kb)
            {:keys [answer ms]} (settle-phases kb2 removed)]
        (testing "every phase is timed, and the table prints them"
          (is (= #{:edit :rebuild :sweep :release :pass :total} (set (keys ms))))
          (is (every? #(<= 0.0 %) (vals ms)))
          (is (str/includes? (table ms) "release")))
        (testing "the settle did what it says"
          (is (contains? #{:reindex :recover} (:rebuilt answer)))
          (is (nil? (v/handle-of kb2 '(sh_dog ShX0) C)))
          (is (some? (v/handle-of kb2 '(sh_animal ShX0) C))))))))

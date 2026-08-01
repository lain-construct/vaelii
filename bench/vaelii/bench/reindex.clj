(ns vaelii.bench.reindex
  "What a **derived index over durable records** costs to open.

  `:disk-memory` and `:disk-columnar` keep the records on disk and the index in RAM, on
  the grounds that the index is recomputable and so need never be written.  The price is
  that it *is* recomputed, wholesale, on every open: one pass over every stored record
  through `reindex`, then `recover` over the result.  That is the number this harness
  produces, and it is the input to two decisions — whether persisting a snapshot of the
  derived index is worth building, and whether the rebuild wants parallelizing.

  The two halves are timed apart because they scale differently and only one of them is
  new here: `reindex` is the index rebuild (linear in records), `recover` is the TMS +
  taxonomy rebuild every durable KB already pays.

  Run: `lein bench-reindex [facts] [rules] [index-backend]`
       (default 100000 facts, 0 rules, :memory — `columnar` for the other mixed mode)."
  (:require [vaelii.core :as v]
            [vaelii.impl.disk.backend :as disk]
            [vaelii.impl.io.generate :as gen]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reindex :as reindex]))

(defn- tmpdir ^String []
  (str (java.nio.file.Files/createTempDirectory
        "vaelii-reindex-" (into-array java.nio.file.attribute.FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (java.io.File. dir)))] (.delete ^java.io.File f)))

(defmacro ^:private timed [& body]
  `(let [t0# (System/nanoTime) r# (do ~@body)]
     [r# (/ (- (System/nanoTime) t0#) 1e6)]))

(defn- run [facts rules index-kind]
  (let [dir (tmpdir)]
    (try
      (let [kb (v/open-kb {:records :disk :index index-kind :dir dir :recover? false})
            _  (v/clear! kb)
            [summary load-ms]
            (timed (gen/load-into kb {:facts facts :rules rules :individuals (max 100 (quot facts 5))
                                      :types 200 :predicates 40 :chain? false}))
            n  (count (p/sentex-ids (:records kb)))]
        (println (format "generated %,d records (%,d facts, %,d rules requested, %,d derived) in %.1f s"
                         n (long facts) (long rules) (long (:derived summary 0)) (/ load-ms 1000.0)))
        ;; the open path, in its two halves — exactly what `{:recover? :auto}` runs
        (let [[res ix-ms]  (timed (reindex/reindex kb))
              [_   rec-ms] (timed (v/recover kb))
              total        (+ ix-ms rec-ms)]
          (println (format "\nindex backend %s, %,d records" index-kind n))
          (println (format "  reindex  %8.0f ms   (%,d sentexes, %,d rules)  %,.0f records/s"
                           ix-ms (long (:sentexes res)) (long (:rules res))
                           (/ n (/ ix-ms 1000.0))))
          (println (format "  recover  %8.0f ms" rec-ms))
          (println (format "  OPEN     %8.0f ms   → %,.0f records/s   ⇒ %.1f min at 100M"
                           total (/ n (/ total 1000.0))
                           (/ (* (/ total n) 100000000) 60000.0)))))
      (finally (disk/close-dir! dir) (rm-rf! dir)))))

(defn -main [& args]
  (let [facts (Long/parseLong (or (first args) "100000"))
        rules (Long/parseLong (or (second args) "0"))
        kind  (keyword (or (nth args 2 nil) "memory"))]
    (run facts rules kind)
    (shutdown-agents)
    (System/exit 0)))

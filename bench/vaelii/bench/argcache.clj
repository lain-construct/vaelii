;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.argcache
  "Caching sub-experiment for the argument-column trie: does memoizing the
  predicate-agnostic point reads (`sentexes-with-arg` / `count-with-arg`) pay on the
  belief-settle sweep?

  Reuses the macro corpus from `vaelii.bench.argindex` (its private `build-macro!`), then
  times one `recover` three ways on the same settled KB:

    * cache-off    — `kv/*arg-point-cache*` nil (the default; the sweep bypasses the memo)
    * cache-on     — the memo bound to a fresh atom for the whole recover
    * sweep-bypass — the memo exists but the sweep leaves it nil, which on a recover that
                     is entirely sweep is the cache-off path — reported to make the point
                     that the recommended default already IS sweep-bypass.

  Run: `lein with-profile +bench run -m vaelii.bench.argcache`"
  (:require [vaelii.bench.argindex :as ai]
            [vaelii.core :as v]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.reindex :as reindex])
  (:import [com.sun.management ThreadMXBean]
           [java.lang.management ManagementFactory]))

(def ^:private ^ThreadMXBean thread-mx
  (let [b (ManagementFactory/getThreadMXBean)]
    (when (instance? ThreadMXBean b) (.setThreadAllocatedMemoryEnabled ^ThreadMXBean b true))
    b))

(defn- alloc ^long []
  (let [ids (.getAllThreadIds thread-mx)
        arr (.getThreadAllocatedBytes thread-mx ids)]
    (areduce arr i acc 0 (let [v (aget arr i)] (if (pos? v) (+ acc v) acc)))))

(defmacro timed [& body]
  `(let [t0# (System/nanoTime) r# (do ~@body)] [r# (- (System/nanoTime) t0#)]))

(defn- time-recover [kb bind-cache?]
  (let [a0 (alloc)
        [_ ns] (if bind-cache?
                 (binding [kv/*arg-point-cache* (atom {})] (timed (v/recover kb)))
                 (timed (v/recover kb)))]
    {:s (/ ns 1e9) :bytes (- (alloc) a0)
     :contradictions (count (v/contradictions kb))}))

(defn -main [& _]
  (let [opts (var-get #'ai/macro-defaults)
        build! (var-get #'ai/build-macro!)
        kb (doto (v/open-kb {:backend :memory :space 49 :recover? false :constraints :arbitrate})
             (v/clear!))]
    (println "building macro corpus…")
    (build! kb opts)
    (reindex/reindex kb)
    (println (format "built %,d sentexes\n" (long (v/sentex-count kb))))
    ;; warm the JIT / settle once, discard
    (v/recover kb)
    (let [off1 (time-recover kb false)
          on   (time-recover kb true)
          off2 (time-recover kb false)]
      (println "  -- recover, three ways (same settled KB) --")
      (println (format "  cache-off     %6.3f s  | %,d contradictions  | %,.0f MB"
                       (:s off1) (long (:contradictions off1)) (/ (:bytes off1) 1048576.0)))
      (println (format "  cache-ON      %6.3f s  | %,d contradictions  | %,.0f MB"
                       (:s on) (long (:contradictions on)) (/ (:bytes on) 1048576.0)))
      (println (format "  cache-off(2)  %6.3f s  | %,d contradictions  | %,.0f MB"
                       (:s off2) (long (:contradictions off2)) (/ (:bytes off2) 1048576.0)))
      (println (format "\n  sweep-bypass = cache-off (the sweep leaves the memo nil): %6.3f s" (:s off2)))
      (let [best-off (min (:s off1) (:s off2))]
        (println (format "  memo delta on the sweep: %+.1f%% (cache-on vs best cache-off)"
                         (* 100.0 (/ (- (:s on) best-off) best-off)))))))
  (shutdown-agents)
  (System/exit 0))

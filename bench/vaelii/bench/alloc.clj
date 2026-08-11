;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.alloc
  "What a trie lookup **allocates**, on the two trie layouts, counted rather than timed.

  The read path is the one index quantity the density work never held to its own
  standard.  `docs/density.md` trusts retained heap because it is structural and
  distrusts wall-clock because it is not, and then measures retrieval in milliseconds
  anyway.  Allocation is the read-path quantity that behaves like retained heap: it is a
  property of the code and the corpus rather than of the box, so it reads the same on a
  loaded laptop as on a quiet one.

  Two layouts walk the same trie:

  * **`KvIndexStore`** (`vaelii.impl.kv`) carries **path prefixes** on its frontier.  A
    step conjes the query token onto the prefix, wraps that in a `[:trie :count prefix]`
    key, and hashes the whole key — and the conjed vector is a fresh object whose
    `hasheq` cache is empty, so each level re-hashes what the level above it just hashed.
  * **`ColumnarIndexStore`** (`vaelii.impl.columnar`) carries **int node ids**.  A step
    interns the token to an int and binary-searches the node's edge array.  No
    path-shaped key is built and nothing is re-hashed.

  So the prediction is that the flat-map walk allocates more, and more of it the deeper
  the path runs.  Two readings qualify it, and each is a section below.  **The regime
  decides how much**: the gap is a narrowing step's, and a fanning step nearly closes it,
  because the columnar walk's `-edges` decodes every child edge into a boxed
  `[token child]` pair before `skip-one` throws the token away.  And **most of a lookup
  belongs to neither layout**: both walks rebuild the frontier as one
  `(into [] (mapcat f) frontier)` per pattern level, and on a narrowing walk that single
  term is larger than everything the layout contributes.

  ## The instrument

  `com.sun.management.ThreadMXBean/getCurrentThreadAllocatedBytes` — bytes this thread has
  allocated, cumulative, out of the JVM's own TLAB accounting.  It needs no agent, no
  profiler and no seam in the engine, and it is exact to the byte across a region bounded
  by two reads on one thread.  The harness reports the floor it measures for itself: the
  delta across two back-to-back reads, which is what the instrument costs the number.

  ## What it cannot see

  * **Scalar replacement.**  An allocation C2 proves non-escaping never reaches a TLAB and
    is invisible here.  That is a real difference between a cold walk and a hot one rather
    than a measurement error, so both are reported: `cold` is the first pass in the JVM
    and `warm` the tail mean after warm-up.  Where they differ, the hot number is what a
    running KB pays and the cold one is what the code writes.
  * **Object *count*.**  The instrument counts bytes, and nothing on this JVM counts
    objects exactly without an agent.  The object figures here are **derived from the
    source** — the vectors, wrappers and boxes the two walks name — and they are a lower
    bound: the seq cells `mapcat` builds, the transient vector `into` builds per level,
    and the answer set at the terminus are none of them in it.  The derived-against-
    measured row is what says how much of the total that leaves.
  * **Which objects.**  A byte here is a byte wherever it came from, so this instrument
    alone cannot attribute a walk to its call sites.
  * **Anything off the walk.**  `B/lookup` includes the answer set the terminus builds,
    which both layouts build alike, so the shapes below are chosen to return few handles
    — the difference between the two rows is the walk, not the answer.

  ## The denominator

  `vaelii.impl.profile`'s `:fan` tally already counts **node probes** per walk, so
  per-probe is a normalization the engine computes rather than one this harness invents.
  The tally fires on `KvIndexStore` only (`docs/profile.md` says so), and a probe count is
  a property of the trie and the pattern rather than of the layout — the two walks hold
  the same frontier at every level — so the `:memory` arm's `:visits` is the denominator
  for both.  That the two agree is checked rather than assumed: every pattern's answer
  set is compared across the layouts before anything is measured, because a walk that
  quietly found nothing allocates almost nothing and would report as a win.

  Run: `lein bench-alloc [facts]`  (default 20000).  Spaces 21 and 22."
  (:require [vaelii.bench.util :as u]
            [vaelii.impl.columnar :as columnar]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.tokens :as tok])
  (:import [com.sun.management ThreadMXBean]
           [java.lang.management ManagementFactory]
           [org.openjdk.jol.info ClassLayout]))

;; ---- the instrument -----------------------------------------------------

(def ^:private thread-mx (ManagementFactory/getThreadMXBean))

(defn- allocated
  "Bytes this thread has allocated so far."
  ^long []
  (.getCurrentThreadAllocatedBytes ^ThreadMXBean thread-mx))

(defn- instrument-floor
  "The instrument's own allocation: the largest delta across `n` back-to-back reads.  A
  reading at or below this is noise rather than a measurement, the same courtesy
  `bench/perf.clj` extends with `noise-floor-ns`."
  ^long [^long n]
  (loop [i 0, worst 0]
    (if (< i n)
      (let [a (allocated), b (allocated)]
        (recur (inc i) (max worst (- b a))))
      worst)))

;; A live sink for each pass's checksum, so nothing measured can be dead code.  Written
;; *after* the closing read, so the write is outside every measured region.
(def ^:private sink (volatile! 0))

(def ^:private tail-blocks
  "How many blocks from the end of a run the answer is the mean of — the same count on
  both layouts, so the two answers average over windows of equal width."
  8)

(defn- tail-mean
  ^double [xs]
  (let [v (vec xs)
        k (min (count v) tail-blocks)]
    (/ (double (reduce + (subvec v (- (count v) k)))) k)))

;; ---- the corpus ---------------------------------------------------------

(defn- gen-facts
  "`n` ground facts of arity `arity` over a Zipf-skewed vocabulary — the skew shape
  `bench-postings` loads, so the trie's fan-out is a real one rather than a uniform one."
  [{:keys [n arity preds inds ctxs seed]}]
  (let [rng  (java.util.Random. (long seed))
        pcum (u/zipf-cumulative (count preds) 1.2)
        icum (u/zipf-cumulative (count inds) 1.0)]
    (into []
          (map (fn [_]
                 (let [pred (nth preds (u/zipf-sample pcum rng))
                       args (repeatedly arity #(nth inds (u/zipf-sample icum rng)))
                       ctx  (nth ctxs (.nextInt rng (count ctxs)))]
                   (sx/sentex (apply list pred args) ctx))))
          (range n))))

(defn- fill!
  "Index every sentex, handles allocated in order — the order a real load gives them,
  which is what makes a posting's clustering realistic."
  [store sentexes]
  (reduce (fn [^long h sx] (p/index-sentex store sx h) (inc h)) 1 sentexes)
  store)

(defn- stores
  "A `:memory` index store and a `:memory-columnar` one, both cleared and both holding
  `sentexes`."
  [sentexes]
  (let [kv  (doto (mem/memory-index-store {:space 21}) (p/clear-index!))
        col (doto (columnar/columnar-index-store {:space 22}) (p/clear-index!))]
    [(fill! kv sentexes) (fill! col sentexes)]))

;; ---- the workload -------------------------------------------------------
;; Four shapes over the same corpus, chosen for the two regimes a walk has rather than for
;; what a matcher would really ask.  `res/candidate-handles` would divert `after-var` to
;; the argument roots and never look it up at all; what is being measured here is the
;; *walk*, so every shape goes through `p/lookup` directly.

(def ^:private shapes
  [[:exact     "every token ground — one node per level, no fan"]
   [:tail-open "the last argument open — narrows, then fans at the tail"]
   [:after-var "the first argument open, the rest ground — fans, then ground probes at width"]
   [:lead-open "every argument open — fans at every argument level"]])

(defn- pattern-sentence
  "One pattern of `shape` over the fact sentence `(pred a1 … ak)`."
  [shape sentence]
  (let [pred (first sentence)
        args (vec (rest sentence))
        k    (count args)
        vr   (fn [i] (symbol (str "?v" i)))]
    (apply list pred
           (case shape
             :exact     args
             :tail-open (conj (subvec args 0 (dec k)) (vr 0))
             :after-var (into [(vr 0)] (subvec args 1))
             :lead-open (mapv vr (range k))))))

(def ^:private shape-widths
  "How many patterns each shape contributes.  A fanning shape costs orders more probes per
  lookup than a narrowing one, so an equal count would put the whole run inside
  `:lead-open` and measure that alone."
  {:exact 128 :tail-open 128 :after-var 32 :lead-open 8})

(defn- workload
  "`{shape [path …]}` — the trie paths for each shape, taken from facts spread across the
  corpus so the patterns meet the skew rather than one hot predicate."
  [sentexes]
  (let [n    (count sentexes)
        pick (fn [k] (mapv #(nth sentexes (mod (* % (quot n (inc k))) n)) (range k)))]
    (into {}
          (map (fn [[shape _]]
                 [shape (mapv (fn [s]
                                (sx/path (sx/sentex (pattern-sentence shape (sx/body s))
                                                    (:context s))))
                              (pick (shape-widths shape)))]))
          shapes)))

;; ---- measurement --------------------------------------------------------

(defn- pass
  "One pass over `paths`, returning a checksum of the answers so the walk cannot be
  optimized away.  A primitive loop over a vector with a primitive accumulator: the pass
  itself allocates nothing the measured region would have to be corrected for."
  ^long [store paths]
  (let [n (count paths)]
    (loop [i 0, acc 0]
      (if (< i n)
        (recur (inc i) (+ acc (long (count (p/lookup store (nth paths i))))))
        acc))))

(defn- block-bytes
  "Bytes allocated by one pass, measured between two reads with nothing else between."
  ^long [store paths]
  (let [b0 (allocated)
        r  (pass store paths)
        b1 (allocated)]
    (vreset! sink r)
    (- b1 b0)))

(defn- measure
  "Mean bytes per lookup over the tail of `blocks` blocks, after `warm` unmeasured passes.

  Both layouts warm by the same count rather than in proportion to what they cost, which
  is `perf.clj`'s hardest-won rule: warming proportionally hands one arm a JIT the other
  never got, and the reading comes back flattering whichever was warmed more.  Allocation
  is less sensitive to that than a duration is and is not immune — escape analysis runs
  only once a path is hot, and what it does is remove allocations."
  ^double [store paths {:keys [warm blocks]}]
  (dotimes [_ warm] (pass store paths))
  (let [^longs out (long-array blocks)]
    (dotimes [i blocks] (aset out i (block-bytes store paths)))
    (/ (tail-mean (vec out)) (count paths))))

(defn- probes
  "`[probes-per-lookup handles-per-lookup]` for one pass over `paths`, off the `:fan` tally
  the engine already keeps."
  [kv paths]
  (prof/start)
  (pass kv paths)
  (let [fan (vals (:fan (prof/stop)))
        cs  (reduce + (map :calls fan))
        vs  (reduce + (map :visits fan))
        hs  (reduce + (map :handles fan))]
    [(/ (double vs) (max 1 cs)) (/ (double hs) (max 1 cs))]))

(defn- agree?
  "Do the two layouts answer every pattern identically?"
  [kv col paths]
  (every? (fn [pth] (= (p/lookup kv pth) (p/lookup col pth))) paths))

;; ---- the frontier container ---------------------------------------------
;; Both walks rebuild their frontier the same way — `(into [] (mapcat f) frontier)`, once
;; per pattern level — so whatever that costs is charged to both layouts equally and is no
;; part of the layout comparison.  It is measured rather than derived, because the
;; transient vector, the transducer chain and the seq cells `mapcat` builds are all
;; implementation detail nobody should be asserting object counts about.

(defn- frontier-cost
  "Bytes one `(into [] (mapcat f) frontier)` costs over a one-node frontier — the shape
  both walks build at every level of a narrowing walk.

  A microbenchmark is the one place escape analysis is most likely to flatter, since the
  container here really is dead on return and the walk's is not, so read this as a floor
  under the per-level constant rather than as the constant."
  ^double [{:keys [warm blocks]}]
  (let [one (fn ^long [^long reps]
              (let [b0 (allocated)]
                (dotimes [_ reps]
                  (vreset! sink (count (into [] (mapcat (fn [x] [x])) [1]))))
                (- (allocated) b0)))
        reps 10000]
    (dotimes [_ warm] (one reps))
    (let [^longs out (long-array blocks)]
      (dotimes [i blocks] (aset out i (long (one reps))))
      (/ (tail-mean (vec out)) reps))))

;; ---- the derivation -----------------------------------------------------
;; What each walk allocates per ground-token probe, read off the source rather than
;; measured.  Exact for the objects the code names; a lower bound on the total, since the
;; seq cells `mapcat` builds, the transient vector `into` builds per level, and the answer
;; set at the terminus are none of them named here.  `sizes` carries jol's shallow sizes,
;; so no byte count below is a guess about object layout.

(defn- shallow ^long [x] (.instanceSize (ClassLayout/parseInstance x)))

(defn- sizes []
  {:vector (shallow [1 2 3])
   :array  (fn [^long n] (shallow (object-array n)))
   :box    (shallow (Integer/valueOf 1000))
   :key    (shallow (tok/->Key 'a))})

(def ^:private ground-probe
  "Per ground-token probe, by layout: `[what objects bytes]`, where `bytes` takes the
  prefix length at that level and the `sizes` map."
  {:memory
   [["conj'ed prefix vector, twice — the token onto the prefix" 4
     (fn [^long i s] (* 2 (+ (long (:vector s)) (long ((:array s) (inc i))))))]
    ["[:trie :count prefix] key vector" 2
     (fn [^long _i s] (+ (long (:vector s)) (long ((:array s) 3))))]
    ["[child] result vector" 2
     (fn [^long _i s] (+ (long (:vector s)) (long ((:array s) 1))))]]
   :columnar
   [["tokens/Key wrapper around the query token" 1
     (fn [^long _i s] (long (:key s)))]
    ["boxed int, three times — token id, child id, subtree count" 3
     (fn [^long _i s] (* 3 (long (:box s))))]
    ["[child] result vector" 2
     (fn [^long _i s] (+ (long (:vector s)) (long ((:array s) 1))))]]})

(defn- probe-bytes
  "Predicted structural bytes for one ground-token probe at level `i`."
  ^long [layout ^long i s]
  (reduce + (for [[_ _ f] (ground-probe layout)] (long (f i s)))))

(defn- derived-bytes
  "Predicted structural bytes for a walk that narrows all the way down a path of `len`
  levels — the `:exact` shape, where the frontier is one node wide and the derivation has
  no seq machinery in it to argue about."
  ^long [layout ^long len s]
  (reduce + (map (fn [i] (probe-bytes layout i s)) (range len))))

(defn- derived-objects ^long [layout] (reduce + (map second (ground-probe layout))))

;; ---- report -------------------------------------------------------------

(defn- fmt [^double x] (format "%,.0f" x))

(defn- rule [^long n] (str "  " (apply str (repeat n \-))))

(defn- slope
  "The marginal bytes one extra frontier node costs, between two shapes over the same
  number of levels.  This is the whole comparison: the per-level frontier container is a
  layout-independent constant, and a ratio taken over `B/lookup` divides it into both
  arms and reports a difference smaller than the one that exists.  It is the mistake
  `perf.clj` names — a baseline that already carries the cost being measured — arriving
  as a denominator rather than as a size."
  ^double [m base wide layout]
  (/ (- (double (get-in m [wide layout])) (double (get-in m [base layout])))
     (- (double (get-in m [wide :probes])) (double (get-in m [base :probes])))))

(defn- shape-table [m]
  (println "\n══ bytes per lookup, by pattern shape ══")
  (println (format "  %-11s %-11s %9s %9s %12s %10s %8s"
                   "shape" "layout" "probes" "handles" "B/lookup" "B/probe" "kv/col"))
  (println (rule 76))
  (doseq [[shape blurb] shapes]
    (let [{:keys [probes handles memory columnar]} (m shape)]
      (println (format "  %-11s %-11s %9.1f %9.1f %12s %10s"
                       (name shape) ":memory" probes handles
                       (fmt memory) (fmt (/ (double memory) probes))))
      (println (format "  %-11s %-11s %9s %9s %12s %10s %7.2f×"
                       "" ":columnar" "" "" (fmt columnar)
                       (fmt (/ (double columnar) probes))
                       (/ (double memory) (double columnar))))
      (println (format "  %-11s %s" "" blurb)))))

(defn- marginal-table [m fc]
  (println "\n══ the marginal cost of a frontier node, per regime ══")
  (println (format "  %-26s %13s %13s %8s" "regime" ":memory B" ":columnar B" "kv/col"))
  (println (rule 64))
  (doseq [[label base wide]
          [["ground probe at width" :exact :after-var]
           ["fanned child edge"     :exact :lead-open]]]
    (let [k (slope m base wide :memory)
          c (slope m base wide :columnar)]
      (println (format "  %-26s %13s %13s %7.2f×" label (fmt k) (fmt c) (/ k c)))))
  (println "\n  Both walks also rebuild one `(into [] (mapcat f) frontier)` per pattern")
  (println (format "  level, measured at %s B over a one-node frontier — a layout-independent" (fmt fc)))
  (println "  constant, and on a narrowing walk the largest single term in the lookup."))

(defn- cold-warm-table [cold m]
  (println "\n══ cold and warm — what escape analysis removes once the walk is hot ══")
  (println (format "  %-11s %14s %14s %9s" "layout" "cold B/lookup" "warm B/lookup" "removed"))
  (println (rule 52))
  (doseq [[label layout] [[":memory" :memory] [":columnar" :columnar]]]
    (let [c (double (cold layout))
          w (double (get-in m [:exact layout]))]
      (println (format "  %-11s %14s %14s %8.1f%%"
                       label (fmt c) (fmt w) (* 100.0 (- 1.0 (/ w (max 1.0 c))))))))
  (println "  Cold is the first pass in this JVM, taken before anything else runs; the two")
  (println "  arms share the transducer and protocol code, so the second is already")
  (println "  part-warmed. The direction is the reading, not the magnitude."))

(defn- derivation-table [m fc len]
  (let [s (sizes)]
    (println "\n══ objects per ground-token probe, derived from the source ══")
    (println (format "  %-11s %-58s %8s" "layout" "what the walk names" "objects"))
    (println (rule 79))
    (doseq [layout [:memory :columnar]]
      (doseq [[what objs _] (ground-probe layout)]
        (println (format "  %-11s %-58s %8d" (str layout) what (long objs))))
      (println (format "  %-11s %-58s %8d" "" "total" (derived-objects layout))))
    (println (format "\n  jol shallow sizes: PersistentVector %d B, boxed int %d B, tokens/Key %d B,"
                     (long (:vector s)) (long (:box s)) (long (:key s))))
    (println (format "  Object[1] %d B, Object[3] %d B, Object[5] %d B"
                     (long ((:array s) 1)) (long ((:array s) 3)) (long ((:array s) 5))))
    (println "\n══ the accounting, on the one shape whose walk has no fan ══")
    (println (format "  %-11s %10s %12s %12s %12s %10s"
                     "layout" "probes B" "frontier B" "accounted" "measured" "residual"))
    (println (rule 74))
    (doseq [layout [:memory :columnar]]
      (let [d   (derived-bytes layout len s)
            f   (* fc len)
            acc (+ d f)
            msd (double (get-in m [:exact layout]))]
        (println (format "  %-11s %10s %12s %12s %12s %9.0f%%"
                         (str layout) (fmt (double d)) (fmt f) (fmt acc) (fmt msd)
                         (* 100.0 (- 1.0 (/ acc msd)))))))
    (println "  The residual is the seq cells `mapcat` builds, the answer set at the")
    (println "  terminus, and the seq the pattern is walked as.")))

(defn- depth-sweep [cfg opts fc]
  (println "\n══ path length — the prefix the flat-map walk rebuilds at every probe ══")
  (println (format "  %-8s %-11s %7s %12s %14s %12s"
                   "arity" "layout" "levels" "B/lookup" "B/extra level" "predicted"))
  (println (rule 70))
  (let [prev (volatile! {})
        s    (sizes)]
    (doseq [arity [2 4 8]]
      (let [sxs      (gen-facts (assoc cfg :arity arity))
            [kv col] (stores sxs)
            paths    (mapv sx/path (take 128 sxs))
            len      (count (first paths))]
        (doseq [[label layout store] [[":memory" :memory kv] [":columnar" :columnar col]]]
          (let [b (measure store paths opts)
                [pl pb] (@prev layout [len b])]
            (vswap! prev assoc layout [len b])
            (println (format "  %-8d %-11s %7d %12s %14s %12s"
                             arity label len (fmt b)
                             (if (= len (long pl))
                               "-"
                               (fmt (/ (- b (double pb)) (- len (long pl)))))
                             (if (= len (long pl))
                               "-"
                               (fmt (+ fc (double (probe-bytes layout (dec len) s)))))))))))
    (println "  `predicted` is the measured frontier container plus the derived probe at that")
    (println "  level, and it is the whole accounting closing on itself. It runs high on")
    (println "  `:columnar` because `Integer/valueOf` caches -128..127, so the subtree-count")
    (println "  box is free at every node holding fewer than 128 sentexes.")
    (println "  A `:memory` probe conjes a prefix-sized array twice, so its cost carries the")
    (println "  depth it is at; a `:columnar` probe is an int intern and a binary search, so")
    (println "  it does not. Both pay one frontier container per extra level, which is what")
    (println "  the per-level column is mostly made of.")))

;; ---- main ---------------------------------------------------------------

(defn -main [& args]
  (let [n     (or (some-> (first args) Long/parseLong) 20000)
        cfg   {:n n :arity 2 :seed 42
               :preds (u/terms "aRel" 40)
               :inds  (u/terms "AInd" 400)
               :ctxs  (mapv #(symbol (str "ACtx" % "Context")) (range 4))}
        opts  {:warm 12 :blocks 20}
        floor (instrument-floor 1000)]
    (println (format "vaelii index-lookup allocation bake-off — %,d facts, arity 2" n))
    (println "Allocated bytes are structural the way retained heap is, so they are trusted")
    (println "under contention. Nothing here is a duration.")
    (println (format "instrument: ThreadMXBean/getCurrentThreadAllocatedBytes, floor %d B" floor))
    (let [sxs      (gen-facts cfg)
          [kv col] (stores sxs)
          wl       (workload sxs)
          exact    (wl :exact)
          ;; the cold readings first, before any other lookup runs in this JVM
          cold     {:memory   (/ (double (block-bytes kv exact)) (count exact))
                    :columnar (/ (double (block-bytes col exact)) (count exact))}]
      (doseq [[shape _] shapes]
        (when-not (agree? kv col (wl shape))
          (throw (ex-info "the two layouts disagree — a cost comparison would be meaningless"
                          {:shape shape}))))
      (println (format "both layouts agree on every answer: %d patterns over %d shapes"
                       (reduce + (map count (vals wl))) (count shapes)))
      (let [m  (into {}
                     (map (fn [[shape _]]
                            (let [paths   (wl shape)
                                  [pr hs] (probes kv paths)]
                              [shape {:probes pr :handles hs
                                      :memory   (measure kv paths opts)
                                      :columnar (measure col paths opts)}])))
                     shapes)
            fc (frontier-cost opts)]
        (shape-table m)
        (marginal-table m fc)
        (cold-warm-table cold m)
        (derivation-table m fc (count (first exact)))
        ;; last, because it rebuilds both stores over corpora of other arities
        (depth-sweep cfg opts fc)))
    (println (format "\n(checksum %d)" @sink))
    (shutdown-agents)))

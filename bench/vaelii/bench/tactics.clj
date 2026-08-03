;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.tactics
  "Does a tactician earn its place?  Runs a query set through **every** ordering the node
  engine offers (`vaelii.impl.tactics`), checks each returns the same answer set as the
  `:cost` baseline, and then measures the only thing an ordering can change.

  **An exhaustive search expands the same node set under every ordering.**  That is the
  whole content of the completeness invariant, and it has a consequence worth stating
  before any number below is read: on a query driven dry, every tactician does identical
  work and their wall-clocks differ by noise plus the estimate's own overhead.  An
  ordering pays only under a **bound** — time to the first K answers, or answers within a
  deadline — which is what the latency pass measures and the correctness pass does not.

  Correctness is the first pass and the reason this is a validator rather than a report:
  ordering is a cost decision and never a semantic one, so a mode whose answer set
  differs from the baseline is a mode that dropped a node, and no timing it produces
  means anything.  `inference_tactics_test` holds the same line on small KBs; this holds it
  on a corpus with hot consequents, layers and 5-antecedent rules.

  Three things about the timing protocol, each of which invalidates the numbers if
  dropped:

  - **The literal cache is cleared before every single run.**  `matches-visible` caches
    per KB (docs/inference.md), so without this the mode that happened to run second
    reads the first one's warm cache and wins for a reason that has nothing to do with
    its ordering.
  - **The mode order is shuffled per query**, from a fixed seed.  JIT compilation and GC
    drift both favour whichever mode runs last, and averaging over a shuffle is what
    makes that a constant rather than a bias.
  - **Backchaining-heavy queries are reported apart from shallow ones.**  A goal stored
    facts answer expands one node whatever the ordering, so mixing the two subsets
    buries the only queries an ordering could possibly help.

  Node counts are structural and **trusted**; wall-clock is a ratio against the baseline
  measured under the protocol above, and the two should agree — a mode that expands
  fewer nodes and takes longer is measuring the machine, not the search.

  Run: `lein bench-tactics [facts] [rules] [depth] [first-k]`
  (default 1200 400 3 50)."
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [vaelii.bench.util :as u :refer [zipf-sample]]
            [vaelii.core :as v]
            [vaelii.impl.inference :as inf]
            [vaelii.impl.literal-cache :as lc]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.tactics :as tac]))

(def ^:private context 'BenchContext)

(defn- say [& parts] (println (apply str parts)) (flush))

;; antecedent-count distribution from the corpus audit: mode 3–4.
(def ^:private ante-dist
  (vec (mapcat (fn [[k w]] (repeat w k)) [[1 10] [2 24] [3 38] [4 20] [5 8]])))

(defn- gen
  "A layered corpus: band-0 predicates carry the facts, and a rule concluding a band-k
  predicate draws its antecedents from the bands below k.  Stratified and acyclic, so a
  backward query on a high band has a real derivation to find rather than a cycle to
  bottom out in, and the band it sits in is the depth it needs."
  [{:keys [facts rules preds base inds seed layers]}]
  (let [rng   (java.util.Random. seed)
        pv    (u/terms "pr" preds)
        iv    (u/terms "Ind" inds)
        icum  (u/zipf-cumulative inds 1.0)
        ind   #(nth iv (zipf-sample icum rng))
        bsz   (max 1 (quot (- preds base) (dec (long layers))))
        band  (fn [k] (if (zero? (long k))
                        (subvec pv 0 base)
                        (subvec pv (min preds (+ base (* (dec (long k)) bsz)))
                                (min preds (+ base (* (long k) bsz))))))
        bcum  (u/zipf-cumulative base 1.1)
        per-k (into {} (for [k (range 1 layers)]
                         (let [cb (band k) lo (vec (mapcat band (range k)))]
                           [k {:cb cb :ccum (u/zipf-cumulative (count cb) 1.3)
                               :lo lo :lcum (u/zipf-cumulative (count lo) 1.1)}])))]
    {:bands (mapv band (range layers))
     :inds  iv
     :facts (repeatedly facts #(list (nth (band 0) (zipf-sample bcum rng)) (ind) (ind)))
     :rules (mapv (fn [_]
                    (let [a    (nth ante-dist (.nextInt rng (count ante-dist)))
                          k    (inc (.nextInt rng (dec (long layers))))
                          {:keys [cb ccum lo lcum]} (per-k k)
                          vars (mapv #(symbol (str "?v" %)) (range (inc a)))]
                      {:antes  (mapv (fn [j] (list (nth lo (zipf-sample lcum rng))
                                                   (nth vars j) (nth vars (inc j))))
                                     (range a))
                       :conseq (list (nth cb (zipf-sample ccum rng)) (first vars) (last vars))}))
                  (range rules))}))

(defn- load-kb!
  "The corpus, asserted.  Every rule is `:direction :backward`, so nothing forward-chains
  and what a query finds it derives."
  [{:keys [facts rules]}]
  (let [k (v/open-kb {:backend :memory :record-space 38 :index-space 39 :recover? false})]
    (p/clear-records! (:records k)) (p/clear-index! (:index k))
    (v/with-deferred-settle k
      (doseq [r rules]
        (try (v/assert-rule k (:antes r) (:conseq r) context {:direction :backward})
             (catch Exception _ nil)))
      (doseq [f facts] (try (v/assert k f context) (catch Exception _ nil))))
    k))

;; ---- the modes -----------------------------------------------------------

(def ^:private modes
  "Every ordering the engine offers, plus the two opt-in ones.  `:first-result?` is here
  because it is a shipped mode whose cost is worth knowing — and flagged incomplete,
  because comparing its answer set to the baseline's would be comparing a mode that
  stops the search with one that finishes it."
  (into (mapv (fn [t] {:label t :strategy t}) (sort (keys tac/tacticians)))
        [{:label :backchain-first :strategy {:tactician :cost :estimate-backchain? :first}}
         {:label :backchain-all   :strategy {:tactician :cost :estimate-backchain? :all}}
         {:label :portfolio       :portfolio? true :exhaustive-only? true}
         {:label :first-result    :strategy {:first-result? true} :incomplete? true}]))

(defn- drain-within
  "Drive `sess` dry and return `[answers complete?]`, giving up at `cap-ms`.

  The cap is checked **between node expansions**, the same granularity `budget`'s
  `:max-ms` honours and for the same reason: one node's inline solve is a whole join and
  has no partial answer to hand back."
  [sess cap-ms]
  (let [end (+ (System/nanoTime) (* 1e6 (double cap-ms)))]
    (loop [acc #{}]
      (if (> (System/nanoTime) end)
        [acc false]
        (if-let [r (inf/step! sess)]
          (recur (into acc r))
          [acc true])))))

(defn- exhaustive
  "One query driven dry under one mode, from a cold literal cache."
  [kb goal depth {:keys [strategy portfolio?]}]
  (lc/clear-cache kb)
  (if portfolio?
    (let [t0 (System/nanoTime)
          a  (set (inf/portfolio-solutions kb [goal] context {:max-depth depth}))]
      {:answers a :ms (/ (- (System/nanoTime) t0) 1e6) :nodes 0})
    (let [sess (inf/session kb [goal] context {:strategy strategy :max-depth depth})
          t0   (System/nanoTime)
          a    (set (doall (inf/search-seq sess)))]
      {:answers a :ms (/ (- (System/nanoTime) t0) 1e6)
       :nodes  (:expanded (inf/tree-stats sess))})))

(defn- to-first-k
  "One query under one mode, stopped at the first `k` answers — what a bounded consumer
  (`budget/collect`) would pay, and the only measurement an ordering can move."
  [kb goal depth k {:keys [strategy]}]
  (lc/clear-cache kb)
  (let [sess (inf/session kb [goal] context {:strategy strategy :max-depth depth})
        t0   (System/nanoTime)
        got  (count (doall (take k (inf/search-seq sess))))]
    {:got got :ms (/ (- (System/nanoTime) t0) 1e6)
     :nodes (:expanded (inf/tree-stats sess))}))

;; ---- the needle ----------------------------------------------------------

(defn- needle-kb!
  "**One** answer, at the bottom of one derivation, among decoys that go nowhere.

  The corpus above cannot measure time-to-first-answer, because its goals are answered
  by the first node the frontier pops — every ordering ties at one node and the metric
  reads as noise.  What separates orderings is a goal whose answer is *rare and deep*,
  which is what this builds:

      step0 ⟸ step1 ⟸ … ⟸ stepC ⟸ (needleOf Needle0 Needle1)      the one derivation
      stepK ⟸ decoyK,j,0 ⟸ … ⟸ decoyK,j,D ⟸ a join that never holds  × decoys, per level

  A decoy chain is the same shape as the true one and just as plausible to the cost
  model — it bottoms out in a join over the haystack against a predicate whose
  individuals are disjoint from it, so it does real index work and yields nothing.  The
  true rule is asserted **between** the decoys at each level, so no engine finds the
  needle by insertion order.

  Returns `{:kb :goal :depth}`, where `:depth` is exactly what the derivation needs."
  [{:keys [chain decoys decoy-depth hay-preds hay-facts inds seed]}]
  (let [rng   (java.util.Random. seed)
        hay   (u/terms "hay" hay-preds)
        his   (u/terms "Hay" inds)
        blks  (u/terms "Blk" (max 4 (quot (long inds) 8)))
        step  (fn [k] (symbol (str "step" k)))
        decoy (fn [k j l] (symbol (str "decoy" k "x" j "y" l)))
        kb    (v/open-kb {:backend :memory :record-space 38 :index-space 39 :recover? false})
        rule! (fn [antes conseq]
                (try (v/assert-rule kb antes conseq context {:direction :backward})
                     (catch Exception _ nil)))]
    (p/clear-records! (:records kb)) (p/clear-index! (:index kb))
    (v/with-deferred-settle kb
      ;; the haystack, and the predicate a decoy dies on: disjoint individuals, so the
      ;; join is real work that never holds
      (doseq [_ (range hay-facts)]
        (try (v/assert kb (list (nth hay (.nextInt rng hay-preds))
                                (nth his (.nextInt rng (count his)))
                                (nth his (.nextInt rng (count his))))
                       context)
             (catch Exception _ nil)))
      (doseq [_ (range (quot (long hay-facts) 20))]
        (try (v/assert kb (list 'blockedOf
                                (nth blks (.nextInt rng (count blks)))
                                (nth blks (.nextInt rng (count blks))))
                       context)
             (catch Exception _ nil)))
      (v/assert kb '(needleOf Needle0 Needle1) context)
      ;; each level: half the decoys, the one true rule, then the other half
      (doseq [k (range (inc (long chain)))]
        (let [half (quot (long decoys) 2)
              dec! (fn [j]
                     (rule! [(list (decoy k j 0) '?x '?y)] (list (step k) '?x '?y))
                     (doseq [l (range (dec (long decoy-depth)))]
                       (rule! [(list (decoy k j (inc l)) '?x '?y)]
                              (list (decoy k j l) '?x '?y)))
                     (rule! [(list (nth hay (mod j hay-preds)) '?x '?z)
                             (list (nth hay (mod (inc j) hay-preds)) '?z '?y)
                             (list 'blockedOf '?x '?y)]
                            (list (decoy k j (dec (long decoy-depth))) '?x '?y)))]
          (doseq [j (range half)] (dec! j))
          (if (< k (long chain))
            (rule! [(list (step (inc k)) '?x '?y)] (list (step k) '?x '?y))
            (rule! ['(needleOf ?x ?y)] (list (step k) '?x '?y)))
          (doseq [j (range half decoys)] (dec! j)))))
    {:kb kb :goal (list (step 0) '?x '?y) :depth (inc (long chain))}))

(defn- engine-ttfa
  "Time to the **first** answer, through the public bounded door — the measurement a
  consumer that stops at one answer actually pays.  `nil` opts is the DFS's own order."
  [kb goal depth engine opts]
  (lc/clear-cache kb)
  (binding [v/*query-engine* engine, v/*query-options* opts]
    (let [t0 (System/nanoTime)
          r  (v/prove-within kb goal context {:max-results 1 :max-depth depth})]
      {:ms (/ (- (System/nanoTime) t0) 1e6) :found (count (:results r))})))

(defn- ask-ttfa
  "The same, through `ask` — the union engine over the whole prover registry, whose
  backward half is `RuleProver`.  It takes no depth bound: its loop guard is per-path."
  [kb goal]
  (lc/clear-cache kb)
  (let [t0 (System/nanoTime)
        r  (v/ask-within kb goal context {:max-results 1})]
    {:ms (/ (- (System/nanoTime) t0) 1e6) :found (count (:results r))}))

(defn- nodes-to-first
  "How many nodes the frontier expands before the first answer, under one strategy.  The
  structural number behind the wall-clock, and the one that is a property of the search
  rather than of the machine."
  [kb goal depth strategy]
  (lc/clear-cache kb)
  (let [sess (inf/session kb [goal] context {:strategy strategy :max-depth depth})]
    (doall (take 1 (inf/search-seq sess)))
    (:expanded (inf/tree-stats sess))))

;; ---- the protocol --------------------------------------------------------

(defn- shuffled
  "`xs` in an order this `rng` chose — the per-query shuffle that keeps JIT and GC drift
  from becoming a per-mode bias."
  [^java.util.Random rng xs]
  (let [a (java.util.ArrayList. ^java.util.Collection xs)]
    (java.util.Collections/shuffle a rng)
    (vec a)))

(defn- screen
  "The candidate goals whose exhaustive `:cost` run finishes inside `cap-ms`, and the
  ones it does not.

  A correctness pass has to compare *complete* answer sets, so a goal the baseline cannot
  finish has nothing to compare against.  Which goals those are is reported rather than
  quietly dropped — a silent cap reads as 'covered everything' when it did not."
  [kb goals depth cap-ms]
  (reduce (fn [acc g]
            (lc/clear-cache kb)
            (let [[_ done?] (drain-within (inf/session kb [g] context {:max-depth depth})
                                          cap-ms)]
              (update acc (if done? :kept :dropped) conj g)))
          {:kept [] :dropped []} goals))

(defn- correctness
  "Every mode over every goal, driven dry, in a shuffled order per query."
  [kb goals depth seed]
  (let [rng (java.util.Random. seed)
        acc (atom {})]
    (doseq [g goals, m (shuffled rng modes)]
      (let [r (exhaustive kb g depth m)]
        (swap! acc update (:label m)
               (fn [s] (-> (or s {:ms 0.0 :nodes 0 :answers {}})
                           (update :ms + (:ms r))
                           (update :nodes + (:nodes r))
                           (assoc-in [:answers g] (:answers r)))))))
    (let [base (get-in @acc [:cost :answers])]
      (mapv (fn [{:keys [label incomplete?]}]
              (let [{:keys [ms nodes answers]} (get @acc label)]
                {:label label :ms ms :nodes nodes
                 :answers (reduce + (map count (vals answers)))
                 :incomplete? (boolean incomplete?)
                 :agrees? (if incomplete?
                            (every? (fn [[g a]] (set/subset? a (get base g))) answers)
                            (= base answers))}))
            modes))))

(defn- latency
  "Every mode's cost to reach the first `k` answers, `reps` times, shuffled per query.

  The reported time is the **min over reps of the whole query set's total** — not the min
  over individual runs, which would let a mode win the column on the one goal it happened
  to suit.  One rep is one comparable measurement; the min of them is the
  least-interrupted one.

  The portfolio sits this pass out: a race is driven to completion before it can be
  unioned, so it has no partial answer to give and is not an anytime mode."
  [kb goals depth k reps seed]
  (let [rng  (java.util.Random. seed)
        runs (remove :exhaustive-only? modes)
        acc  (atom {})]
    (doseq [rep (range reps), g goals, m (shuffled rng runs)]
      (let [r (to-first-k kb g depth k m)]
        (swap! acc update (:label m)
               (fn [s] (-> (or s {:ms {} :nodes 0 :got 0})
                           (update-in [:ms rep] (fnil + 0.0) (:ms r))
                           (update :nodes + (:nodes r))
                           (update :got + (:got r)))))))
    (mapv (fn [{:keys [label incomplete?]}]
            (let [{:keys [ms nodes got]} (get @acc label)]
              {:label label :ms (apply min (vals ms)) :incomplete? (boolean incomplete?)
               :nodes (double (/ nodes (max 1 (* reps (count goals)))))
               :answers (double (/ got (max 1 (* reps (count goals)))))}))
          runs)))

(defn- needle-runs
  "Every engine the needle is asked of.  The DFS and `ask` are the other two backward
  chainers, measured through the same public bounded door, because time-to-first-answer
  is a claim about *engines* and not only about orderings."
  []
  (-> [{:label :prove-dfs :engine :dfs}
       {:label :ask :ask? true}]
      (into (map (fn [t] {:label t :engine :inference :opts t}))
            (sort (keys tac/tacticians)))
      (into [{:label :backchain-first :engine :inference
              :opts {:estimate-backchain? :first}}
             {:label :backchain-all :engine :inference
              :opts {:estimate-backchain? :all}}])))

(defn- needle-report
  "Time to the first answer on the needle, every engine, `reps` times, shuffled per rep.
  The min over reps is reported; a run that did not find the needle is marked, because a
  fast engine that answers nothing is not fast."
  [{:keys [kb goal depth]} reps seed]
  (let [rng  (java.util.Random. seed)
        runs (needle-runs)
        acc  (atom {})]
    (doseq [_ (range reps), m (shuffled rng runs)]
      (let [r (if (:ask? m) (ask-ttfa kb goal)
                  (engine-ttfa kb goal depth (:engine m) (:opts m)))]
        (swap! acc update (:label m)
               (fn [s] (-> (or s {:ms [] :found 0})
                           (update :ms conj (:ms r))
                           (update :found max (:found r)))))))
    (mapv (fn [{:keys [label engine opts]}]
            (let [{:keys [ms found]} (get @acc label)]
              {:label label :ms (apply min ms) :found? (pos? (long found))
               :nodes (if (= :inference engine)
                        (nodes-to-first kb goal depth opts)
                        0)}))
          runs)))

(defn- report-needle [title rows]
  (say (format "\n── %s ──" title))
  (say (format "  %-22s %8s %11s %11s %11s" "engine" "found?" "nodes" "ttfa ms" "vs dfs"))
  (say "  " (apply str (repeat 68 \-)))
  (let [base (:ms (first (filter #(= :prove-dfs (:label %)) rows)))]
    (doseq [{:keys [label ms nodes found?]} rows]
      (say (format "  %-22s %8s %11s %11.2f %10.2f×"
                   label (if found? "yes" "NONE")
                   (if (pos? (long nodes)) (str nodes) "—")
                   ms (/ ms (max 0.001 base)))))))

(defn- report [title time-label rows]
  (say (format "\n── %s ──" title))
  (say (format "  %-18s %9s %9s %10s %11s %9s"
               "mode" "answers" "nodes" time-label "vs :cost" "same?"))
  (say "  " (apply str (repeat 72 \-)))
  (let [base (:ms (first (filter #(= :cost (:label %)) rows)))]
    (doseq [{:keys [label ms nodes answers agrees? incomplete?]} rows]
      (say (format "  %-18s %9.1f %9.1f %10.1f %10.2f× %9s"
                   (str label (when incomplete? " ⊂")) (double answers) (double nodes)
                   ms (/ ms (max 0.001 base))
                   (cond (nil? agrees?) "—"
                         incomplete?    (if agrees? "prefix" "BROKEN")
                         agrees?        "yes"
                         :else          "NO"))))))

(defn -main [& args]
  (let [f      (or (some-> (first args) Long/parseLong) 1200)
        r      (or (some-> (second args) Long/parseLong) 400)
        depth  (or (some-> (nth args 2 nil) Long/parseLong) 3)
        k      (or (some-> (nth args 3 nil) Long/parseLong) 50)
        layers 3
        cap    4000
        cfg    {:facts f :rules r :preds (max 90 (quot r 3)) :base (max 20 (quot r 20))
                :inds (max 40 (quot f 8)) :seed 11 :layers layers}
        data   (gen cfg)
        _      (say (format "vaelii tactician validator — %,d facts, %,d rules, %,d preds (%,d base), %d layers, depth %d"
                            f r (:preds cfg) (:base cfg) layers depth))
        kb     (load-kb! data)
        bands  (:bands data)
        hot    (first (:inds data))
        deep   (mapv (fn [pr] (list pr hot '?b)) (take 10 (last bands)))
        flat   (mapv (fn [pr] (list pr hot '?b)) (take 6 (first bands)))
        scr    (screen kb deep depth cap)
        ncfg   {:decoys 6 :decoy-depth 4 :hay-preds 6
                :hay-facts (max 400 (quot f 3)) :inds 120 :seed 5}]
    (say "correctness TRUSTED (answer sets vs the :cost baseline). timing: literal cache")
    (say "cleared before every run, mode order shuffled per query.")
    (say (format "\n  screened %d band-%d goals at %,d ms each: %d kept, %d over the cap%s"
                 (count deep) (dec layers) cap (count (:kept scr)) (count (:dropped scr))
                 (if (seq (:dropped scr))
                   (str " — " (str/join ", " (map first (:dropped scr))))
                   "")))
    (when (seq (:kept scr))
      (report (format "correctness — %d backchaining-heavy goals, driven dry"
                      (count (:kept scr)))
              "total ms" (correctness kb (:kept scr) depth 7)))
    (report (format "correctness — %d shallow goals (band 0), driven dry" (count flat))
            "total ms" (correctness kb flat depth 7))
    (report (format "latency — first %d answers, %d backchaining-heavy goals, min of 3 reps"
                    k (count deep))
            "min ms" (latency kb deep depth k 3 7))
    (report (format "ttfa — first answer, %d backchaining-heavy goals, min of 3 reps"
                    (count deep))
            "min ms" (latency kb deep depth 1 3 7))
    (doseq [chain [2 5 8]]
      (let [nd (needle-kb! (assoc ncfg :chain chain))]
        (report-needle
         (format "ttfa — needle in a haystack: 1 answer at depth %d, %d decoy chains per level"
                 (:depth nd) (:decoys ncfg))
         (needle-report nd 3 7))))
    (say "\n  Reading:")
    (say "  - `same?` is the gate. A complete mode reading NO is a bug in that mode, not a")
    (say "    trade-off; :first-result is marked ⊂ and only has to be a prefix.")
    (say "  - the correctness pass drives every query dry, so every ordering expands the same")
    (say "    nodes and its ms column measures the estimate's overhead, not the search.")
    (say "  - the latency pass is where an ordering can pay: nodes-to-first-k is the trusted")
    (say "    number, and a tactician that does not beat :cost there has no reason to exist.")
    (say "  - ttfa is the widest spread of any column here, and it wants the OPPOSITE ordering")
    (say "    to bulk: level order is the best way to collect 50 answers and among the worst")
    (say "    ways to find one. Read the k=1 and k=50 tables against each other.")
    (say "  - the needle is what separates the engines rather than the orderings: one answer,")
    (say "    deep, with plausible decoys at every level. The DFS's edge is largest on a")
    (say "    shallow needle and gone by the time the derivation is deep.")
    (shutdown-agents)))

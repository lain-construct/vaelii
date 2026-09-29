;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.ref.gen
  "Random worlds inside the reference's v1 fragment, the loader that asserts a world into
  a fresh KB in a given order, the reader of the engine's belief per context, the
  comparators (engine against reference, engine against engine across orders), the
  divergence classifier, the shrinker and the failure report.

  A **world** is `{:contexts #{C ...} :writes [{:sentence S :context C :strength k} ...]}`
  (the belief reference design note).  An **order** is a vector holding each write of a
  world once, so an order stays meaningful after the shrinker drops a write: dropping it
  from every order is `filterv`.

  This namespace requires no reference namespace.  The caller passes the reference in
  `check-world`'s judges map as `:reference`, a function `world -> {C {:believed #{S}
  :out #{S} :inherited #{S} :nogoods [...]}}`.

  **The reference judges every write offered** (decision D8).  A write the engine refuses
  is not dropped from the reference's world: the run records the refusal as a divergence
  of kind `:engine-refused-clash`, `:engine-refused-mark` or `:engine-refused-other`
  (`refusal-kind`), and the belief differences of that run are reported under that
  divergence and never as belief disagreements.  Every belief disagreement of a run with
  no refusal is shrunk to a minimal world and given a `:kind` by `classify`.

  Every KB this namespace opens is an in-RAM KB on a space of its own
  (`[::ref n]`, `n` from a process counter), opened `{:constraints :arbitrate}` so a
  clash is stored and decided rather than refused.  `run-order` and every caller of it
  close the KB and drop both RAM stores in a `finally`; `load-world!` hands the open KB
  to its caller, who closes it with `close-kb!`."
  (:refer-clojure :exclude [compare])
  (:require [clojure.java.io :as io]
            [clojure.pprint :as pp]
            [clojure.set :as set]
            [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.impl.memory :as mem]
            [vaelii.test-util :as tu])
  (:import [java.util ArrayList Collections Random]))

;; ---- small helpers -----------------------------------------------------

(defn- pick [^Random rng coll]
  (let [v (vec coll)] (nth v (.nextInt rng (count v)))))

(defn- between
  "A uniform integer in `[lo hi]`, both ends included."
  [^Random rng [lo hi]]
  (+ lo (.nextInt rng (inc (- hi lo)))))

(defn- chance [^Random rng p] (< (.nextDouble rng) p))

(defn- weighted
  "One key of `table`, a seq of `[weight key]`, drawn in proportion to the weights."
  [^Random rng table]
  (let [total (reduce + (map first table))
        r     (.nextInt rng total)]
    (loop [[[w k] & more] table acc 0]
      (if (< r (+ acc (long w))) k (recur more (+ acc (long w)))))))

(defn- shuffled
  "`coll` shuffled by a `Random` seeded with `seed`: the same seed gives the same order."
  [seed coll]
  (let [al (ArrayList. ^java.util.Collection (vec coll))]
    (Collections/shuffle al (Random. (long seed)))
    (vec al)))

(defn permutations
  "Every ordering of the vector `xs`, as vectors, the given order first."
  [xs]
  (let [xs (vec xs)]
    (if (empty? xs)
      [[]]
      (vec (for [i    (range (count xs))
                 more (permutations (into (subvec xs 0 i) (subvec xs (inc i))))]
             (into [(nth xs i)] more))))))

(defn- symbols-in [form]
  (filter symbol? (tree-seq coll? seq form)))

(defn- variable? [x]
  (and (symbol? x) (str/starts-with? (name x) "?")))

(defn rule-sentence?
  "Is `s` a rule write: an `implies`, a `set/forwardRule` or an `exceptWhen` wrapping one?"
  [s]
  (and (seq? s) (contains? #{'implies 'exceptWhen 'set/forwardRule} (first s))))

(defn forward
  "`s` with its `implies` wrapped `set/forwardRule`, inside its `exceptWhen` when it has
  one; a sentence already wrapped, or not a rule, is returned as it is.  A bare `implies`
  is backward-only (docs/inference.md), so a world carries the wrapper and the reference
  and the engine read one shape."
  [s]
  (cond
    (and (seq? s) (= 'implies (first s)))    (list 'set/forwardRule s)
    (and (seq? s) (= 'exceptWhen (first s))) (list 'exceptWhen (second s) (forward (nth s 2)))
    :else s))

(defn- comparable-sentence?
  "Is `s` a sentence the comparators judge: a list with no variable, not a rule and not a
  meta-sentence naming a handle.  Rules are left out on both sides, since the engine
  stores a rule under canonical variable names and the reference is not required to list
  rules among what it believes."
  [s]
  (and (seq? s)
       (not (rule-sentence? s))
       (not-any? #(or (variable? %) (= 'sentexHandle %)) (symbols-in s))))

(defn world-contexts
  "Every context a world's writes name: each write's own context, and both contexts of
  each `(genlCx a b)` sentence."
  [writes]
  (into #{}
        (mapcat (fn [{:keys [sentence context]}]
                  (cons context
                        (when (and (seq? sentence) (= 'genlCx (first sentence)))
                          (rest sentence)))))
        writes))

(defn- functor-of
  "The functor of `s`, or of the sentence a denial `(not S)` wraps; nil for a non-list."
  [s]
  (when (seq? s)
    (if (= 'not (first s)) (functor-of (second s)) (first s))))

;; ---- the generator -----------------------------------------------------

(def drawn-monotonic
  "The roster functors the generator writes `:monotonic` itself, because the engine at
  HEAD stores a `:default` write of one as written (decision D11 is not yet in the
  engine).  The engine coerces the rest of `vaelii.ref.world/forced-monotonic`, so those
  take a random strength."
  '#{disjoint covering})

(def default-sizes
  "The v1 sizes from the design note, each an inclusive `[lo hi]` range.  `:writes`
  counts every write, rules included."
  {:contexts    [2 4]
   :types       [3 6]
   :individuals [2 4]
   :predicates  [2 3]
   :writes      [4 10]
   :rules       [0 2]})

(defn- letter [i] (char (+ (int \a) i)))

(defn- fresh-pools
  "The world's terms, each with a gensym tail from `tu/fresh-term`, so no two worlds and
  no two KBs share a term.  Types are bare lowercase (`tmptya17`), predicates bare
  lowercase used at arity 2, individuals CapitalCamel, contexts `CxTmp…`.  Each predicate
  carries a kind that fixes its argument shape:

  - `:plain` — two individuals; marks `irreflexive`, `anti_transitive`, `functional`,
    `functionalInArg`, `anti_symmetric`.  Two symbol fillers colliding under a mark are
    a merge only when both are `:monotonic` (decision D6), and `demote-merges` keeps the
    generator from writing that pair.
  - `:num` — two integers in 1..3; the same marks.  Two integers never merge.
  - `:type-arg` — a type then an individual; marks `(transitiveInArg P 1 genl)`."
  [rng sizes]
  {:contexts    (vec (for [i (range (between rng (:contexts sizes)))]
                       (tu/fresh-term :context (str "Cx" (str/upper-case (str (letter i)))))))
   :types       (vec (for [i (range (between rng (:types sizes)))]
                       (tu/fresh-term :type (str "ty" (letter i)))))
   :individuals (vec (for [i (range (between rng (:individuals sizes)))]
                       (tu/fresh-term :individual (str "Ind" (str/upper-case (str (letter i)))))))
   :predicates  (vec (for [i (range (between rng (:predicates sizes)))]
                       {:pred (tu/fresh-term :predicate (str "rel" (letter i)))
                        :kind (pick rng [:plain :num :type-arg])}))})

(defn- strength [rng] (if (chance rng 0.35) :monotonic :default))

(defn- type-pair
  "Two distinct types `[sub super]` with `sub` later in the pool than `super`, so every
  `genl` edge and every cover points to an earlier type and the forest has no cycle."
  [rng types]
  (let [i (inc (.nextInt ^Random rng (dec (count types))))
        j (.nextInt ^Random rng i)]
    [(nth types i) (nth types j)]))

(defn- filler
  "One argument for a tuple of predicate kind `kind` (`:plain` or `:num`)."
  [rng kind individuals]
  (if (= :num kind) (inc (.nextInt ^Random rng 3)) (pick rng individuals)))

(defn- tuple [rng {:keys [pred kind]} {:keys [types individuals]}]
  (case kind
    :plain    (list pred (pick rng individuals)
                    (if (chance rng 0.2) ::same (pick rng individuals)))
    :num      (list pred (filler rng kind individuals) (filler rng kind individuals))
    :type-arg (list pred (pick rng types) (pick rng individuals))))

(defn- fix-self
  "Replace the `::same` placeholder a `:plain` self tuple carries with its first argument."
  [t]
  (if (= ::same (last t)) (list (first t) (second t) (second t)) t))

(defn- declaration [rng {:keys [types predicates]}]
  (let [{:keys [pred kind]} (pick rng predicates)
        options (cond-> [:disjoint]
                  (>= (count types) 3)      (conj :covering)
                  (#{:plain :num} kind)     (into [:functional :functional-in-arg
                                                   :anti-symmetric :irreflexive
                                                   :anti-transitive])
                  (= :type-arg kind)        (conj :transitive-in-arg))]
    (case (pick rng options)
      :disjoint          (let [[a b] (type-pair rng types)]
                           (list* 'disjoint (sort [a b])))
      :covering          (let [whole-i (.nextInt ^Random rng (- (count types) 2))
                               parts   (->> (subvec types (inc whole-i)) (shuffled (.nextLong ^Random rng))
                                            (take 2) sort)]
                           (list* 'covering (nth types whole-i) parts))
      :irreflexive       (list 'irreflexive pred)
      :anti-transitive   (list 'anti_transitive pred)
      :functional        (list 'functional pred)
      :functional-in-arg (list 'functionalInArg pred (inc (.nextInt ^Random rng 2)))
      :anti-symmetric    (list 'anti_symmetric pred)
      :transitive-in-arg (list 'transitiveInArg pred 1 'genl))))

(defn- violation
  "A tuple a mark among the writes `acc` convicts, or nil when `acc` holds no
  `irreflexive` or `anti_symmetric` mark: a self tuple `(P a a)` under an `(irreflexive
  P)`, or under an `(anti_symmetric P)` the converse of a tuple of `P` in `acc` with two
  distinct arguments (a fresh pair of distinct arguments when `acc` holds none).  Both
  are nogoods under decision D7, so the generator writes them on purpose."
  [rng {:keys [individuals predicates]} acc]
  (let [kinds (into {} (map (juxt :pred :kind)) predicates)
        marks (vec (for [{s :sentence} acc
                         :when (and (seq? s) (#{'irreflexive 'anti_symmetric} (first s)))]
                     s))]
    (when (seq marks)
      (let [[m p] (pick rng marks)
            kind  (kinds p)
            arg   #(filler rng kind individuals)]
        (if (= 'irreflexive m)
          (let [a (arg)] (list p a a))
          (let [prior (vec (for [{s :sentence} acc
                                 :when (and (seq? s) (= p (first s)) (= 3 (count s))
                                            (not= (nth s 1) (nth s 2)))]
                             s))]
            (if (seq prior)
              (let [[_ a b] (pick rng prior)] (list p b a))
              (let [a (arg) b (first (remove #{a} (shuffled (.nextLong ^Random rng)
                                                            (repeatedly 6 arg))))]
                (when b (list p a b))))))))))

(defn- fact-write
  "One non-rule write drawn from the menu: a `genlCx` edge, a `genl` edge or its denial, a
  membership or its denial, a tuple or its denial, a declaration, or a `violation` of a
  mark among `acc`, the writes drawn before it.  A write whose functor is in
  `drawn-monotonic` is written `:monotonic`; any other write of
  `vaelii.ref.world/forced-monotonic` takes a random strength, since the reference and
  the engine both store it `:monotonic`.  The menu holds no denial of a
  `vaelii.ref.world/forced-monotonic` functor."
  [rng {:keys [contexts types individuals predicates] :as pools} acc]
  (let [ctx   #(pick rng contexts)
        kind  (weighted rng (cond-> [[2 :genl] [1 :genl-denial] [5 :member] [2 :member-denial]
                                     [3 :tuple] [1 :tuple-denial] [3 :declaration]]
                              (>= (count contexts) 2) (conj [2 :genl-cx])
                              (some #(#{'irreflexive 'anti_symmetric} (functor-of (:sentence %)))
                                    acc)
                              (conj [2 :violation])))
        write (fn [s c]
                ;; the strength is drawn first either way, so the seed's draws stay put
                (let [k (strength rng)]
                  {:sentence s :context c
                   :strength (if (contains? drawn-monotonic (functor-of s)) :monotonic k)}))]
    (case kind
      :genl-cx       (let [[sub super] (type-pair rng contexts)]
                       (write (list 'genlCx sub super) 'CxUniverse))
      :genl          (let [[sub super] (type-pair rng types)]
                       (write (list 'genl sub (if (chance rng 0.25) 'thing super)) (ctx)))
      :genl-denial   (let [[sub super] (type-pair rng types)]
                       (write (list 'not (list 'genl sub super)) (ctx)))
      :member        (write (list (pick rng types) (pick rng individuals)) (ctx))
      :member-denial (write (list 'not (list (pick rng types) (pick rng individuals))) (ctx))
      :tuple         (write (fix-self (tuple rng (pick rng predicates) pools)) (ctx))
      :tuple-denial  (write (list 'not (fix-self (tuple rng (pick rng predicates) pools))) (ctx))
      :declaration   (write (declaration rng pools) (ctx))
      :violation     (when-let [t (violation rng pools acc)] (write t (ctx))))))

(defn- merge-marks
  "`{P #{mark …}}` over the writes: `:functional`, `[:functional-in-arg n]` and
  `:anti-symmetric` for each such declaration of `P`, whatever its context."
  [writes]
  (reduce (fn [m {s :sentence}]
            (if-let [mk (when (seq? s)
                          (case (first s)
                            functional      :functional
                            functionalInArg [:functional-in-arg (nth s 2)]
                            anti_symmetric  :anti-symmetric
                            nil))]
              (update m (second s) (fnil conj #{}) mk)
              m))
          {} writes))

(defn- merge-pair?
  "Do the distinct binary tuples `t1` and `t2` collide with symbol fillers under a mark of
  `marks` (`merge-marks`): a pair two `:monotonic` members make a merge (decision D6)."
  [marks t1 t2]
  (and (not= t1 t2) (= (first t1) (first t2)) (= 3 (count t1) (count t2))
       (let [[_ a1 b1] t1 [_ a2 b2] t2]
         (some (fn [mk]
                 (cond
                   (= :functional mk)     (and (= a1 a2) (symbol? b1) (symbol? b2))
                   (= :anti-symmetric mk) (and (= a1 b2) (= b1 a2) (not= a1 b1)
                                               (symbol? a1) (symbol? b1))
                   :else (let [n (second mk)
                               [v1 v2 o1 o2] (if (= 1 n) [a1 a2 b1 b2] [b1 b2 a1 a2])]
                           (and (= o1 o2) (symbol? v1) (symbol? v2)))))
               (get marks (first t1))))))

(defn- demote-merges
  "`writes` with every `:monotonic` tuple that is a `merge-pair?` with an earlier
  `:monotonic` tuple set to `:default`, so no two `:monotonic` symbol-filler tuples
  collide under one mark (decision D6: equality is outside v1).  One member of such a
  pair stays `:monotonic`."
  [writes]
  (let [marks (merge-marks writes)]
    (first
     (reduce (fn [[acc kept] {s :sentence k :strength :as w}]
               (cond
                 (not (and (= :monotonic k) (seq? s) (contains? marks (first s))))
                 [(conj acc w) kept]
                 (some #(merge-pair? marks s %) kept) [(conj acc (assoc w :strength :default)) kept]
                 :else                               [(conj acc w) (conj kept s)]))
             [[] []] writes))))

(defn- up-closure
  "`start` plus every type reachable from it over `edges`, a map sub -> #{super}."
  [edges start]
  (loop [seen (set start) todo (vec start)]
    (if-let [t (peek todo)]
      (let [new (remove seen (get edges t))]
        (recur (into seen new) (into (pop todo) new)))
      seen)))

(defn- type-edges
  "sub -> #{super} over every `genl` write and every cover's part -> whole, whatever the
  context or strength: the widest graph a derivation of a membership can follow."
  [writes]
  (reduce (fn [m {s :sentence}]
            (cond
              (and (seq? s) (= 'genl (first s)))
              (update m (nth s 1) (fnil conj #{}) (nth s 2))
              (and (seq? s) (= 'covering (first s)))
              (reduce #(update %1 %2 (fnil conj #{}) (second s)) m (drop 2 s))
              :else m))
          {} writes))

(defn- rule-writes
  "`n` rules over the pools, stratified.  Each rule concludes a membership `(tb ?x)`; a
  body is `(ta ?x)`, or `(and (ta ?x) (P ?x ?y))` over a `:plain` predicate concluding
  `(tb ?y)`, or `(and (ta ?x) (unknown (tu ?x)))`, or the rule is wrapped
  `(exceptWhen (tu ?x) …)`.  `tu` is never a type a rule concludes, a supertype of one
  over `type-edges`, or a type a cover names, so no rule reads the absence of what a
  rule derives; with no such type left the rule takes the plain body."
  [rng {:keys [contexts types predicates]} facts n]
  (let [conclusions (vec (repeatedly n #(pick rng types)))
        edges       (type-edges facts)
        covered     (into #{} (comp (map :sentence)
                                    (filter #(and (seq? %) (= 'covering (first %))))
                                    (mapcat rest))
                          facts)
        blocked     (into (up-closure edges conclusions) covered)
        plain       (filterv #(= :plain (:kind %)) predicates)]
    (vec (for [tb conclusions
               :let [ta    (pick rng (remove #{tb} types))
                     free  (remove (conj blocked ta) types)
                     shape (weighted rng (cond-> [[2 :simple]]
                                           (seq plain) (conj [2 :join])
                                           (seq free)  (into [[3 :unknown] [2 :except]])))
                     tu    (when (seq free) (pick rng free))]]
           {:sentence (forward
                       (case shape
                         :simple  (list 'implies (list ta '?x) (list tb '?x))
                         :join    (list 'implies
                                        (list 'and (list ta '?x) (list (:pred (pick rng plain)) '?x '?y))
                                        (list tb '?y))
                         :unknown (list 'implies
                                        (list 'and (list ta '?x) (list 'unknown (list tu '?x)))
                                        (list tb '?x))
                         :except  (list 'exceptWhen (list tu '?x)
                                        (list 'implies (list ta '?x) (list tb '?x)))))
            :context  (pick rng contexts)
            :strength (strength rng)}))))

(defn- guarded-parts
  "`[ta tb tu]` of a guarded rule sentence of `rule-writes`' shapes: `(and (ta ?x)
  (unknown (tu ?x)))` or `(exceptWhen (tu ?x) …)` over `(ta ?x)`, concluding `(tb ?x)`.
  Nil for an unguarded rule."
  [s]
  (if (= 'exceptWhen (first s))
    (let [[_ [tu] [_ [_ [ta] [tb]]]] s] [ta tb tu])
    (let [[_ [_ ante [tb]]] s]
      (when (and (seq? ante) (= 'and (first ante)) (seq? (nth ante 2))
                 (= 'unknown (first (nth ante 2))))
        (let [[_ [ta] [_ [tu]]] ante] [ta tb tu])))))

(defn- guarded-clash
  "The writes that put a guarded rule's conclusion into a clash with a `:default` member
  (decision D14), or nil when `rules` holds no guarded rule.  For the first guarded rule
  `(ta ?x) ⇒ (tb ?x)`, placed in `k`, and an individual `I`: a `:monotonic` `(ta I)` in
  `k`, and either a `:default` `(not (tb I))` in `k` or a `:monotonic` `(disjoint tb tc)`
  and a `:default` `(tc I)` in `k`, `tc` a type that is neither `ta`, the guard's type,
  nor above or below `tb` over `type-edges`.  The engine confers the conclusion
  `:monotonic` and takes the `:default` member OUT; the reference confers it `:default`
  and reads a dilemma."
  [rng {:keys [types individuals]} facts rules]
  (when-let [[k [ta tb tu]] (first (keep #(when-let [p (guarded-parts (:sentence %))]
                                            [(:context %) p])
                                         rules))]
    (let [ind    (pick rng individuals)
          edges  (type-edges facts)
          apart  (remove (fn [t] (or (contains? #{ta tb tu} t)
                                     (contains? (up-closure edges [tb]) t)
                                     (contains? (up-closure edges [t]) tb)))
                         types)
          member {:sentence (list ta ind) :context k :strength :monotonic}]
      (if (and (seq apart) (chance rng 0.5))
        (let [tc (pick rng apart)]
          [member
           {:sentence (list* 'disjoint (sort [tb tc])) :context k :strength :monotonic}
           {:sentence (list tc ind) :context k :strength :default}])
        [member {:sentence (list 'not (list tb ind)) :context k :strength :default}]))))

(defn gen-world
  "A random world for `seed`, inside the v1 fragment.  The same seed gives the same
  structure; every term carries a fresh gensym tail, so two calls never share a term.
  `opts` may override any range of `default-sizes`.

  Contexts form a `genlCx` DAG (an edge always points to an earlier context, stored in
  `CxUniverse`); types form a `genl` forest under `thing` the same way; the writes are
  drawn from `fact-write`'s menu without repeating a `[sentence context]` pair; 0–2
  rules come from `rule-writes`; half the worlds holding a guarded rule add the writes of
  `guarded-clash`, less any `[sentence context]` pair already drawn.  Every write of
  `vaelii.ref.world/forced-monotonic` is stored `:monotonic` and none is denied;
  `demote-merges` leaves no two `:monotonic` symbol-filler tuples colliding under one
  mark.  `:contexts` holds every generated context plus `CxUniverse` when an edge names
  it."
  [seed opts]
  (let [rng    (Random. (long seed))
        sizes  (merge default-sizes opts)
        pools  (fresh-pools rng sizes)
        total  (between rng (:writes sizes))
        nrules (min (between rng (:rules sizes)) (max 0 (- total 2)))
        facts  (loop [acc [] seen #{} guard 0]
                 (if (or (= (count acc) (- total nrules)) (> guard 200))
                   acc
                   (let [w (fact-write rng pools acc)
                         k [(:sentence w) (:context w)]]
                     (if (or (nil? w) (seen k))
                       (recur acc seen (inc guard))
                       (recur (conj acc w) (conj seen k) (inc guard))))))
        facts  (demote-merges facts)
        rules  (rule-writes rng pools facts nrules)
        clash  (when (chance rng 0.5) (guarded-clash rng pools facts rules))
        seen   (into #{} (map (juxt :sentence :context)) facts)
        writes (-> facts
                   (into (remove #(seen [(:sentence %) (:context %)])) clash)
                   (into rules))]
    {:contexts (into (set (:contexts pools)) (world-contexts writes))
     :writes   writes}))

;; ---- orders ------------------------------------------------------------

(defn orders-for
  "The orders a check runs `world` in: every permutation of its writes when there are at
  most `:exhaustive-up-to` of them, else `:sample` orders — the writes as generated, their
  reverse, and seeded shuffles (`:seed`) of the rest, without repeats."
  [world {:keys [exhaustive-up-to sample seed] :or {exhaustive-up-to 6 sample 8 seed 0}}]
  (let [ws (vec (:writes world))]
    (if (<= (count ws) exhaustive-up-to)
      (permutations ws)
      (->> (concat [ws (vec (rseq ws))]
                   (map #(shuffled (+ (* 1000 seed) %) ws) (range (* 4 sample))))
           distinct
           (take sample)
           vec))))

;; ---- the engine side ---------------------------------------------------

(defonce ^:private space-counter (atom 0))

(defn engine-form
  "The sentence `assert` receives for a world write.  A bare `implies` is backward-only
  (docs/inference.md), so a rule is wrapped `set/forwardRule`, inside its `exceptWhen`
  when it has one; every other write is asserted as written."
  [s]
  (forward s))

(defn close-kb!
  "Close the KB `load-world!` returned and drop the RAM stores its space held."
  [{:keys [kb space]}]
  (try (some-> kb v/close!)
       (finally
         (when space
           (mem/drop-record-space! space)
           (mem/drop-index-space! space)))))

(defn load-world!
  "A fresh KB on a space of its own, opened `{:constraints :arbitrate}` merged with
  `opts`, with the writes of `order` (a vector of the world's writes) asserted in that
  order.  A write `assert` refuses with an `ex-info` is recorded as
  `{:refused write :type (:type ex-data) :message …}` and loading goes on; any other
  throwable closes the KB and propagates.

  Returns `{:kb kb :space space :refused [...]}`; the caller closes it with `close-kb!`.
  Decision D15 removes the `:constraints` option; the loader passes it until the engine
  drops it."
  [_world order opts]
  (let [space [::ref (swap! space-counter inc)]
        kb    (v/open-kb (merge {:backend :memory :space space :recover? false
                                 :constraints :arbitrate}
                                opts))]
    (try
      {:kb      kb
       :space   space
       :refused (into []
                      (keep (fn [{:keys [sentence context strength] :as w}]
                              (try (v/assert kb (engine-form sentence) context
                                             {:strength (or strength :default)})
                                   nil
                                   (catch clojure.lang.ExceptionInfo e
                                     {:refused w
                                      :type    (:type (ex-data e) :untyped)
                                      :message (ex-message e)}))))
                      order)}
      (catch Throwable t
        (close-kb! {:kb kb :space space})
        (throw t)))))

(defn engine-beliefs
  "`{C #{sentence}}` for every context `C` of `world`: the sentences the engine believes
  at `C`, read one sentence at a time (decision D5).

  - A stored literal sentence is read by `believed?` at `C` on its handle, when the
    handle's context is seen from `C` (`believed?` does not test visibility,
    docs/api.md).  Rules, variables and handle-naming meta-sentences are left out
    (`comparable-sentence?`).
  - A sentence of `asks` `{C #{S}}` that no handle seen from `C` stores is read by
    `ask?` at `C`: an inherited claim, which the engine answers and never stores.

  A sentence neither stored nor asked is absent here, which reads as OUT."
  ([kb world] (engine-beliefs kb world {}))
  ([kb world asks]
   (let [stored (into []
                      (keep (fn [h]
                              (let [sx (v/sentex kb h)]
                                (when (and sx (nil? (:antecedent sx)))
                                  (let [s (v/sentence-of sx)]
                                    (when (comparable-sentence? s)
                                      [h s (:context sx)]))))))
                      (v/handles kb))]
     (into {}
           (for [c (:contexts world)
                 :let [seen (filterv (fn [[_ _ ctx]] (or (nil? ctx) (v/sees? kb c ctx))) stored)
                       held (into #{} (keep (fn [[h s _]] (when (v/believed? kb h c) s))) seen)
                       kept (into #{} (map second) seen)]]
             [c (into held
                      (filter #(and (not (kept %)) (v/ask? kb % c)))
                      (sort-by pr-str (get asks c)))])))))

(defn run-order
  "Load `world` in `order`, read `engine-beliefs` (asking the sentences of `asks`,
  `{C #{S}}`, through `ask?`), and close the KB.
  Returns `{:order order :refused [...] :beliefs {C #{S}}}`."
  ([world order opts] (run-order world order opts {}))
  ([world order opts asks]
   (let [loaded (load-world! world order opts)]
     (try
       {:order   order
        :refused (:refused loaded)
        :beliefs (engine-beliefs (:kb loaded) world asks)}
       (finally (close-kb! loaded))))))

;; ---- reading the reference ---------------------------------------------

(defn- inherited-at
  "The inherited claims the reference result `ref-c` (one context's map) derives, which
  the engine answers through `ask?` (decision D5)."
  [ref-c]
  ;; `believe`'s per-context map carries `:inherited #{S}`; before it
  ;; lands the key is absent and this is empty
  (set (:inherited ref-c)))

(defn- merge-at?
  "Does the reference hold a `:merge` verdict at this context (decision D6): an
  all-monotonic symbol-filler functional or anti-symmetric pair, whose belief comparison
  is skipped and counted."
  [ref-c]
  ;; `decide` gives such a nogood the verdict :merge; before it lands no
  ;; nogood carries it and nothing is skipped
  (boolean (some #(= :merge (:verdict %)) (:nogoods ref-c))))

(defn- ref-in? [ref-c s]
  (or (contains? (set (:believed ref-c)) s) (contains? (inherited-at ref-c) s)))

;; ---- comparison --------------------------------------------------------

(defn compare
  "Every disagreement between the reference and the engine, as
  `[{:context C :sentence S :engine bool :reference bool}]`, sorted by context and
  sentence.  For each context of `world` outside `skip` the sentences judged are the
  reference's believed, inherited and OUT sentences and the engine's believed ones
  (`comparable-sentence?` filters all four); a sentence is IN for the reference when it
  is believed or inherited."
  ([world ref-result engine-result] (compare world ref-result engine-result #{}))
  ([world ref-result engine-result skip]
   (vec (for [c (sort-by str (:contexts world))
              :when (not (contains? skip c))
              :let [ref-c    (get ref-result c)
                    eb       (get engine-result c #{})
                    universe (filter comparable-sentence?
                                     (set/union (set (:believed ref-c)) (set (:out ref-c))
                                                (inherited-at ref-c) (set eb)))]
              s (sort-by pr-str universe)
              :let [r (ref-in? ref-c s)
                    e (contains? eb s)]
              :when (not= r e)]
          {:context c :sentence s :engine e :reference r}))))

(defn- refused-set [run] (into #{} (map :refused) (:refused run)))

(defn- run-disagreements
  "The belief disagreements between two runs of one world, each naming both orders."
  [world a b]
  (vec (for [c (sort-by str (:contexts world))
             :let [ba (get (:beliefs a) c #{}) bb (get (:beliefs b) c #{})]
             s (sort-by pr-str (set/union ba bb))
             :let [x (contains? ba s) y (contains? bb s)]
             :when (not= x y)]
         {:context c :sentence s :order-a (:order a) :order-b (:order b) :a x :b y})))

(defn order-disagreements
  "Engine-against-engine over `runs` of one world.  Runs are grouped by the set of writes
  the engine refused, since two runs that stored different content may believe
  differently; within a group each run is compared with the group's first."
  [world runs]
  (vec (for [[_ group] (sort-by (comp count key) (group-by refused-set runs))
             b         (rest group)
             d         (run-disagreements world (first group) b)]
         d)))

;; ---- refusals ----------------------------------------------------------

(def clash-refusal-types
  "The `:type`s of an entry-point refusal that reads other stored content and convicts a
  clash (docs/naming.md's roster of `assert`'s refusals).  Decision D8 stores such a
  clash instead."
  #{:disjoint :functional :cover :asymmetric :anti-transitive})

(def mark-refusal-types
  "The `:type`s of an entry-point refusal of an `irreflexive` or `anti_symmetric`
  violation.  Decision D7 makes each a nogood instead."
  #{:irreflexive :anti-symmetric})

(defn refusal-kind
  "The divergence kind of an engine refusal `{:refused w :type t …}`:
  `:engine-refused-clash` for a type in `clash-refusal-types`, `:engine-refused-mark`
  for one in `mark-refusal-types`, `:engine-refused-genl-related` for a `disjoint` or
  `covering` write refused as `:not-well-formed` (the entry point reads the stored genl
  and disjoint content to refuse a declaration over related types; a generated
  declaration is well formed on its own, so the refusal read other content, which
  decision D8 makes a stored hard clash), and `:engine-refused-other` for anything
  else.  The reference judges every write offered (decision D8), so every refusal of a
  generated write is a divergence."
  [{:keys [type refused]}]
  (let [f (let [s (:sentence refused)] (when (seq? s) (first s)))]
    (cond (contains? clash-refusal-types type) :engine-refused-clash
          (contains? mark-refusal-types type)  :engine-refused-mark
          (and (= :not-well-formed type)
               (contains? #{'disjoint 'covering} f)) :engine-refused-genl-related
          :else                                :engine-refused-other)))

;; ---- the check ---------------------------------------------------------

(defn check-world
  "Run `world` in every order of `orders` and judge it against the reference over the
  writes offered (decision D8).  Returns

    {:refusals    [{:kind k :refusal w :type t :message m :order o
                    :beliefs [disagreement …]} …]   ; one per refusal per run; :beliefs
                                                     ; holds that run's belief differences
     :reference   [disagreement …]  ; engine against reference in the runs that refused
                                    ; nothing, each with the :order it was read in
     :orders      [disagreement …]  ; `order-disagreements`
     :merge-skips #{C …}            ; contexts skipped for a :merge verdict (D6)
     :refused     [{:refused w :type t :message m} …]  ; every refusal, distinct
     :store-split bool              ; did two orders store different content
     :runs        n}

  `judges` is a map.  `:reference` is `world -> {C {:believed :out :inherited
  :nogoods}}`, called once on the whole world.  `:kb-opts` is merged into each KB's
  `open-kb` options.  An inherited claim of the reference at `C` is read from the engine
  through `ask?` at `C`."
  [world orders {:keys [reference kb-opts]}]
  (let [ref    (reference world)
        asks   (into {} (for [[c ref-c] ref :let [i (inherited-at ref-c)] :when (seq i)] [c i]))
        skip   (into #{} (keep (fn [[c ref-c]] (when (merge-at? ref-c) c))) ref)
        runs   (mapv #(run-order world % kb-opts asks) orders)
        judged (mapv (fn [r] [r (compare world ref (:beliefs r) skip)]) runs)]
    {:refusals    (vec (for [[r ds] judged
                             rf     (:refused r)]
                         (assoc rf :kind (refusal-kind rf) :order (:order r) :beliefs ds)))
     :reference   (vec (for [[r ds] judged
                             :when (empty? (:refused r))
                             d ds]
                         (assoc d :order (:order r))))
     :orders      (order-disagreements world runs)
     :merge-skips skip
     :refused     (vec (distinct (mapcat :refused runs)))
     :store-split (< 1 (count (distinct (map refused-set runs))))
     :runs        (count runs)}))

;; ---- shape readers for the classifier ------------------------------------

(defn- context-up
  "`c` plus every context it sees over the `genlCx` writes of `writes` (every such write
  counts: decision D1 makes each one monotonic and undeniable)."
  [writes c]
  (let [adj (reduce (fn [m {[f a b] :sentence}]
                      (if (= 'genlCx f) (update m a (fnil conj #{}) b) m))
                    {} (filter #(seq? (:sentence %)) writes))]
    (up-closure adj [c])))

(defn- conjuncts
  "The literals of an antecedent or exception form: an `(and …)`'s arguments, a
  vector's elements, or the form alone."
  [form]
  (cond (vector? form)                            (vec form)
        (and (seq? form) (= 'and (first form)))  (vec (rest form))
        :else                                    [form]))

(defn- rule-shape
  "`{:consequent C :antecedents [literal …] :guards [[literal …] …]}` for a rule sentence
  of the generator's shapes: the join antecedents, and one guard per `(unknown X)`
  antecedent and per `exceptWhen` exception, a set of conjuncts whose holding blocks the
  firing.  Nil for a sentence that is not a rule."
  [s]
  (when (rule-sentence? s)
    (let [[exc body] (if (= 'exceptWhen (first s)) [(second s) (nth s 2)] [nil s])
          body       (if (= 'set/forwardRule (first body)) (second body) body)
          [_ ante c] body
          lits       (conjuncts ante)]
      {:consequent  c
       :antecedents (vec (remove #(and (seq? %) (= 'unknown (first %))) lits))
       :guards      (cond-> (vec (for [l lits :when (and (seq? l) (= 'unknown (first l)))]
                                   (conjuncts (second l))))
                      exc (conj (conjuncts exc)))})))

(defn- bind
  "The bindings under which the pattern `p` equals the ground sentence `s`, or nil."
  [p s]
  (when (and (seq? p) (seq? s) (= (count p) (count s)))
    (reduce (fn [b [x y]]
              (cond (and (variable? x) (contains? b x)) (if (= (b x) y) b (reduced nil))
                    (variable? x)                        (assoc b x y)
                    (and (seq? x) (seq? y))              (if-let [b' (bind x y)]
                                                           (merge b b')
                                                           (reduced nil))
                    (= x y)                              b
                    :else                                (reduced nil)))
            {} (map vector p s))))

(defn- substitute [form b]
  (cond (variable? form) (get b form form)
        (seq? form)      (apply list (map #(substitute % b) form))
        (vector? form)   (mapv #(substitute % b) form)
        :else            form))

(defn- guarded-firings
  "`[[rule-write guard-instances] …]`: for each guarded rule of `world` visible at `c`
  whose consequent matches `s`, each guard instantiated under that match."
  [world c s]
  (let [up (context-up (:writes world) c)]
    (for [{r :sentence k :context :as w} (:writes world)
          :let [{:keys [consequent guards]} (rule-shape r)]
          :when (and (seq guards) (contains? up k))
          :let [b (bind consequent s)]
          :when b
          g guards]
      [w (mapv #(substitute % b) g)])))

(defn- ground-sentence?
  "Is `s` a `genl` edge or a declaration: something a clash is read through."
  [s]
  (and (seq? s) (or (= 'genl (first s))
                    (contains? '#{disjoint covering functional functionalInArg irreflexive
                                  anti_symmetric asymmetric anti_transitive transitiveInArg}
                               (first s)))))

;; ---- classification ----------------------------------------------------

(defn- exit-gate?
  "Prompt 29: the engine disbelieves `s` at `c` where the reference believes it; `s` is
  the conclusion of a guarded rule visible at `c`; one guard instance is OUT at `c` in
  the reference, defeated by a nogood that is not a negation pair (a cross-functor
  defeat, which queues none of the loser's watchers)."
  [world ref {:keys [context sentence engine reference]}]
  (let [ref-c (get ref context)]
    (and reference (not engine)
         (boolean
          (some (fn [[_ g]]
                  (some (fn [b]
                          (and (contains? (set (:out ref-c)) b)
                               (some #(and (= :defeat (:verdict %)) (= b (:loser %))
                                           (not= :negation (:kind %)))
                                     (:nogoods ref-c))))
                        g))
                (guarded-firings world context sentence))))))

(defn- joint-view?
  "Prompt 31: the engine believes `s` at `c` where the reference takes it OUT there; a
  `genlCx` edge `(genlCx H K)` with `H` a strict ancestor of `c` widens `c`'s view (`c`
  sees strictly less without it), and in the disagreement's order the edge arrives
  after `s` when `s` is itself a write."
  [world ref {:keys [context sentence engine reference order]}]
  (let [ws  (:writes world)
        up  (context-up ws context)
        pos (fn [s] (first (keep-indexed (fn [i w] (when (= s (:sentence w)) i)) order)))]
    (and engine (not reference)
         (contains? (set (:out (get ref context))) sentence)
         (boolean
          (some (fn [{[f h] :sentence :as e}]
                  (and (= 'genlCx f) (not= h context) (contains? up h)
                       (< (count (context-up (filterv #(not= e %) ws) context)) (count up))
                       (let [pe (pos (:sentence e)) ps (pos sentence)]
                         (or (nil? ps) (and pe (> pe ps))))))
                (filter #(seq? (:sentence %)) ws))))))

(defn- verdict-bound-below-vantage?
  "Decision D3: the engine disbelieves `s` at `c` where the reference believes it, and a
  strict ancestor `V` of `c` takes `s` OUT in the reference: `c` reads a denial or an
  edge that dissolves the clash `V` decides, and the engine keeps `V`'s verdict at `c`."
  [world ref {:keys [context sentence engine reference]}]
  (and reference (not engine)
       (boolean (some #(and (not= context %) (contains? (set (:out (get ref %))) sentence))
                      (context-up (:writes world) context)))))

(defn- pass-count?
  "Prompt 30: the engine disbelieves `s` at `c` where the reference believes it; the
  reference at `c` takes a ground (a `genl` edge or a declaration) OUT, which releases a
  clash there; and the world holds a guarded rule, whose blocker makes a settle run a
  second pass."
  [world ref {:keys [context engine reference]}]
  (and reference (not engine)
       (boolean (some ground-sentence? (:out (get ref context))))
       (boolean (some #(seq (:guards (rule-shape (:sentence %)))) (:writes world)))))

(defn- exception-not-reasked?
  "Decision D4: the engine believes `s` at `c` where the reference does not; `s` is the
  conclusion of a guarded rule visible at `c`, every conjunct of one guard instance is
  believed at `c` in the reference, and a strict ancestor of `c` believes `s` in the
  reference: the blocking fact is visible at the reader and not at the placement."
  [world ref {:keys [context sentence engine reference]}]
  (let [ref-c (get ref context)]
    (and engine (not reference)
         (boolean (some (fn [[_ g]] (every? #(contains? (set (:believed ref-c)) %) g))
                        (guarded-firings world context sentence)))
         (boolean (some #(and (not= context %) (ref-in? (get ref %) sentence))
                        (context-up (:writes world) context))))))

(defn- late-mark-reported?
  "Decision D7: the engine believes `s` at `c` where the reference takes it OUT as the
  loser of an `irreflexive` or `anti_symmetric` nogood: the mark arrived after the
  tuple, and the engine files a report and leaves the tuple believed instead of
  deciding the nogood."
  [_world ref {:keys [context sentence engine reference]}]
  (and engine (not reference)
       (boolean (some #(and (contains? #{:irreflexive :anti-symmetric} (:kind %))
                            (= sentence (:loser %)))
                      (:nogoods (get ref context))))))

(defn- naf-conclusion-monotonic?
  "Decision D14: the engine and the reference disagree on `s` at `c`; `s` is a member of a
  nogood the reference decides at `c` that also holds the conclusion `m` of a guarded
  rule visible at `c`, decided as a dilemma or with `m` the loser; and the rule's join
  antecedents under the binding that concludes `m` are `:monotonic` writes seen from `c`.
  The engine confers `m` `:monotonic` there, where the reference caps a guarded firing
  at `:default`."
  [world ref {:keys [context sentence]}]
  (let [ws    (:writes world)
        up    (context-up ws context)
        mono  (into #{} (keep (fn [{s :sentence k :context st :strength}]
                                (when (and (= :monotonic st) (contains? up k)) s)))
                    ws)
        mono? (fn [m]
                (some (fn [{r :sentence k :context}]
                        (let [{:keys [consequent antecedents guards]} (rule-shape r)
                              b (when (and (seq guards) (contains? up k)) (bind consequent m))]
                          (and b (every? #(contains? mono (substitute % b)) antecedents))))
                      ws))]
    (boolean
     (some (fn [{:keys [members verdict loser]}]
             (and (contains? members sentence)
                  (some #(and (mono? %) (or (= :dilemma verdict) (= % loser))) members)))
           (:nogoods (get ref context))))))

(def classifiers
  "The belief-disagreement shapes, as `[kind predicate]` in the order `classify` tries
  them.  Each predicate reads the minimal world, the reference's result on it and the
  disagreement `{:context :sentence :engine :reference :order}`."
  [[:late-mark-reported                     late-mark-reported?]
   [:naf-conclusion-monotonic               naf-conclusion-monotonic?]
   [:exit-gate                              exit-gate?]
   [:joint-view                             joint-view?]
   [:verdict-bound-below-vantage            verdict-bound-below-vantage?]
   [:pass-count                             pass-count?]
   [:exception-not-reasked-below-placement exception-not-reasked?]])

(defn classify
  "The `:kind` of the belief disagreement `d` read in the minimal world `world`, whose
  reference result is `ref`: the first kind of `classifiers` whose shape matches, else
  `:unclassified`.  Best-effort: a shape names the mechanism a known engine defect
  follows, read off the world's content, and cannot prove the engine followed it."
  [world ref d]
  (or (some (fn [[k pred]] (when (pred world ref d) k)) classifiers)
      :unclassified))

;; ---- shrinking ---------------------------------------------------------

(defn- drop-write [world w]
  (update world :writes #(filterv (partial not= w) %)))

(defn- drop-context
  "`world` without context `c`: the writes stored in `c` or naming it leave with it."
  [world c]
  (-> world
      (update :contexts disj c)
      (update :writes (fn [ws] (filterv #(and (not= c (:context %))
                                              (not (some #{c} (symbols-in (:sentence %)))))
                                        ws)))))

(defn shrink
  "The smallest world `failing?` still fails on, reached by dropping writes one at a time
  while the failure persists, then dropping contexts (with the writes that name them)
  the same way.  `failing?` is `world -> failure-or-nil` (`failing-under`).  Returns
  `{:world minimal :failure (failing? minimal)}`; when `world` itself passes, `:failure`
  is nil and `:world` is `world`."
  [world failing?]
  (if-let [f (failing? world)]
    (let [[w1 f1] (loop [w world f f]
                    (if-let [[w' f'] (first (keep (fn [x]
                                                    (let [c (drop-write w x)]
                                                      (when-let [f' (failing? c)] [c f'])))
                                                  (:writes w)))]
                      (recur w' f')
                      [w f]))
          [w2 f2] (loop [w w1 f f1]
                    (if-let [[w' f'] (first (keep (fn [c]
                                                    (let [cand (drop-context w c)]
                                                      (when-let [f' (failing? cand)] [cand f'])))
                                                  (sort-by str (:contexts w))))]
                      (recur w' f')
                      [w f]))]
      {:world w2 :failure f2})
    {:world world :failure nil}))

(defn failing-under
  "A `failing?` for `shrink` that holds one belief disagreement `target` (`{:context
  :sentence :engine}`) fixed: re-run a candidate world in `orders` projected onto its
  writes, judged by `judges` (`check-world`'s third argument), and answer the candidate's
  reference disagreement on the same context, sentence and engine answer, or nil.  A
  candidate the reference refuses as outside the fragment passes."
  [judges orders {:keys [context sentence engine]}]
  (fn [world]
    (let [keep?  (set (:writes world))
          orders (vec (distinct (map #(filterv keep? %) orders)))]
      (try
        (first (filter #(and (= context (:context %)) (= sentence (:sentence %))
                             (= engine (:engine %)))
                       (:reference (check-world world orders judges))))
        (catch clojure.lang.ExceptionInfo e
          (when-not (= :unsupported (:type (ex-data e))) (throw e)))))))

;; ---- divergences -------------------------------------------------------

(defn divergences
  "Every divergence `check` (`check-world`'s result on `world`) holds, each with a
  `:kind`, deduplicated:

  - one per refused write, `{:kind (refusal-kind …) :category :refusal :refusal w :type t
    :message m :runs n :belief-differences n}`, the belief differences summed over the
    runs that refused it;
  - one per `[context sentence engine-answer]` of the reference disagreements,
    `{:kind k :category :reference :context :sentence :engine :reference :orders [o …]
    :world minimal :minimal d}`: the world shrunk while that disagreement persists
    (`shrink`, `failing-under` over at most two of the orders it was read in), and `k`
    from `classify` on the minimal world;
  - one per engine-against-engine disagreement no divergence above accounts for (none
    is expected: a disagreement between two runs that refused nothing is a reference
    disagreement of one of them, and one between two runs that refused the same writes
    is reported under those refusals), `{:kind :unclassified :category :orders …}`."
  [world check judges]
  (let [refusals (for [[[w k] rs] (group-by (juxt :refused :kind) (:refusals check))]
                   {:kind               k
                    :category           :refusal
                    :refusal            w
                    :type               (:type (first rs))
                    :message            (:message (first rs))
                    :runs               (count rs)
                    :belief-differences (reduce + (map (comp count :beliefs) rs))})
        refs     (for [[[c s e] ds] (group-by (juxt :context :sentence :engine) (:reference check))
                       :let [orders (vec (take 2 (distinct (map :order ds))))
                             {mw :world mf :failure}
                             (shrink world (failing-under judges orders
                                                          {:context c :sentence s :engine e}))
                             mf     (or mf (first ds))
                             kind   (classify mw ((:reference judges) mw) mf)]]
                   {:kind      kind
                    :category  :reference
                    :context   c
                    :sentence  s
                    :engine    e
                    :reference (:reference (first ds))
                    :orders    orders
                    :world     mw
                    :minimal   mf})
        covered  (into #{} (map (juxt :context :sentence)) (:reference check))
        refusing (into #{} (comp (map :order)) (:refusals check))
        orphans  (for [d (:orders check)
                       :when (not (or (covered [(:context d) (:sentence d)])
                                      (refusing (:order-a d)) (refusing (:order-b d))))]
                   (assoc d :kind :unclassified :category :orders))]
    (vec (concat (sort-by #(pr-str (:refusal %)) refusals)
                 (sort-by #(pr-str [(:context %) (:sentence %)]) refs)
                 orphans))))

;; ---- reporting ---------------------------------------------------------

(defn default-report-dir
  "`vaelii-ref` under the platform temp directory (`java.io.tmpdir`)."
  []
  (io/file (System/getProperty "java.io.tmpdir") "vaelii-ref"))

(defn summary
  "One line naming a divergence `d` of `divergences` for `seed`: its kind and category,
  what disagreed, and the size of the minimal world when it was shrunk."
  [seed d]
  (str "seed " seed ": " (name (:kind d)) " (" (name (:category d)) ") "
       (case (:category d)
         :refusal   (let [w (or (:refused d) (:refusal d))]
                      (str "engine refused " (pr-str (:sentence w)) " in " (:context w)
                           " as " (:type d) " in " (:runs d) " run(s)"))
         :reference (str "at " (:context d) " on " (pr-str (:sentence d)) ", engine "
                         (:engine d) " reference " (:reference d) "; minimal world "
                         (count (:writes (:world d))) " writes, "
                         (count (:contexts (:world d))) " contexts; order "
                         (pr-str (mapv (juxt :sentence :context :strength)
                                       (:order (:minimal d) (first (:orders d))))))
         :orders    (str "at " (:context d) " on " (pr-str (:sentence d)) ", order a "
                         (:a d) " order b " (:b d)))))

(defn report!
  "Write the divergence `d` of `seed` as EDN into `dir` (default `default-report-dir`),
  and return `summary` followed by the file's path."
  ([seed d] (report! seed d (default-report-dir)))
  ([seed d dir]
   (let [f (io/file dir (str "reference-divergence-seed" seed "-"
                             (System/currentTimeMillis) ".edn"))]
     (io/make-parents f)
     (spit f (with-out-str (pp/pprint (assoc d :seed seed))))
     (str (summary seed d) " — " (.getPath f)))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.quality
  "Four readings about the **knowledge**, where the rest of the instrumentation reads the
  engine: which rules never fire, how skewed the predicate extents are, how deep the rule
  graph's chains reach, and how much of the taxonomy is connected to anything.

  `settle-stats` and `chain-stats` answer *how the engine ran*.  These answer *whether the
  knowledge is any good*, which is the question the author of a large KB has and the one
  nothing else here asks.  None of it is a gate: a threshold on somebody's ontology is not
  a build failure, and `lein perf` gates the engine while this reports on the content.

  **Every reading comes off state that already exists, and nothing new is indexed.**  A
  `rule -> firings` index would be a second copy of the JTMS adjacency to keep in step,
  which is the failure class the taxonomy's single `:support` map exists to avoid.  So the
  cost is
  `O(terms + rules + firings + genl edges)` and never `O(sentexes)` — the **vocabulary**,
  which on a KB of a million facts about a hundred individuals is a hundred-odd names:

  - **One walk over the term roster**, and one is the number: the functor names come off it
    by filter, and the type-shaped names come off *those* rather than off the roster a
    second time.  Measured at 8x the terms for 8x the cost, so the walk is the term the
    formula above leads with.
  - **Three O(1) index reads per functor name** — the stored extent off the count-aware
    trie, and the rule postings *both* ways.  That is everything the extent and chain
    readings need, and it is where the rule handles come from, so the record store is read
    only for the handful of rules the report actually lists.
  - **The firing census reads each rule's own `:consequences` adjacency**, the candidate
    set `jtms/restrength-informant*` uses, and never scans the justification map.  At
    11.5M justifications that difference is the report existing or not.
  - **The chain depth condenses strongly-connected components first.**  A KB's rule graph
    is cyclic in the ordinary case — `(genl ?a ?b) & (genl ?b ?c) => (genl ?a ?c)` alone
    makes it so — so memoizing a *path* re-explores the reachable subgraph along every one
    of them.  Memoize the component.

  Every count is of what is **stored**.  A believed extent is O(n) per predicate
  (`vaelii.core/count-with-functor` says why), which would turn an O(predicates) report
  into an O(sentexes) one — and stored-vs-believed is exactly the distinction an author
  wants to see rather than have chosen for them.  The firing census is the one reading that
  consults belief, because \"fired and every conclusion defeated\" is a category and not a
  rounding error."
  (:require [clojure.string :as str]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.taxonomy :as tax]))

(def default-limit
  "How many rules and how many heavy predicates the report lists before it says it
  truncated.  A cap rather than the whole set because the *counts* are the headline and a
  30,000-entry list is not one; `:limit` raises it."
  25)

(def ^:private progress-every
  "How many predicates or rules a phase covers between `:on-progress` calls.  Low enough
  that a cancel lands promptly on a corpus-sized vocabulary, high enough that the callback
  is not the cost of the pass."
  4096)

;; ---- the vocabulary pass -------------------------------------------------
;; One walk, and the three readings that come off it.  A rule is enumerated from the rule
;; index rather than by scanning the records: `index-rule-sentex` posts every rule under
;; all of its antecedent predicates and its consequent predicate, whatever its direction,
;; so probing both ways over the functor names finds every rule the index can key.

(defn- functor-name?
  "Could `t` be the functor of a literal?  Every predicate and every type name is
  lowercase-initial (`docs/naming.md`), and nothing else may head a literal, so this is
  the filter that keeps the pass to a few reads per *predicate* instead of per term."
  [t]
  (and (symbol? t) (or (nm/predicate? t) (nm/type-symbol? t))))

(defn- vocabulary-pass
  "The stored extent per predicate, plus `rule -> antecedent predicates` and
  `rule -> consequent predicate`, in one walk over the vocabulary's functor names.

  `:type-names` rides along: every type-shaped name is lowercase-initial and so is already
  in this filter's answer, which is what keeps the taxonomy reading from walking the term
  roster a second time — the roster is the report's one superlinear term and it is walked
  once."
  [kb progress!]
  (let [idx   (:index kb)
        preds (into [] (filter functor-name?) (p/terms idx))
        total (count preds)]
    ;; before the loop, so a phase with nothing in it still reports itself — a caller
    ;; watching the phases is watching for where a long report is, and \"skipped because
    ;; empty\" and \"not reached\" must not read the same
    (progress! {:phase :extents :done 0 :total total})
    (loop [i 0, extents (transient {}), ante (transient {}), conseq (transient {})]
      (if (= i total)
        {:predicates total
         :type-names (into #{} (filter nm/type-symbol?) preds)
         :extents    (persistent! extents)
         :ante       (persistent! ante)
         :conseq     (persistent! conseq)}
        (let [pred (nth preds i)
              n    (p/count-with-functor idx pred)]
          (when (and (pos? i) (zero? (mod i progress-every)))
            (progress! {:phase :extents :done i :total total}))
          (recur (inc i)
                 (if (pos? n) (assoc! extents pred n) extents)
                 (reduce (fn [m h] (assoc! m h (conj (get m h #{}) pred)))
                         ante (p/rules-by-antecedent idx pred))
                 (reduce (fn [m h] (assoc! m h pred))
                         conseq (p/rules-by-consequent idx pred))))))))

;; ---- which rules never fire ----------------------------------------------

(defn- rule-line
  "A listed rule as something an author can read: its handle, the sentence as *written*
  (a rule is stored canonically numbered, which reads as gibberish), and its context."
  [kb h]
  (when-let [sx (p/get-sentex (:records kb) h)]
    {:handle   h
     :sentence (if-let [vm (:varmap sx)]
                 (sx/originalize (:sentence sx) vm)
                 (:sentence sx))
     :context  (:context sx)}))

(defn- signature
  "A rule's **content** key: its consequent predicate and its antecedent predicates
  sorted, both read off the vocabulary pass and neither of them a record read.

  What the listed sets are ranked on, because a handle is assertion order and ranking on
  one would make the capped list a function of the order the author happened to write the
  rules in — the same knowledge loaded differently would list different rules under the
  same counts.  Two rules can share a signature (the pass knows their predicates, not
  their shape), and `rule-line-order` breaks exactly those ties."
  [pass h]
  [(str (get-in pass [:conseq h]))
   (str/join "," (sort (map str (get-in pass [:ante h] #{}))))])

(defn- rule-line-order
  "`handles` in content order, as rendered lines, capped at `limit`.

  The signature ranks them for free.  Where several rules share one — the tie the
  vocabulary pass cannot see through — the sentences themselves decide, and **only those
  are fetched**: a group of one is already ordered, so the record store is still read for
  the listed rules plus whichever share a signature with them, never for every rule in the
  set."
  [kb pass handles limit]
  (->> handles
       (group-by #(signature pass %))
       (sort-by key)
       (mapcat (fn [[_ hs]]
                 (if (next hs)
                   ;; the context joins the key: one implication stated in two contexts
                   ;; shares sentence and signature, and the residual tie fell to the
                   ;; handle set's iteration order — ahead of the `take limit` cap
                   (sort-by (fn [h] (let [rl (rule-line kb h)]
                                      [(pr-str (:sentence rl)) (str (:context rl))]))
                            hs)
                   hs)))
       (take limit)
       (into [] (keep #(rule-line kb %)))))

(defn- firing-census
  "Sort every rule handle into one of three categories by reading its node's dependents:
  never fired, fired with every conclusion defeated, or live.

  The listed handles are capped at `limit` and taken in **content order**
  (`rule-line-order`), never in handle order: a handle is assertion order, so ranking on
  one would make the listed subset a function of the order the rules were written in while
  the counts beside it are not — two loads of the same knowledge reporting the same totals
  over different examples."
  [kb pass handles limit progress!]
  (let [tms   (:tms kb)
        hs    (vec handles)
        total (count hs)]
    (progress! {:phase :rules :done 0 :total total})
    (loop [i 0, never [], defeated [], fired 0, firings 0]
      (if (= i total)
        (let [listed (fn [hs] (rule-line-order kb pass hs limit))]
          {:total              total
           :never              (listed never)
           :never-count        (count never)
           :all-defeated       (listed defeated)
           :all-defeated-count (count defeated)
           :fired              fired
           :firings            firings
           :truncated?         (boolean (or (> (count never) limit)
                                            (> (count defeated) limit)))})
        (let [h    (nth hs i)
              js   (into [] (comp (keep #(jtms/justification tms %))
                                  (filter #(= h (:informant %))))
                         (jtms/dependents tms h))
              live (count (filter #(jtms/in? tms (:consequence %)) js))]
          (when (and (pos? i) (zero? (mod i progress-every)))
            (progress! {:phase :rules :done i :total total}))
          (recur (inc i)
                 (if (empty? js) (conj never h) never)
                 (if (and (seq js) (zero? live)) (conj defeated h) defeated)
                 (if (pos? live) (inc fired) fired)
                 (+ firings (count js))))))))

;; ---- how skewed the extents are ------------------------------------------

(defn- gini
  "The Gini coefficient over the extent sizes: 0.0 when every predicate holds the same
  number, rising towards 1 as one holds everything (exactly `(n-1)/n` at that limit, so a
  small vocabulary cannot reach 1).  The single number that goes in a baseline; the
  buckets are what an author reads."
  [counts]
  (let [xs (vec (sort counts))
        n  (count xs)
        s  (reduce + 0 xs)]
    (if (or (zero? n) (zero? s))
      0.0
      (double (/ (- (* 2 (reduce + 0 (map-indexed (fn [i x] (* (inc i) x)) xs)))
                    (* (inc n) s))
                 (* n s))))))

(defn- extent-skew
  "Buckets by order of magnitude, a Gini, and the heaviest predicates.  Ties among the
  heaviest break on the **name**, so the list is the same however the KB was loaded."
  [pass limit]
  (let [extents (:extents pass)
        xs      (vec (vals extents))]
    {:predicates  (:predicates pass)
     :with-extent (count xs)
     :stored      (reduce + 0 xs)
     :gini        (gini xs)
     :buckets     (frequencies (map #(long (Math/floor (Math/log10 (double %)))) xs))
     :heaviest    (into [] (comp (map (fn [[pred n]] [pred n])) (take limit))
                        (sort-by (juxt (comp - val) (comp str key)) extents))}))

;; ---- how deep the chains reach -------------------------------------------

(defn- rule-graph
  "consequent functor -> the antecedent functors of every rule concluding it."
  [{:keys [ante conseq]}]
  (reduce-kv (fn [g h c] (update g c (fnil into #{}) (get ante h #{})))
             {} conseq))

(defn- sccs
  "Tarjan's strongly-connected components, iterative — the recursive spelling overflows
  the stack on a graph a rule set is entitled to have.  Returns a vector of node sets."
  [g]
  (let [nodes (into #{} (concat (keys g) (mapcat val g)))]
    (loop [stack (vec nodes), idx {}, low {}, on #{}, s [], out [], counter 0, work []]
      (cond
        (seq work)
        (let [[v state] (peek work)]
          (case state
            :enter
            (if (contains? idx v)
              (recur stack idx low on s out counter (pop work))
              (recur stack (assoc idx v counter) (assoc low v counter) (conj on v)
                     (conj s v) out (inc counter)
                     (into (conj (pop work) [v :exit])
                           (map (fn [w] [w :enter])) (get g v #{}))))
            :exit
            (let [lo  (reduce (fn [a w] (if (contains? on w)
                                          (min a (get low w (get idx w)))
                                          a))
                              (get low v) (get g v #{}))
                  low (assoc low v lo)]
              (if (= lo (get idx v))
                (let [[comp s'] (split-with #(not= % v) (reverse s))
                      comp      (conj (vec comp) v)]
                  (recur stack idx low (reduce disj on comp)
                         (vec (reverse (rest s'))) (conj out (set comp)) counter (pop work)))
                (recur stack idx low on s out counter (pop work))))))
        (seq stack)
        (recur (pop stack) idx low on s out counter [[(peek stack) :enter]])
        :else out))))

(defn- component-depths
  "Longest path to a leaf, per condensed component, on an **explicit** stack: the
  recursive spelling stack-overflows just past a thousand-deep chain, which a rule graph
  is entitled to have.  The condensation is a DAG, so this terminates on a cyclic input —
  which is the ordinary input."
  [cg ids]
  (loop [todo (vec ids), depths {}]
    (if-let [c (peek todo)]
      (if (contains? depths c)
        (recur (pop todo) depths)
        (let [ss     (get cg c)
              undone (into [] (remove #(contains? depths %)) ss)]
          (if (seq undone)
            (recur (into todo undone) depths)
            (recur (pop todo)
                   (assoc depths c (if (seq ss) (inc (reduce max 0 (map depths ss))) 0))))))
      depths)))

(defn- chain-depth
  "Depth per rule — the depth of the component its consequent functor lands in — as a
  histogram plus the fraction of rules in a chain at least that deep, which is the reading
  a single number loses: most rules can sit at depth 1 while one outlier reaches 7."
  [pass progress!]
  (progress! {:phase :chains :done 0 :total (count (:conseq pass))})
  (let [g      (rule-graph pass)
        comps  (sccs g)
        k      (count comps)
        ;; the condensation is keyed by a component **id**, not by the component itself:
        ;; two node sets compare equal in O(nodes), and the `remove` below runs one such
        ;; comparison per edge — which is how an O(V+E) pass turns into O(V*E) and reads as
        ;; a second, quieter version of the memoize-the-path mistake (measured: 1,146ms to
        ;; 36ms on a 4,000-functor cycle)
        of     (into {} (for [i (range k), node (nth comps i)] [node i]))
        cg     (reduce (fn [m i]
                         (assoc m i (into #{} (comp (mapcat #(get g % #{}))
                                                    (keep of)
                                                    (remove #(= % i)))
                                          (nth comps i))))
                       {} (range k))
        depths (component-depths cg (range k))
        ;; per rule, not per component: a component's depth is shared by every rule
        ;; concluding into it, and it is rules the author is asking about
        rules  (into [] (keep #(get depths (get of %))) (vals (:conseq pass)))
        n      (count rules)
        hist   (frequencies rules)
        deepest (reduce max 0 (keys hist))]
    {:functors   (count of)
     :components k
     ;; a self-loop is a cycle of one node, and `genl` transitivity is exactly that — so
     ;; counting only multi-node components would report the commonest cycle as acyclic
     :cyclic     (count (filter (fn [c] (or (> (count c) 1)
                                            (some #(contains? (get g % #{}) %) c)))
                                comps))
     :largest    (reduce max 0 (map count comps))
     :rules      n
     :depths     hist
     :at-least   (into (sorted-map)
                       (for [d (range 1 (inc deepest))]
                         [d (if (zero? n)
                              0.0
                              (double (/ (count (filter #(>= % d) rules)) n)))]))}))

;; ---- how much of the taxonomy is connected -------------------------------

(defn- taxonomy-coverage
  "Two numbers, not one: how many type names carry a `genl` edge at all, and how many
  reach the root.  A type with an edge into a disconnected island is counted by the first
  and not the second, and **the gap between them is the finding**.

  The root is *found*, not assumed — `thing` is this engine's and a converted corpus
  brings its own — so whatever type the most others reach is the one reported against, and
  the reading means the same on a corpus that never heard of `thing`.

  The denominator is every type-shaped name in the vocabulary, which by `docs/naming.md`
  includes a bare lowercase word (`likes` is a legal predicate *and* a legal type name;
  arity decides and the index does not record arity).  That is why the gap is the finding
  rather than either fraction on its own.

  Reachability is **reflexive**, as `genls` is: the root reaches itself, so `:rooted`
  counts it and `:islands` is exactly the edged types outside the root's cone."
  [kb pass progress!]
  (let [taxo  (:taxonomy kb)
        nodes (tax/types taxo)
        named (:type-names pass)]
    (progress! {:phase :taxonomy :done 0 :total (count nodes)})
    (let [reach (frequencies (mapcat #(tax/genls taxo %) nodes))
          [root rooted] (first (sort-by (juxt (comp - val) (comp str key)) reach))]
      {:names   (count (into named nodes))
       :edged   (count nodes)
       :root    root
       :rooted  (or rooted 0)
       :islands (max 0 (- (count nodes) (or rooted 0)))})))

;; ---- the report ----------------------------------------------------------

(defn census
  "The four readings as one map — `{:rules … :extents … :chains … :taxonomy …}`.
  `vaelii.core/kb-quality` is the door and documents the options."
  [kb {:keys [limit on-progress]}]
  ;; sequenced in a `let` rather than left to a map literal's argument order: the phases a
  ;; caller watching `:on-progress` sees are part of what this answers, and an evaluation
  ;; order is not something to read off the shape of a literal
  (let [limit     (or limit default-limit)
        progress! (or on-progress (fn [_] nil))
        pass      (vocabulary-pass kb progress!)
        handles   (into (set (keys (:ante pass))) (keys (:conseq pass)))
        rules     (firing-census kb pass handles limit progress!)
        extents   (extent-skew pass limit)
        chains    (chain-depth pass progress!)
        taxonomy  (taxonomy-coverage kb pass progress!)]
    {:rules rules :extents extents :chains chains :taxonomy taxonomy}))

;; ---- the same map, as prose ----------------------------------------------
;; A separate function over the report rather than a second traversal of the KB, so
;; nothing can print a figure the data does not hold.

(defn- pct [n total] (if (pos? total) (format "%.1f%%" (* 100.0 (/ (double n) total))) "—"))

(defn- commas [n] (format "%,d" (long n)))

(defn- rule-lines [heading rules]
  (when (seq rules)
    (str "\n" heading "\n\n"
         (str/join "\n" (for [{:keys [handle sentence context]} rules]
                          (str "- `" handle "` `" (pr-str sentence) "` in `" context "`")))
         "\n")))

(defn report
  "The `census` map as Markdown — the four readings in the order an author reads them,
  the counts first and the lists after.  A map that is not a `census` answer is refused
  (`:not-a-report`) rather than rendered as a page of zeros, which is what a caller passing
  the wrong map would otherwise be handed and believe."
  [{:keys [rules extents chains taxonomy] :as quality}]
  (when-not (and (map? quality) (:total rules) (:predicates extents)
                 (:rules chains) (:names taxonomy))
    (throw (ex-info (str "not a kb-quality report — want the map `kb-quality` answers, with"
                         " :rules / :extents / :chains / :taxonomy")
                    {:type :not-a-report :keys (when (map? quality) (vec (sort (keys quality))))})))
  (str
   "# KB quality\n\n"
   "## Rules that never fire\n\n"
   (commas (:total rules)) " rules — **" (commas (:never-count rules)) " never fired** ("
   (pct (:never-count rules) (:total rules)) "), " (commas (:all-defeated-count rules))
   " fired with every conclusion defeated, " (commas (:fired rules))
   " live; " (commas (:firings rules)) " recorded firings in all.\n\n"
   "A firing is a **currently supported** one: a rule whose conclusions have since been\n"
   "retracted has no live justification and is counted as never fired.\n"
   (rule-lines "### Never fired" (:never rules))
   (rule-lines "### Fired, every conclusion defeated" (:all-defeated rules))
   (when (:truncated? rules)
     (str "\nThe lists are capped; the counts above are not.\n"))
   "\n## Predicate extent skew\n\n"
   (commas (:predicates extents)) " predicates, " (commas (:with-extent extents))
   " with an extent, " (commas (:stored extents)) " stored facts, Gini "
   (format "%.4f" (:gini extents)) ".\n\n"
   "| extent | predicates |\n|---|---|\n"
   (str/join "\n" (for [[k n] (sort (:buckets extents))]
                    (str "| 10^" k " | " (commas n) " |")))
   "\n\n### The heaviest\n\n"
   (str/join "\n" (for [[pred n] (:heaviest extents)]
                    (str "- `" pred "` — " (commas n))))
   "\n\n## Chain depth over the rule graph\n\n"
   (commas (:functors chains)) " functors in " (commas (:components chains))
   " components (" (commas (:cyclic chains)) " cyclic, largest " (commas (:largest chains))
   "), over " (commas (:rules chains)) " rules.\n\n"
   "| depth | rules | at least |\n|---|---|---|\n"
   (str/join "\n" (for [[d n] (sort (:depths chains))]
                    (str "| " d " | " (commas n) " | "
                         (if-let [f (get (:at-least chains) d)]
                           (format "%.1f%%" (* 100.0 f))
                           "100.0%")
                         " |")))
   "\n\n## Taxonomy coverage\n\n"
   (commas (:names taxonomy)) " type names — " (commas (:edged taxonomy))
   " carry a `genl` edge (" (pct (:edged taxonomy) (:names taxonomy)) ")"
   (if-let [root (:root taxonomy)]
     (str ", " (commas (:rooted taxonomy)) " reach `" root "` ("
          (pct (:rooted taxonomy) (:names taxonomy)) ").\n\n"
          "Edged but not reaching the root: " (commas (:islands taxonomy))
          " — the types sitting in disconnected islands, and the gap between the two\n"
          "fractions above is the finding rather than either one of them.\n")
     ;; no edge anywhere means no root to report against, which is a different statement
     ;; from a root nothing reaches — and an empty code span is neither
     ".\n\nNo `genl` edge anywhere, so there is no root to measure reach against.\n")))

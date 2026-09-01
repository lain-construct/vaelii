;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.mixed-order-property-test
  "Order independence over a **mixed** KB, on every storage backend.

  The per-subsystem shuffle tests each hold one mechanism still and permute the rest:
  `aggregate_test` the aggregates, `equality_test` the partition, `inherit_forward_test`
  the genl seeding, `constraint_nogood_test` the nogoods, `canonical_vars_test` the
  variable canonicalization, `asp_edge_test` the solver. `property_test` generates
  scenarios rather than writing them, but from one pool in one context.

  A mixed KB is where the mechanisms meet, and the meeting is the part no per-subsystem
  shuffle sees. So the pool here spans them at once: ground facts in three contexts
  joined by `genlCx` edges, a four-link `genl` chain, a defeasible rule and a monotonic
  one, a rule with a negated antecedent, a rule carrying its own `exceptWhen`, a `sameAs`
  edge above one of the context edges and two `equals` edges — one beside the fact it
  displaces, one on the type a rule fires on — and two chains that end where they began.
  A drawn subset routinely puts a taxonomy edge, an equality merge, an exception and a
  retraction into one KB, and the question is whether the arrival order of those decides
  anything.

  **What is compared, and why it is content.** Three readings, all handle-free:

  - the believed sentences **per assertion context**, and per **view** context up the
    `genlCx` cone (which is where the exception force and the visibility gate land);
  - the belief label of each believed sentex — `defeat-class`, plus the contradiction
    and conflict tallies, so a flipped class or a double-counted dilemma surfaces;
  - the `genl` / `genlCx` closures at every probe type and context, plus the equality
    partition they are cached beside.

  Which sentexes are **stored** is deliberately absent, for `property_test`'s reason: a
  conclusion drawn and then defeated leaves a record an ordering that defeated its
  antecedent first never wrote, and both orderings read the same belief off different
  record sets. A stored sentex is not a believed one.

  **Every backend, one JVM.** `scripts/test-backends.sh` runs the whole suite on each of
  the eight, which is the thorough gate and a thing somebody has to remember; this
  opens all eight itself, so an order-dependence that only appears under the durable
  index fails in an ordinary `lein test`. The KBs are private — their own spaces, and a
  private temp directory per durable arm — so they share a store with nothing.

  **Two runs of one property, and the difference is the seed.** The `:default` sweep
  fixes it and draws small scenarios, so a red is reproducible from the failure alone.
  The `^:slow` run takes three fixed seeds and draws the whole pool. Both assert one
  `is` per backend (per seed, in the slow one) whatever they find, so the assertion
  count is a property of the file rather than of the box."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.walk :as walk]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

;; ---- the vocabulary the pool is written in --------------------------------

(def ^:private cx-base  'CxMixBase)
(def ^:private cx-home  'CxMixHome)
(def ^:private cx-field 'CxMixField)

;; The contexts a reading is taken from: the three the pool writes in, plus the one the
;; `genlCx` edges are asserted in — an edge is forced global (docs/contexts.md), so where
;; it is stored may not decide what the closure says.
(def ^:private view-contexts [cx-base cx-home cx-field 'CxUniverse])

(def ^:private probe-types '[terrier dog mammal animal thing])
(def ^:private probe-terms '[Rex Nell Tom Thomas Bud Sparrow Ann Anna Kip Kipper])

(defn- default-rule [antes conseq]
  (list 'set/defaultRule (list 'implies (cons 'and antes) conseq)))

;; Each entry is a **chain**: `[label op]` pairs that must run in the order written.
;; Most chains are one op long and constrain nothing; the two at the end hold a
;; retraction to the assertion whose handle it names, which a flat permutation cannot
;; say. Labelled so a shrunk counterexample prints the operations.
;;
;; Every chain is well-formed on its own and any sub-multiset runs in any linear
;; extension without throwing — so a failing property is an order-dependence and not a
;; bad input. A chain drawn twice re-asserts a sentence that canonicalizes to the handle
;; it already has, and the second retraction then names nothing, which `retract!` takes.
(def ^:private chain-pool
  [;; the two contexts, hung under the base
   [[:home-sees-base
     #(v/assert % (list 'genlCx cx-home cx-base) 'CxUniverse {:strength :monotonic})]]
   [[:field-sees-base
     #(v/assert % (list 'genlCx cx-field cx-base) 'CxUniverse {:strength :monotonic})]]
   ;; the genl chain, one link per chain so a subset can break it anywhere
   [[:terrier-is-a-dog
     #(v/assert % '(genl terrier dog) cx-base {:strength :monotonic})]]
   [[:dogs-are-mammals
     #(v/assert % '(genl dog mammal) cx-base {:strength :monotonic})]]
   [[:mammals-are-animals
     #(v/assert % '(genl mammal animal) cx-base {:strength :monotonic})]]
   ;; ground facts, spread over the two child contexts
   [[:rex-is-a-terrier
     #(v/assert % '(terrier Rex) cx-home {:strength :monotonic})]]
   [[:nell-is-a-dog
     #(v/assert % '(dog Nell) cx-field)]]
   [[:tom-is-a-mammal
     #(v/assert % '(mammal Tom) cx-field {:strength :monotonic})]]
   [[:bud-is-a-dog
     #(v/assert % '(dog Bud) cx-home)]]
   ;; the rules: a default, a monotonic one over its conclusion, one that triggers on a
   ;; negated antecedent, and one that states its own exception
   [[:dogs-bark
     #(v/assert % (default-rule '[(dog ?x)] '(barks ?x)) cx-base)]]
   [[:barking-is-audible
     #(v/assert-rule % '[(barks ?x)] '(audible ?x) cx-base {:strength :monotonic})]]
   [[:a-silent-dog-is-quiet
     #(v/assert-rule % '[(dog ?x) (not (barks ?x))] '(quiet ?x) cx-base)]]
   [[:mammals-have-fur-unless-shorn
     #(v/assert % (list 'exceptWhen '(shorn ?x)
                        (default-rule '[(mammal ?x)] '(has_fur ?x)))
                cx-base)]]
   [[:rex-is-shorn
     #(v/assert % '(shorn Rex) cx-home {:strength :monotonic})]]
   ;; The equality edges, each over an individual a stored fact mentions — so a merge has
   ;; records to displace and a representative to elect, and the closure behind
   ;; `representative` / `equiv-class` is recomputed on an edge that can arrive anywhere
   ;; in the sequence.
   ;;
   ;; **The three positions a merge can sit in are all in the pool**, because each is a
   ;; different question about when migration runs and all three are settled by content
   ;; rather than by arrival:
   ;;
   ;; - `kip-equals-kipper` sits in the context holding the fact it displaces, which is
   ;;   the merge arriving beside its own records;
   ;; - `ann-is-anna` sits **above** a `genlCx` edge, so `cx-field` cannot see it until
   ;;   `field-sees-base` is drawn and arrives — and when that edge arrives last it is
   ;;   the edge, not the merge and not the fact, that owes the restatement;
   ;; - `tom-is-thomas` reaches a **rule**: `mammal` is what the excepted default fires
   ;;   on, so the merge retires the spelling the rule's own trigger arrives under, and
   ;;   the conclusion must be drawn once at the elected name whichever of the three
   ;;   came last.
   [[:ann-owns-nell
     #(v/assert % '(ownerOf Anna Nell) cx-field {:strength :monotonic})]]
   [[:ann-is-anna
     #(v/assert % '(sameAs Ann Anna) cx-base {:strength :monotonic})]]
   [[:kip-owns-rex
     #(v/assert % '(ownerOf Kip Rex) cx-home {:strength :monotonic})]]
   [[:kip-equals-kipper
     #(v/assert % '(equals Kip Kipper) cx-home {:strength :monotonic})]]
   [[:tom-is-thomas
     #(v/assert % '(equals Tom Thomas) cx-base {:strength :monotonic})]]
   ;; ---- the chains that end where they began ----
   ;; A fact learned and forgotten. While it stands it feeds the default rule and
   ;; whatever the default feeds, so the retraction has a cascade to sweep.
   [[:sparrow-is-a-dog
     #(v/assert % '(dog Sparrow) cx-field)]
    [:forget-the-sparrow
     #(v/retract! % (v/handle-of % '(dog Sparrow) cx-field))]]
   ;; A doubt raised and withdrawn. This one defeats rather than adds, and it is also
   ;; what makes `a-silent-dog-is-quiet` fire: while it stands Nell is quiet rather than
   ;; barking, and lifting it has to take the quiet back.
   [[:doubt-nells-barking
     #(v/assert % '(not (barks Nell)) cx-field {:strength :monotonic})]
    [:withdraw-the-doubt
     #(v/retract! % (v/handle-of % '(not (barks Nell)) cx-field))]]])

(defn- op-of    [[ci si]] (second (nth (nth chain-pool ci) si)))
(defn- label-of [[ci si]] (first  (nth (nth chain-pool ci) si)))

;; ---- the reading ----------------------------------------------------------

(defn- name-by-content
  "`form` with every `(sentexHandle N)` term replaced by the **sentence** stored at N.

  A meta-sentex predicates about another sentex by naming its handle, and `exceptWhen`
  is stored that way (docs/exceptions.md): the rule keeps its own handle and the
  exception becomes `(exceptWhen <query> (sentexHandle H))` beside it. So the stored
  sentence carries an allocation order *inside its own content*, and two orderings that
  attach the same exception to the same rule spell it `(sentexHandle 1)` and
  `(sentexHandle 2)`. Neither belief nor the attachment differs; only the number does.
  What the claim is about is the referent's content, which is what this substitutes.
  Bounded, so a meta naming a meta terminates whatever the store holds."
  ([kb form] (name-by-content kb form 4))
  ([kb form depth]
   (if (neg? ^long depth)
     form
     (walk/postwalk
      (fn [x]
        (if-let [id (and (v/sentex-handle? x) (v/handle-id x))]
          (if-let [sx (v/sentex kb id)]
            (list 'sentexHandle (name-by-content kb (:sentence sx) (dec (long depth))))
            x)
          x))
      form))))

(defn- believed-rows
  "`{:handle :sentence :context}` for every believed sentex — the handle is carried for
  the label reads below and never compared."
  [kb]
  (into []
        (keep (fn [h]
                (when (v/in? kb h)
                  (when-let [sx (v/sentex kb h)]
                    {:handle   (long h)
                     :sentence (name-by-content kb (:sentence sx))
                     :context  (:context sx)}))))
        (tu/sentex-ids kb)))

(defn- reading
  "A whole-KB reading, compared as one value across orderings. Content and belief only."
  [kb]
  (let [rows (believed-rows kb)]
    {;; the believed sentences, grouped by the context they were asserted in
     :believed-by-context
     (reduce (fn [m r] (update m (:context r) (fnil conj #{}) (:sentence r))) {} rows)
     ;; and grouped by the context a reader stands in: up the genlCx cone, after the
     ;; exception cascade that context can see
     :visible-from
     (into {} (for [c view-contexts]
                [c (into #{} (comp (filter #(and (v/sees? kb c (:context %))
                                                 (v/believed? kb (:handle %) c)))
                                   (map :sentence))
                         rows)]))
     ;; the belief label of each, keyed by content
     :defeat-classes
     (into {} (map (fn [r] [[(:context r) (:sentence r)] (v/defeat-class kb (:handle r))])) rows)
     :contradictions (count (v/contradictions kb))
     :conflicts      (count (v/conflicts kb))
     ;; the cached closures, per context because a closure is scoped
     :genls   (into {} (for [c view-contexts t probe-types] [[c t] (v/genls kb t c)]))
     :specs   (into {} (for [c view-contexts t probe-types] [[c t] (v/specs kb t c)]))
     :isa     (into {} (for [c view-contexts x probe-terms t probe-types]
                         [[c x t] (v/isa? kb x t c)]))
     :context-up   (into {} (for [c view-contexts] [c (v/context-up kb c)]))
     :context-down (into {} (for [c view-contexts] [c (v/context-down kb c)]))
     ;; the equality partition, cached and recomputed the same way the closures are
     :equiv-class    (into {} (for [c view-contexts x probe-terms] [[c x] (v/equiv-class kb x c)]))
     :representative (into {} (for [c view-contexts x probe-terms] [[c x] (v/representative kb x c)]))}))

(defn- run-order
  "Apply one ordering to a fresh KB over `opts`' stores and read it.

  A **new KB value** per ordering rather than one KB cleared between them: `clear!`
  empties the stores and says so, but the JTMS and the taxonomy live in memory and it
  leaves them where they are (`core/clear!`, and it is what `tu/fresh` re-opens for).
  Two KBs over one durable directory share the store, so a durable arm re-opens rather
  than remounting."
  [opts order]
  (let [kb (doto (v/open-kb (assoc opts :recover? false)) (tu/clear-kb!))]
    (doseq [step order] ((op-of step) kb))
    (reading kb)))

(defn- disagreement
  "nil when every ordering reads the same, else the first key they differ at with the
  distinct values under it — a whole-map mismatch over fourteen keys names none of them."
  [opts orders]
  (let [readings (mapv #(run-order opts %) orders)
        head     (first readings)]
    (some (fn [k]
            (let [vs (into #{} (map #(get % k)) readings)]
              (when (< 1 (count vs)) {:key k :values vs})))
          (sort-by str (keys head)))))

;; ---- the backends ---------------------------------------------------------

;; A private temp directory per durable arm rather than one derived from a space
;; number: a derived directory is a fixed global path, so a previous run that was killed
;; rather than closed leaves its single-writer lock behind and every later run fails on
;; it.
(defn- disk-dir []
  (str (java.nio.file.Files/createTempDirectory
        "vaelii-mixorder-" (into-array java.nio.file.attribute.FileAttribute []))))

(defn- backends
  "The eight `scripts/lib/suite-configs.sh` names, as opts. Namespaced spaces, so a KB
  here shares a store with nothing — not another test's, and not its own siblings'."
  []
  [{:backend :memory          :space [::mix :memory]}
   {:backend :memory-dense    :space [::mix :dense]}
   {:backend :memory-columnar :space [::mix :columnar]}
   {:backend :disk-memory     :dir (disk-dir)}
   {:backend :disk-dense      :dir (disk-dir)}
   {:backend :disk-columnar   :dir (disk-dir)}
   {:backend :disk-log        :dir (disk-dir)}
   ;; the fork decorator over an EMPTY base (docs/overlay.md): every merge rule
   ;; degenerates, so the orderings must agree exactly as they do on the plain store
   {:backend :overlay
    :base    {:backend :memory :space [::mix :overlay-base]}
    :overlay {:backend :memory :space [::mix :overlay-top]}}])

(defn- on-backend
  "Call `(f opts)`, and leave nothing behind — a durable arm holds a single-writer lock
  and file handles for the JVM's life unless it is closed."
  [opts f]
  (try (f opts)
       (finally
         (doto (v/open-kb (assoc opts :recover? false)) (tu/clear-kb!))
         (when-let [dir (:dir opts)]
           ((requiring-resolve 'vaelii.impl.disk.backend/close-dir!) dir)
           ;; best-effort: the durability daemon may still hold a handle, in which case
           ;; a few KB survive in the OS temp directory — which is what it is for
           (doseq [f (reverse (file-seq (java.io.File. ^String dir)))]
             (.delete ^java.io.File f))))))

;; ---- the generator --------------------------------------------------------

(defn- gen-linearization
  "One random linear extension of `chains`: at each step take the head of a chain that
  still has steps left, so every chain keeps its own order while the chains interleave
  freely. Written out rather than taken from a test.check combinator, so it stays fixed
  across versions of the library."
  [chains]
  (let [chains (into [] (remove empty?) chains)]
    (if (empty? chains)
      (gen/return [])
      (gen/let [i    (gen/choose 0 (dec (count chains)))
                tail (gen-linearization (update chains i rest))]
        (into [(first (nth chains i))] tail)))))

(defn- steps-of
  "The drawn chain indices as chains of `[chain-index step-index]` steps — data, so a
  shrunk counterexample prints as something a reader can map back to labels."
  [picks]
  (mapv (fn [ci] (into [] (map-indexed (fn [si _] [ci si])) (nth chain-pool ci))) picks))

(defn- gen-scenario
  "A sub-multiset of the pool, `lo` to `hi` chains, and `n` independent orderings of it.
  Independent orderings rather than the written order against a reordering: with chains
  the written order is one linear extension among many and has no claim to be the
  reference, and drawing them all makes the property symmetric in what it compares."
  [lo hi n]
  (gen/let [picks  (gen/vector (gen/choose 0 (dec (count chain-pool))) lo hi)
            orders (apply gen/tuple (repeat n (gen-linearization (steps-of picks))))]
    (vec orders)))

(defn- labels-of [orders] (mapv #(mapv label-of %) orders))

(defn- check-seed
  "Run the property against one backend at one seed and report it as one `is`, whatever
  it finds — so the assertion count is a property of the file and not of what it found."
  [opts scenario num-tests seed]
  (let [res      (tc/quick-check num-tests
                                 (prop/for-all [orders scenario]
                                               (nil? (disagreement opts orders)))
                                 :seed seed)
        smallest (some-> res :shrunk :smallest first)]
    (is (:pass? res)
        (str (name (:backend opts)) " reads two orderings of one KB differently"
             " (seed " seed ")"
             (when smallest
               (str "\n  orderings: " (pr-str (labels-of smallest))
                    "\n  " (pr-str (disagreement opts smallest))))))))

;; ---- the properties -------------------------------------------------------

;; Small scenarios and a fixed seed: the draws are the same on every machine and every
;; run, so a red reproduces from the failure alone.
(def ^:private default-seed 20260825)

(deftest a-mixed-kb-reads-the-same-in-any-order
  ;; Parity between orderings that all did nothing is worthless, so pin the pool down
  ;; first: run every chain in the order written and check the KB it builds is the
  ;; interaction-dense one the docstring claims.
  (testing "the pool is not vacuous"
    (on-backend {:backend :memory :space [::mix :witness]}
                (fn [opts]
                  (let [r (run-order opts (into [] cat (steps-of (range (count chain-pool)))))]
                    (is (contains? (get-in r [:visible-from cx-home]) '(barks Bud))
                        "the default rule fired, over a type it reaches by the genl chain")
                    (is (contains? (get-in r [:visible-from cx-home]) '(audible Bud))
                        "and the monotonic rule fired on its conclusion")
                    (is (contains? (get-in r [:visible-from cx-home]) '(has_fur Bud))
                        "the excepted rule concluded where its exception does not hold")
                    (is (not (contains? (get-in r [:visible-from cx-home]) '(has_fur Rex)))
                        "and was blocked where it does")
                    (is (= '#{terrier dog mammal animal} (get-in r [:genls [cx-home 'terrier]]))
                        "the genl chain closed")
                    (is (= #{cx-base cx-home} (get-in r [:context-up cx-home]))
                        "and the genlCx edge did")
                    (is (contains? (get-in r [:visible-from cx-field]) '(barks Nell))
                        "a sibling context's own conclusion is visible from it")
                    (is (not (contains? (get-in r [:visible-from cx-home]) '(barks Nell)))
                        "and not from the other side of the cone")
                    (is (= (get-in r [:representative [cx-field 'Ann]])
                           (get-in r [:representative [cx-field 'Anna]]))
                        "the sameAs edge merged")
                    (is (contains? (get-in r [:believed-by-context cx-field])
                                   (list 'ownerOf (get-in r [:representative [cx-field 'Ann]]) 'Nell))
                        "and the fact it displaced, a context edge below it, is restated")
                    (is (contains? (get-in r [:visible-from cx-field]) '(has_fur Thomas))
                        "the merge on the rule's own type concludes at the elected spelling")
                    (is (not (contains? (get-in r [:visible-from cx-field]) '(has_fur Tom)))
                        "and nowhere else")
                    (is (not (contains? (get-in r [:believed-by-context cx-field]) '(dog Sparrow)))
                        "and the chains that end where they began left nothing behind")))))
  (let [scenario (gen-scenario 3 8 3)]
    (doseq [opts (backends)]
      (testing (str "backend " (name (:backend opts)))
        (on-backend opts #(check-seed % scenario 4 default-seed))))))

;; The search half: three seeds and the whole pool, so a shape the fixed seed never draws
;; has somewhere to be found. The seeds are written down rather than taken from the
;; clock — a counterexample nobody can re-run is a counterexample nobody fixes.
(def ^:private slow-seeds [20260825 314159265 987654321])

(deftest ^:slow a-large-mixed-kb-reads-the-same-in-any-order
  (let [scenario (gen-scenario 6 (count chain-pool) 3)]
    (doseq [opts (backends)]
      (testing (str "backend " (name (:backend opts)))
        ;; one `is` per seed, and the durable arm's directory torn down once at the end
        ;; rather than per seed
        (on-backend opts
                    (fn [o] (doseq [seed slow-seeds]
                              (check-seed o scenario 12 seed))))))))

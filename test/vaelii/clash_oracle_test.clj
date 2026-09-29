;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.clash-oracle-test
  "Incremental clash discovery finds the same nogoods as the exhaustive pass
  (`settle/*incremental-clashes*` bound false), which checks every believed sentex on
  every settle.  Each test runs one operation sequence into two KBs, one each way, and
  compares believed content, dilemmas, conflicts and refusals after every step, so a
  divergence names the operation that caused it (docs/nmtms.md, \"How a settle finds the
  clashes\").

  Both KBs run under `checks/*arbitrate-constraints?*`: under `:refuse` the entry point
  refuses most clashing writes, so few pairs form to compare.

  No `transitiveInArg` declaration is made, since a claim read through argument
  preservation convicts one way only and the two passes differ on it by design
  (docs/nmtms.md, \"Where conviction is one-sided\").  A pair across a visibility edge is
  covered: individuals are written in either context.

  Disabling either arm of `could-clash?`, forgetting the remembered pairs, or skipping
  the retroactive sweep turns these streams red.  The carry-forward's `moved?` is not
  reachable here: a pair whose member the region holds is re-derived through the region
  and the fresh answer overrides the carried one.  `lein perf`'s `clash-arbitration`
  holds the carry instead."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

;; ---- the shared ontology ------------------------------------------------

(def ^:private ctxs '[CxClashBase CxClashSub])

(def ^:private types
  '[animal mammal reptile dog cat snake plant])

(def ^:private inds
  "One pool of individuals for both contexts, so a term routinely holds one membership
  either side of the `genlCx` edge — the pair only `CxClashSub` can see whole
  (see the namespace docstring)."
  '[CI0 CI1 CI2 CI3 CI4 CI5])

(defn- build-ontology!
  "A hierarchy a separation closes over several levels of, two contexts, and one
  declaration of each arbitrable kind.  `(disjoint dog cat)`, `(genl snake animal)`,
  `(anti_transitive precedes)` and `(sibling_disjoint animal)` are left for the stream,
  so declarations also arrive over stored content.  Two rules conclude `(dog ?x)`, so a
  second route from a `:monotonic` premise can lift a standing pair's `:priority` while
  both its handles sit still."
  [kb]
  (v/with-deferred-settle kb
    (v/assert kb (list 'genlCx (second ctxs) (first ctxs)) 'CxUniverse)
    (doseq [[sub sup] '[[mammal animal] [reptile animal] [dog mammal] [cat mammal]]]
      (v/assert kb (list 'genl sub sup) (first ctxs) {:strength :monotonic}))
    (v/assert kb '(disjoint mammal reptile) (first ctxs) {:strength :monotonic})
    (v/assert kb '(disjoint animal plant)   (first ctxs) {:strength :monotonic})
    (v/assert kb '(functional ageOf)        (first ctxs) {:strength :monotonic})
    (v/assert kb '(asymmetric parentOf)     (first ctxs) {:strength :monotonic})
    (doseq [from '[pet canine]]
      (v/assert kb (list 'set/forwardRule (vr/rule-sentence [(list from '?x)] '(dog ?x)))
                (first ctxs) {:strength :monotonic}))))

;; ---- the operation stream -----------------------------------------------

(defn- rand-op
  "One write, drawn over every route a clash arrives by: a membership, a functional
  slot value, an asymmetric converse, a chain step, a retraction, a premise a rule
  derives a membership from, a declaration arriving after the content it convicts, a
  sibling-disjointness exception arriving and leaving, and a `rewriteOf` merge arriving
  and leaving."
  [^java.util.Random rng]
  (let [ctx  (nth ctxs (.nextInt rng (count ctxs)))
        ind  #(nth inds  (.nextInt rng (count inds)))
        typ  #(nth types (.nextInt rng (count types)))
        str8 #(if (zero? (.nextInt rng 3)) {:strength :monotonic} {})
        ;; a small pool for `precedes`, so random pairs close two-step chains
        near #(nth inds (.nextInt rng 3))]
    (case (.nextInt rng 20)
      (0 1 2) [:assert (list (typ) (ind)) ctx (str8)]
      (3 4)   [:assert (list 'ageOf (ind) (.nextInt rng 4)) ctx (str8)]
      (5 6)   [:assert (list 'parentOf (ind) (ind)) ctx (str8)]
      7       [:retract (list (typ) (ind)) ctx]
      8       [:assert '(disjoint dog cat) (first ctxs) {:strength :monotonic}]
      9       [:assert '(genl snake animal) (first ctxs) {:strength :monotonic}]
      (10 11) [:assert (list (if (even? (.nextInt rng 2)) 'pet 'canine) (ind)) ctx (str8)]
      12      [:retract (list (if (even? (.nextInt rng 2)) 'pet 'canine) (ind)) ctx]
      13      [:assert (list 'precedes (near) (near)) ctx (str8)]
      14      [:assert '(anti_transitive precedes) (first ctxs) {:strength :monotonic}]
      15      [:assert '(sibling_disjoint animal) (first ctxs) {:strength :monotonic}]
      16      [:assert '(siblingDisjointException dog cat) (first ctxs) {:strength :monotonic}]
      17      [:retract '(siblingDisjointException dog cat) (first ctxs)]
      18      [:assert (list 'rewriteOf (ind) (ind)) (first ctxs) {:strength :monotonic}]
      19      [:retract (list 'rewriteOf (ind) (ind)) (first ctxs)])))

(defn- apply-op!
  "Run one op, returning a refusal as an observation the two KBs must agree on."
  [kb [kind sentence context opts]]
  (try (case kind
         :assert  (do (v/assert kb sentence context opts) :ok)
         :retract (if-let [h (v/handle-of kb sentence context)]
                    (do (v/retract! kb h) :ok)
                    :absent))
       (catch clojure.lang.ExceptionInfo e
         [:refused (:type (ex-data e))])))

;; ---- the observation ----------------------------------------------------

(defn- clash-key
  "A reported pair as content: kind, rank, `contradicts` form and sides, without the
  handles, which differ between the two KBs."
  [e]
  [(:kind e) (:priority e) (:sentence e)
   (into #{} (map (juxt :sentence :context :defeat-class)) (:sides e))])

(defn- snapshot [kb]
  {:believed   (into #{}
                     (comp (keep #(p/get-sentex (:records kb) %))
                           (map (juxt v/sentence-of :context)))
                     (jtms/in-datums (reasoning/tms kb)))
   :dilemmas   (into #{} (map clash-key) (v/contradictions kb))
   :conflicts  (into #{} (map clash-key) (v/conflicts kb))
   :violations (into #{} (map :violation) (v/violations kb))})

(defn- diff [a b]
  (into {} (keep (fn [k]
                   (let [x (get a k) y (get b k)]
                     (when (not= x y)
                       [k {:incremental-only (set/difference x y)
                           :exhaustive-only  (set/difference y x)}]))))
        (keys a)))

;; ---- oracle 1: randomized operation streams -----------------------------

(defn- trial-ops
  "`steps` ops of `seed`'s stream in arrival order `order`: 0 as drawn, any other a
  seeded shuffle of the same ops."
  [seed steps order]
  (let [rng (java.util.Random. (long seed))
        ops (vec (repeatedly steps #(rand-op rng)))]
    (if (zero? (long order))
      ops
      (let [l (java.util.ArrayList. ^java.util.Collection ops)]
        (java.util.Collections/shuffle l (java.util.Random. (+ (* 1000 (long seed)) (long order))))
        (vec l)))))

(defn- run-trial
  "`ops` into both KBs, comparing after every write.  Returns `[step op
  incremental-snapshot exhaustive-snapshot]` for the first divergence, or nil."
  [ops]
  (let [inc-kb (tu/fresh)
        exh-kb (tu/isolated-fresh)]
    (try
      (binding [checks/*arbitrate-constraints?* true]
        (binding [settle/*incremental-clashes* true]  (build-ontology! inc-kb))
        (binding [settle/*incremental-clashes* false] (build-ontology! exh-kb))
        (loop [step 0, [op & more] ops]
          (when op
            (let [ri (binding [settle/*incremental-clashes* true]  (apply-op! inc-kb op))
                  re (binding [settle/*incremental-clashes* false] (apply-op! exh-kb op))
                  si (snapshot inc-kb)
                  se (snapshot exh-kb)]
              (if (and (= ri re) (= si se))
                (recur (inc step) more)
                [step op si se])))))
      (finally (tu/clear-kb! inc-kb) (tu/clear-kb! exh-kb)))))

(defn- stream-reading
  "One KB's reading after `steps` of `seed`'s stream, on whatever retrieval strategy is
  bound around the call."
  [seed steps]
  (let [kb (tu/fresh)]
    (try
      (binding [checks/*arbitrate-constraints?* true
                settle/*incremental-clashes*    true]
        (build-ontology! kb)
        (let [rng (java.util.Random. (long seed))]
          (dotimes [_ steps] (apply-op! kb (rand-op rng))))
        (snapshot kb))
      (finally (tu/clear-kb! kb)))))

(deftest the-retrieval-strategy-does-not-change-what-clashes
  ;; `matches-visible` returns `(animal CI2)` beside the `(dog CI2)` that implies it, in
  ;; an order each retrieval path chooses, and `checks/membership-handles` names one of
  ;; them.  In the default suite because only the weekly `deep.yml` runs `VAELII_HIER=0`.
  (doseq [seed (range 4)]
    (is (= (binding [res/*hierarchical-retrieval* true]  (stream-reading seed 24))
           (binding [res/*hierarchical-retrieval* false] (stream-reading seed 24)))
        (str "seed " seed ": the retrieval strategy changed the clash reading"))))

(deftest the-lead-side-does-not-change-what-clashes
  ;; `checks/membership-handles` leads from the `matches-visible` reference under
  ;; `:scoped` and from the term's own postings under `:auto` / `:agnostic`, and
  ;; arbitration turns belief on the handle it names.
  (doseq [seed (range 4)]
    (let [scoped   (binding [res/*lead-side* :scoped]   (stream-reading seed 24))
          auto     (binding [res/*lead-side* :auto]     (stream-reading seed 24))
          agnostic (binding [res/*lead-side* :agnostic] (stream-reading seed 24))]
      (is (= scoped auto agnostic)
          (str "seed " seed ": the lead side changed the clash reading"
               "\n  scoped vs auto:     " (pr-str (diff scoped auto))
               "\n  scoped vs agnostic: " (pr-str (diff scoped agnostic)))))))

(deftest ^:slow randomized-streams-discover-the-same-clashes
  (doseq [seed (range 12), order (range 3)]
    (let [[step op si se] (run-trial (trial-ops seed 45 order))]
      (is (nil? step)
          (str "seed " seed " order " order " diverged at step " step " on " (pr-str op) "\n"
               (pr-str (diff si se)))))))

(deftest a-seeded-stream-discovers-the-same-clashes
  ;; one seed of the `^:slow` sweep, so `:default` runs the harness
  (let [[step op si se] (run-trial (trial-ops 0 45 0))]
    (is (nil? step)
        (str "seed 0 diverged at step " step " on " (pr-str op) "\n" (pr-str (diff si se))))))

;; ---- oracle 2: the retroactive declaration ------------------------------
;;
;; A separation arriving over content stored long before it: only the sweep finds the
;; pair, and a random stream may not draw the shape.

(deftest a-separation-arriving-last-finds-what-it-convicts
  (let [[step op si se]
        (let [inc-kb (tu/fresh)
              exh-kb (tu/isolated-fresh)]
          (try
            (binding [checks/*arbitrate-constraints?* true]
              (binding [settle/*incremental-clashes* true]  (build-ontology! inc-kb))
              (binding [settle/*incremental-clashes* false] (build-ontology! exh-kb))
              (let [pool inds
                    ops  (concat
                          ;; the memberships are out of the region when it lands
                          (for [x pool] [:assert (list 'dog x) (first ctxs) {}])
                          (for [x pool] [:assert (list 'cat x) (first ctxs) {}])
                          (for [x pool]
                            [:assert (list 'parentOf x (first pool)) (first ctxs) {}])
                          [[:assert '(disjoint dog cat) (first ctxs) {:strength :monotonic}]]
                          ;; and a settle after it, where a dropped pair would vanish
                          [[:assert (list 'plant (first pool)) (first ctxs) {}]])]
                (loop [step 0 [op & more] ops]
                  (if-not op
                    nil
                    (let [ri (binding [settle/*incremental-clashes* true]
                               (apply-op! inc-kb op))
                          re (binding [settle/*incremental-clashes* false]
                               (apply-op! exh-kb op))
                          si (snapshot inc-kb)
                          se (snapshot exh-kb)]
                      (if (and (= ri re) (= si se))
                        (recur (inc step) more)
                        [step op si se]))))))
            (finally (tu/clear-kb! inc-kb) (tu/clear-kb! exh-kb))))]
    (is (nil? step)
        (str "diverged at step " step " on " (pr-str op) "\n" (pr-str (diff si se))))))

;; ---- oracle 3: the carry-forward, under a moving vocabulary -------------
;;
;; A `genl` edge or a separation moving under standing memberships that sit still.

(deftest vocabulary-moving-under-standing-content-agrees
  (let [inc-kb (tu/fresh)
        exh-kb (tu/isolated-fresh)
        ops    [;; content first, and nothing about it moves again
                [:assert '(dog CI0)   'CxClashBase {}]
                [:assert '(snake CI0) 'CxClashBase {}]
                [:assert '(dog CI1)   'CxClashBase {}]
                [:assert '(cat CI1)   'CxClashBase {}]
                ;; …then the vocabulary moves under it, twice
                [:assert '(genl snake reptile) 'CxClashBase {:strength :monotonic}]
                [:assert '(disjoint dog cat)   'CxClashBase {:strength :monotonic}]
                ;; a settle that touches neither pair: both must still be reported
                [:assert '(plant CI4) 'CxClashBase {}]
                ;; and the separations leaving again
                [:retract '(disjoint dog cat) 'CxClashBase]
                [:retract '(genl snake reptile) 'CxClashBase]
                [:assert '(plant CI5) 'CxClashBase {}]]]
    (try
      (binding [checks/*arbitrate-constraints?* true]
        (binding [settle/*incremental-clashes* true]  (build-ontology! inc-kb))
        (binding [settle/*incremental-clashes* false] (build-ontology! exh-kb))
        (doseq [[i op] (map-indexed vector ops)]
          (let [ri (binding [settle/*incremental-clashes* true]  (apply-op! inc-kb op))
                re (binding [settle/*incremental-clashes* false] (apply-op! exh-kb op))
                si (snapshot inc-kb)
                se (snapshot exh-kb)]
            (is (= ri re) (str "step " i " " (pr-str op) ": refusal differs"))
            (is (= si se) (str "step " i " " (pr-str op) ": " (pr-str (diff si se)))))))
      (finally (tu/clear-kb! inc-kb) (tu/clear-kb! exh-kb)))))

;; ---- oracle 4: a genl edge, weighed per pair ----------------------------
;;
;; `settle/genl-view`'s four claims, one test each.  Oracle 3's edge sits under a type
;; its pair names, so a bare generation counter would pass it.

(defn- directed-stream
  "A fixed op sequence into both KBs, compared after every write."
  [ops]
  (let [inc-kb (tu/fresh)
        exh-kb (tu/isolated-fresh)]
    (try
      (binding [checks/*arbitrate-constraints?* true]
        (binding [settle/*incremental-clashes* true]  (build-ontology! inc-kb))
        (binding [settle/*incremental-clashes* false] (build-ontology! exh-kb))
        (doseq [[i op] (map-indexed vector ops)]
          (let [ri (binding [settle/*incremental-clashes* true]  (apply-op! inc-kb op))
                re (binding [settle/*incremental-clashes* false] (apply-op! exh-kb op))
                si (snapshot inc-kb)
                se (snapshot exh-kb)]
            (is (= ri re) (str "step " i " " (pr-str op) ": refusal differs"))
            (is (= si se) (str "step " i " " (pr-str op) ": " (pr-str (diff si se))))))
        (v/contradictions inc-kb))
      (finally (tu/clear-kb! inc-kb) (tu/clear-kb! exh-kb)))))

(deftest a-genl-edge-elsewhere-leaves-a-standing-pair-alone
  ;; the count at the end fails a memo that dropped every pair
  (let [cs (directed-stream
            [;; a standing pair on `mammal` / `reptile`, and nothing about it moves again
             [:assert '(mammal CI0)  'CxClashBase {}]
             [:assert '(reptile CI0) 'CxClashBase {}]
             ;; edges arriving and leaving under types the pair does not name
             [:assert '(genl snake reptile) 'CxClashBase {:strength :monotonic}]
             [:assert '(genl plant thing)   'CxClashBase {:strength :monotonic}]
             [:assert '(cat CI3) 'CxClashBase {}]
             [:retract '(genl plant thing) 'CxClashBase]
             [:retract '(genl snake reptile) 'CxClashBase]
             [:assert '(cat CI4) 'CxClashBase {}]])]
    (is (= 1 (count cs))
        "the pair the edges were never about is still the one standing dilemma")))

(deftest a-genl-edge-the-pair-rests-on-withdraws-it-when-it-goes
  ;; the clash `(dog CI0)` / `(plant CI0)` rests on `(genl mammal animal)`, an edge
  ;; between types neither sentence names, so a reading of the two functors alone would
  ;; carry the pair after the edge goes
  (directed-stream
   [[:assert '(dog CI0)   'CxClashBase {}]
    [:assert '(plant CI0) 'CxClashBase {}]
    ;; a settle that touches neither, so the pair is standing rather than arriving
    [:assert '(cat CI3) 'CxClashBase {}]
    ;; ...and the edge the separation reaches `dog` through goes
    [:retract '(genl mammal animal) 'CxClashBase]
    [:assert '(cat CI4) 'CxClashBase {}]
    ;; and comes back, so the pair has to be found a second time
    [:assert '(genl mammal animal) 'CxClashBase {:strength :monotonic}]
    [:assert '(cat CI5) 'CxClashBase {}]]))

(deftest an-edge-relating-two-supertypes-withdraws-their-separation
  ;; `clsh_amphi_t` stands under both `clsh_car_t` and `clsh_boat_t`, so the closing edge
  ;; between them moves neither member's closure.  `tax/disjointness-test`'s
  ;; genl-relatedness guard reads that edge.  In the sibling row the exceptions leave the
  ;; pair of the two supertypes as the one separating the members.
  (doseq [[arm decls]
          {:sibling '[(sibling_disjoint clsh_craft_t)
                      (genl clsh_car_t clsh_craft_t)
                      (genl clsh_boat_t clsh_craft_t)
                      (siblingDisjointException clsh_amphi_t clsh_yacht_t)
                      (siblingDisjointException clsh_car_t clsh_yacht_t)]
           :metatype '[(disjoint_metatype clsh_kind_t)
                       (clsh_kind_t clsh_car_t)
                       (clsh_kind_t clsh_boat_t)]
           :partition '[(partition clsh_craft_t clsh_car_t clsh_boat_t)]}]
    (let [m   {:strength :monotonic}
          ops (-> (mapv (fn [d] [:assert d 'CxClashBase m]) decls)
                  (into [[:assert '(genl clsh_amphi_t clsh_car_t) 'CxClashBase m]
                         [:assert '(genl clsh_amphi_t clsh_boat_t) 'CxClashBase m]
                         [:assert '(genl clsh_yacht_t clsh_boat_t) 'CxClashBase m]
                         [:assert '(clsh_amphi_t CI0) 'CxClashBase {}]
                         [:assert '(clsh_yacht_t CI0) 'CxClashBase {}]
                         ;; a settle that touches neither, so the pair is standing
                         [:assert '(cat CI3) 'CxClashBase {}]]))
          end (into ops [[:assert '(genl clsh_car_t clsh_boat_t) 'CxClashBase m]
                         [:assert '(cat CI4) 'CxClashBase {}]])]
      (is (= 1 (count (directed-stream ops))) (str arm ": the pair stands before the edge"))
      (is (empty? (directed-stream end)) (str arm ": the edge leaves nothing separating it")))))

(deftest an-edge-two-contexts-support-is-read-from-each-of-them
  ;; the edge keeps its `CxClashSub` supporter, so the relation stands while the base
  ;; context's pair loses its separation: `settle/scoped-reading`'s case
  (directed-stream
   [[:assert '(genl mammal animal) 'CxClashSub {:strength :monotonic}]
    [:assert '(dog CI0)   'CxClashBase {}]
    [:assert '(plant CI0) 'CxClashBase {}]
    [:assert '(dog CI1)   'CxClashSub {}]
    [:assert '(plant CI1) 'CxClashSub {}]
    [:assert '(cat CI3) 'CxClashBase {}]
    ;; the base supporter goes; the sub one keeps the edge alive
    [:retract '(genl mammal animal) 'CxClashBase]
    [:assert '(cat CI4) 'CxClashBase {}]]))

(deftest a-metatype-member-leaving-withdraws-what-it-was-separating
  ;; a member arriving reaches its pairs through the sweep; a member leaving moves only
  ;; `clash-vocabulary`'s membership map
  (let [kb  (tu/fresh)
        exh (tu/isolated-fresh)
        ops [[:assert '(disjoint_metatype clsh_kind_t) 'CxClashBase {:strength :monotonic}]
             [:assert '(clsh_kind_t clsh_a_t) 'CxClashBase {:strength :monotonic}]
             [:assert '(clsh_a_t CI0) 'CxClashBase {}]
             [:assert '(clsh_b_t CI0) 'CxClashBase {}]
             ;; the member arrives over content already stored, and must reach it
             [:assert '(clsh_kind_t clsh_b_t) 'CxClashBase {:strength :monotonic}]
             ;; a settle that touches neither member of the pair
             [:assert '(plant CI4) 'CxClashBase {}]
             ;; ...and the member goes again, with the mark still standing
             [:retract '(clsh_kind_t clsh_b_t) 'CxClashBase]
             [:assert '(plant CI5) 'CxClashBase {}]]]
    (try
      (binding [checks/*arbitrate-constraints?* true]
        (doseq [[i op] (map-indexed vector ops)]
          (let [ri (binding [settle/*incremental-clashes* true]  (apply-op! kb op))
                re (binding [settle/*incremental-clashes* false] (apply-op! exh op))]
            (is (= ri re) (str "step " i " " (pr-str op) ": refusal differs"))
            (is (= (snapshot kb) (snapshot exh))
                (str "step " i " " (pr-str op) ": "
                     (pr-str (diff (snapshot kb) (snapshot exh)))))))
        (is (zero? (count (v/contradictions kb)))
            "with the member gone the two types are separated by nothing"))
      (finally (tu/clear-kb! kb) (tu/clear-kb! exh)))))

(deftest the-contradictions-list-is-ordered-by-content-not-arrival
  ;; three independent dilemmas in three assertion orders; the nogoods are handle-keyed
  (let [pairs  '[[(clsh_p CA) (not (clsh_p CA))]
                 [(clsh_q CB) (not (clsh_q CB))]
                 [(clsh_r CC) (not (clsh_r CC))]]
        read!  (fn [sentences]
                 (let [kb (tu/fresh)]
                   (try
                     (doseq [s sentences] (v/assert kb s 'CxClashBase))
                     (mapv (fn [r] (mapv :sentence (:sides r))) (v/contradictions kb))
                     (finally (tu/clear-kb! kb)))))
        fwd    (read! (apply concat pairs))
        rev    (read! (apply concat (reverse pairs)))
        rot    (read! (apply concat (take 3 (drop 1 (cycle pairs)))))]
    (is (= 3 (count fwd)) "three standing dilemmas")
    (is (= fwd rev rot) "every assertion order publishes one list")
    (is (= fwd (vec (sort-by pr-str fwd))) "and it is the content order, stated directly")))

(deftest a-sides-derivations-are-ordered-by-content-not-arrival
  ;; the derivations inside a side come off `jtms/supports`, a set of allocation-ordered
  ;; ids.  The two arms share one term set, since the readings are compared as values.
  (tu/with-terms [seenA seenB derivedQ Subject CxBase]
    (let [ops   {:fA  #(v/assert % (list seenA Subject) CxBase)
                 :fB  #(v/assert % (list seenB Subject) CxBase)
                 :r1  #(v/assert-rule % [(list seenA '?x)] (list derivedQ '?x) CxBase {:direction :forward})
                 :r2  #(v/assert-rule % [(list seenB '?x)] (list derivedQ '?x) CxBase {:direction :forward})
                 :neg #(v/assert % (list 'not (list derivedQ Subject)) CxBase)}
          sent  (fn [kb x] (if (integer? x) (v/sentence-of (v/sentex kb x)) x))
          read! (fn [order]
                  (let [kb (tu/fresh)]
                    (try
                      (doseq [o order] ((ops o) kb))
                      (mapv (fn [report]
                              (mapv (fn [side]
                                      [(:sentence side)
                                       (mapv (fn [j] [(sent kb (:informant j))
                                                      (mapv #(sent kb %) (:antecedents j))])
                                             (:justifications side))])
                                    (:sides report)))
                            (v/contradictions kb))
                      (finally (tu/clear-kb! kb)))))
          fwd   (read! [:r1 :r2 :fA :fB :neg])
          rev   (read! [:neg :fB :fA :r2 :r1])]
      (is (= 1 (count fwd)) "one standing dilemma")
      (is (some (fn [[_ js]] (= 2 (count js))) (first fwd))
          "and one side of it is derived twice — else there is no list to order")
      (is (= fwd rev) "every assertion order publishes one reading"))))

;; ---- oracle 5: a merge moves which spellings a reader reads ---------------

(deftest a-merge-and-its-retraction-move-the-pairs-the-spellings-form
  ;; `(rewriteOf CI2 CI3)` makes `CI2` the representative, so a reader below it retires the
  ;; `CI3` spellings without relabelling or superseding them.  Declared before that merge,
  ;; the separation convicts a pair the merge then withdraws; declared after it, the
  ;; separation convicts nothing until the merge is retracted
  (let [[a b c m1 sep m2 & tail]
        '[[:assert (reptile CI2) CxClashSub {}]
          [:assert (pet CI1) CxClashSub {}]
          [:assert (cat CI1) CxClashSub {}]
          [:assert (rewriteOf CI3 CI1) CxClashBase {:strength :monotonic}]
          [:assert (disjoint dog cat) CxClashBase {:strength :monotonic}]
          [:assert (rewriteOf CI2 CI3) CxClashBase {:strength :monotonic}]
          [:retract (rewriteOf CI2 CI3) CxClashBase]
          ;; a settle that touches none of the spellings
          [:assert (plant CI4) CxClashBase {}]]]
    (doseq [order [[a b c m1 sep m2] [a b c m1 m2 sep] [m1 m2 sep c b a]]]
      (directed-stream (into order tail)))))

;; ---- the argument-root readers are total --------------------------------

(deftest a-sentence-with-no-arity-on-an-argument-root-is-skipped-not-counted
  ;; an arity-less sentence reaching `count` would throw out of the settle.  `reify`
  ;; stores, since a protocol-method redef intercepts nothing (testing.md).
  (let [tms (jtms/create-tms)
        recs #_{:clj-kondo/ignore [:missing-protocol-method]}
        (reify p/RecordStore
          (get-sentex [_ id]
            (case (long id)
              1 {:id 1 :sentence 'clshArityless    :context 'CxUniverse}
              2 {:id 2 :sentence '(clsh_member CK)  :context 'CxUniverse}
              nil)))
        idx #_{:clj-kondo/ignore [:missing-protocol-method]}
        (reify p/IndexStore
          (sentexes-with-arg [_ _pos _term] [1 2]))
        fake {:records recs :index idx :reasoning (volatile! {:tms tms})}]
    (jtms/add-premise tms 1 :monotonic)
    (jtms/add-premise tms 2 :monotonic)
    (is (false? (@#'settle/holds-two-members? fake '{clsh_member #{clsh_member}} 'CK))
        "the arity-less posting is skipped, and one real membership is not two members")))

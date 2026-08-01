(ns vaelii.clash-oracle-test
  "Incremental clash discovery finds the same nogoods an exhaustive pass does.

  `settle` has to know which pairs of believed sentexes violate a separation, a
  `functional` or an `asymmetric` declaration — and that question is exhaustive by
  nature: every believed sentex against every other.  Asking it that way costs an
  `arbitrable-violations` call per believed sentex per settle, and a settle runs after
  every mutation, so a KB would load its own content in quadratic time.

  So the engine narrows it three ways, and each narrowing is a *claim* that what it
  skips cannot have changed the answer:

  * **region + remembered pairs** (`clash-candidates`) — only what this settle moved,
    plus every pair already known to clash, plus what a declaration arriving in the
    region puts retroactively back in question;
  * **`could-clash?`** — a sentex that cannot be half of any pair is dropped before the
    check runs, on an O(1) root cardinality or property read;
  * **carry-forward** — a known pair neither of whose members moved keeps last settle's
    answer, priority and all.

  A wrong narrowing is not a crash.  It is a dilemma that stops being reported, or a
  defeat that stops being applied, on a KB that looks entirely healthy — the failure
  mode a unit test written against a hand-built scenario is worst at catching, because
  the scenario names the very pair the narrowing would have to skip to be wrong.

  `settle/*incremental-clashes*` bound to `false` is the exhaustive question, asked in
  full on every settle.  These tests run the same operation sequence into two KBs, one
  each way, and compare **after every step**: believed content, the dilemmas, the
  conflicts, and whether the write was refused at all.  Step-by-step rather than at the
  end, so a divergence names the operation that caused it rather than the run.

  Both KBs run under `checks/*arbitrate-constraints?*`, because that is the policy under
  which the claim is true.  With it off the assert path *refuses* a clash instead of
  admitting it, and the retroactive sweeps do not run — a declaration arriving over
  content stored long before it is deliberately left to the exposure pass — so the two
  discoveries answer different questions and comparing them would prove nothing.

  **Conviction has to be symmetric for the claim to hold**, and the streams here are
  built so it is.  The discovery checks the sentexes the settle *moved*; where each side
  of a pair convicts the other that is enough, because whichever side arrives second
  finds the pair.  Two shapes convict one-way only, and both are excluded here because
  the incremental path is order-dependent on them for reasons that have nothing to do
  with the three narrowings above — see docs/nmtms.md, \"Where conviction is one-sided\":

  * **across a visibility edge** — `(animal X)` in a general microtheory and `(plant X)`
    in one that sees it.  Only the seeing side's check can see both.  So each term's
    content is written in exactly one context here.
  * **through argument preservation** — `(outranks animal cat)` denies the more specific
    `(outranks cat reptile)`, and preservation reads a goal's arguments upwards, so the
    specific claim asks about the general one and never the reverse.  So no
    `argPreserving` declaration is made here.

  Both are open questions about *which* sentexes a settle owes a re-check, not about
  whether the narrowings are sound, and the exhaustive reference does not share either —
  a stream generating them would measure the open question instead of the three claims.

  **What this reaches, checked by breaking it.**  Disabling either arm of `could-clash?`,
  forgetting the remembered pairs, or skipping the retroactive sweep each turns these
  streams red.  One mechanism it cannot reach is the carry-forward's `moved?` predicate,
  and the reason is worth stating rather than leaving as a gap: a pair whose member the
  region holds is re-derived through the region anyway, and the fresh answer *overrides*
  the carried one, so within a single context `moved?` decides nothing that `stale?` and
  that override do not already decide.  It earns its keep only by handing the untouched
  member back as a candidate — which matters exactly where conviction is one-sided, and
  that is the regime excluded above.  `lein perf`'s `clash-arbitration` check is what
  holds it from the other side, since carrying is what keeps a settle off the standing
  set."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.settle :as settle]
            [vaelii.test-util :as tu]))

;; ---- the shared ontology ------------------------------------------------

(def ^:private ctxs '[ClashBaseContext ClashSubContext])

(def ^:private types
  '[animal mammal reptile dog cat snake plant])

(def ^:private inds
  "One block of individuals per context.  A term is only ever written where its block
  says, so no pair straddles the `genlContext` edge (see the namespace docstring)."
  {'ClashBaseContext '[CI0 CI1 CI2]
   'ClashSubContext  '[CI3 CI4 CI5]})

(defn- build-ontology!
  "A hierarchy deep enough that a separation closes over several levels, two contexts so
  the scoping is exercised, and one declaration of each arbitrable kind.

  Deliberately *incomplete*: `(disjoint dog cat)` and `(genl snake animal)` are left for
  the operation stream to assert, since a declaration arriving over content already
  stored is the case the retroactive sweep exists for and the case a region-only
  discovery would miss.

  **Two rules concluding one literal**, so a clashing membership can be *derived* and can
  hold two justifications at once.  That is what lets a standing pair's `:priority` move
  while both its handles sit still: a second route arriving from a `:monotonic` premise
  lifts the conclusion's defeat class without storing anything new about it, which is the
  one thing the carry-forward has to notice and the one thing an all-premise stream can
  never produce."
  [kb]
  (v/with-deferred-settle kb
    (v/assert kb (list 'genlContext (second ctxs) (first ctxs)) 'UniverseContext)
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
  "One write, drawn to hit every route a clash can arrive by: a membership that
  separates against another, a second value for a functional slot, a converse of an
  asymmetric claim, a retraction that can revive a defeated loser, a premise whose rule
  *derives* a clashing membership (and a second premise giving that conclusion a stronger
  second route), and — the retroactive cases — a separation or a genl edge arriving after
  the content it convicts."
  [^java.util.Random rng]
  (let [ctx  (nth ctxs (.nextInt rng (count ctxs)))
        pool (inds ctx)
        ind  #(nth pool  (.nextInt rng (count pool)))
        typ  #(nth types (.nextInt rng (count types)))
        str8 #(if (zero? (.nextInt rng 3)) {:strength :monotonic} {})]
    (case (.nextInt rng 13)
      (0 1 2) [:assert (list (typ) (ind)) ctx (str8)]
      (3 4)   [:assert (list 'ageOf (ind) (.nextInt rng 4)) ctx (str8)]
      (5 6)   [:assert (list 'parentOf (ind) (ind)) ctx (str8)]
      7       [:retract (list (typ) (ind)) ctx]
      8       [:assert '(disjoint dog cat) (first ctxs) {:strength :monotonic}]
      9       [:assert '(genl snake animal) (first ctxs) {:strength :monotonic}]
      (10 11) [:assert (list (if (even? (.nextInt rng 2)) 'pet 'canine) (ind)) ctx (str8)]
      12      [:retract (list (if (even? (.nextInt rng 2)) 'pet 'canine) (ind)) ctx])))

(defn- apply-op!
  "Run one op, reporting the refusal rather than propagating it — a refusal is an
  observation the two KBs must agree on, not a reason to stop the trial."
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
  "A reported pair as content: the kind, the rank, the `contradicts` form (already
  content-ordered by the discovery) and both sides.  Handles are dropped — they are
  allocated in arrival order and the two KBs are compared on what they believe, not on
  where they put it."
  [e]
  [(:kind e) (:priority e) (:sentence e)
   (into #{} (map (juxt :sentence :context :defeat-class)) (:sides e))])

(defn- snapshot [kb]
  {:believed   (into #{}
                     (comp (keep #(p/get-sentex (:records kb) %))
                           (map (juxt :sentence :context :truth)))
                     (jtms/in-datums (:tms kb)))
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

(defn- run-trial
  "The same op stream into both KBs, comparing after every write.  Returns
  `[step op incremental-snapshot exhaustive-snapshot]` for the first divergence, or nil."
  [seed steps]
  (let [inc-kb (tu/fresh)
        exh-kb (tu/isolated-fresh)]
    (try
      (binding [checks/*arbitrate-constraints?* true]
        (binding [settle/*incremental-clashes* true]  (build-ontology! inc-kb))
        (binding [settle/*incremental-clashes* false] (build-ontology! exh-kb))
        (let [rng (java.util.Random. (long seed))]
          (loop [step 0]
            (if (= step steps)
              nil
              (let [op (rand-op rng)
                    ri (binding [settle/*incremental-clashes* true]  (apply-op! inc-kb op))
                    re (binding [settle/*incremental-clashes* false] (apply-op! exh-kb op))
                    si (snapshot inc-kb)
                    se (snapshot exh-kb)]
                (if (and (= ri re) (= si se))
                  (recur (inc step))
                  [step op si se]))))))
      (finally (tu/clear-kb! inc-kb) (tu/clear-kb! exh-kb)))))

(deftest randomized-streams-discover-the-same-clashes
  (doseq [seed (range 12)]
    (let [[step op si se] (run-trial seed 45)]
      (is (nil? step)
          (str "seed " seed " diverged at step " step " on " (pr-str op) "\n"
               (pr-str (diff si se)))))))

;; ---- oracle 2: the retroactive declaration ------------------------------
;;
;; The narrowing most likely to be wrong, isolated: a separation arriving over content
;; stored long before it.  Neither membership is in the settle's region and the pair is
;; not yet remembered, so the *only* thing that finds it is the sweep — and a randomized
;; stream that happened not to generate this shape would report a clean run.

(deftest a-separation-arriving-last-finds-what-it-convicts
  (let [[step op si se]
        (let [inc-kb (tu/fresh)
              exh-kb (tu/isolated-fresh)]
          (try
            (binding [checks/*arbitrate-constraints?* true]
              (binding [settle/*incremental-clashes* true]  (build-ontology! inc-kb))
              (binding [settle/*incremental-clashes* false] (build-ontology! exh-kb))
              (let [pool (inds (first ctxs))
                    ops  (concat
                          ;; a dozen settles' worth of unrelated traffic, so the two
                          ;; memberships are long out of the region by the time the
                          ;; declaration lands
                          (for [x pool] [:assert (list 'dog x) (first ctxs) {}])
                          (for [x pool] [:assert (list 'cat x) (first ctxs) {}])
                          (for [x pool]
                            [:assert (list 'parentOf x (first pool)) (first ctxs) {}])
                          [[:assert '(disjoint dog cat) (first ctxs) {:strength :monotonic}]]
                          ;; and one more settle after it, which is where a pair that was
                          ;; found once and then dropped would silently vanish
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
;; A pair is carried forward when neither member moved *and* the clash vocabulary is
;; unchanged.  The second half is the one with a long reach: a `genl` edge can make two
;; standing memberships clash without either of them being written, and a retracted
;; separation can stop a standing pair clashing the same way.  Both are vocabulary
;; movements over pairs whose members sit perfectly still.

(deftest vocabulary-moving-under-standing-content-agrees
  (let [inc-kb (tu/fresh)
        exh-kb (tu/isolated-fresh)
        ops    [;; content first, and nothing about it moves again
                [:assert '(dog CI0)   'ClashBaseContext {}]
                [:assert '(snake CI0) 'ClashBaseContext {}]
                [:assert '(dog CI1)   'ClashBaseContext {}]
                [:assert '(cat CI1)   'ClashBaseContext {}]
                ;; …then the vocabulary moves under it, twice
                [:assert '(genl snake reptile) 'ClashBaseContext {:strength :monotonic}]
                [:assert '(disjoint dog cat)   'ClashBaseContext {:strength :monotonic}]
                ;; a settle that touches neither pair: both must still be reported
                [:assert '(plant CI4) 'ClashBaseContext {}]
                ;; and the separations leaving again
                [:retract '(disjoint dog cat) 'ClashBaseContext]
                [:retract '(genl snake reptile) 'ClashBaseContext]
                [:assert '(plant CI5) 'ClashBaseContext {}]]]
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

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.taxonomy-depth-test
  "The `genl` / `genlContext` **depth potential** — the topological ranking that lets
  `reachable?` reject most pairs in O(1) — and what a deferred batch does to it.

  The potential is derived state with one invariant, over the **condensation**:
  `edge x→y ⇒ depth[x] > depth[y]`, except inside a strongly connected component,
  where the two are equal and mutual reachability is read off `:scc` instead.  Every
  test here checks reads against the invariant rather than against particular depth
  numbers, because the numbers legitimately differ between an incremental build
  (`raise-depth` / `local-lift`, which only ever grow a depth) and a from-scratch one
  (`repair-depths`, which computes each component's exact height).  What must never
  differ is the answers.

  Three costs are in tension and each has its own test:

    * repairing per edge is O(that edge's descendants) — quadratic when edges arrive
      child-first, which is why a batch defers it;
    * a `:loose?` relation makes every read an unpruned walk, and `wff` runs one per
      taxonomy edge asserted — which is why deferring must not simply go loose;
    * `local-lift` is the middle: O(1) plus the source's in-degree, sound for the
      parent-before-child order a hierarchy usually arrives in."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

;; ---- reading the potential ----------------------------------------------

(defn- rel [t k] (get @t k))

(defn- violations
  "Active edges the potential does not rank — the invariant, as data.  An edge inside
  a component is ranked by being *level*: the potential ranks the condensation, and
  within one component there is nothing to rank."
  [t k]
  (let [{:keys [edges depth scc]} (rel t k)
        same-comp? (fn [a b] (let [ca (get scc a)] (and (some? ca) (= ca (get scc b)))))]
    (into #{} (remove (fn [[a b]]
                        (if (same-comp? a b)
                          (= (get depth a -1) (get depth b -1))
                          (> (get depth a -1) (get depth b -1)))))
          edges)))

(defn- sound? [t k] (empty? (violations t k)))
(defn- loose? [t k] (boolean (:loose? (rel t k))))

(defn- ty [i] (symbol (str "d" i "_t")))
(defn- ctx [i] (symbol (str "D" i "Context")))

(defn- chain-edges
  "A `d0 ← d1 ← … ← dn` chain as `[sub super handle]` triples, parent-first (the order
  a hierarchy is normally written in) or child-first (`raise-depth`'s worst case)."
  [n order]
  (let [es (map (fn [i] [(ty i) (ty (dec i)) i]) (range 1 (inc n)))]
    (if (= :child-first order) (reverse es) es)))

(defn- build
  "A taxonomy holding `edges`, inserted eagerly or under `*defer-depths?*`."
  [edges defer?]
  (let [t (tax/create-taxonomy)]
    (binding [tax/*defer-depths?* defer?]
      (doseq [[a b h] edges] (tax/add-genl t a b h)))
    t))

;; ---- the invariant, whichever way the edges arrive -----------------------

(deftest a-deferred-batch-leaves-a-potential-that-ranks-every-edge
  (doseq [order [:parent-first :child-first]
          :let  [edges (chain-edges 40 order)]]
    (testing (str "eager insert keeps the invariant — " order)
      (is (sound? (build edges false) :genl)))
    (testing (str "deferred insert plus one repair keeps it — " order)
      (let [t (build edges true)]
        (tax/restore-depths t)
        (is (sound? t :genl))
        (is (not (loose? t :genl)) "the repair clears the loose mark")))))

(deftest parent-first-arrival-never-goes-loose
  ;; The whole point of `local-lift`: a hierarchy loaded the way hierarchies are
  ;; written keeps a sound potential *during* the batch, so reads stay pruned.  A
  ;; blanket `:loose?` would have made every `wff` cycle check walk unpruned instead.
  (let [t (build (chain-edges 40 :parent-first) true)]
    (is (not (loose? t :genl)))
    (is (sound? t :genl) "sound without any repair having run"))
  (testing "a wide shallow hierarchy — every child of one root — stays sound too"
    (let [t (build (map (fn [i] [(ty i) (ty 0) i]) (range 1 40)) true)]
      (is (not (loose? t :genl)))
      (is (sound? t :genl))))
  (testing "child-first arrival is the case that does go loose, and reads survive it"
    (let [t (build (chain-edges 40 :child-first) true)]
      (is (loose? t :genl))
      (is (tax/genl? t (ty 40) (ty 0)) "reachability is answered unpruned, not wrongly")
      (is (not (tax/genl? t (ty 0) (ty 40))))
      (is (= (into #{} (map ty) (range 0 41)) (tax/genls t (ty 40)))))))

(deftest genlContext-gets-the-same-treatment-as-genl
  ;; Both relations run through one `activate`, so the deferral covers both — and
  ;; `genlContext` is the one that matters most for a corpus load, whose topology file
  ;; is written depth-sorted, i.e. exactly parent-first.
  (let [edges (map (fn [i] [(ctx i) (ctx (dec i)) i]) (range 1 41))
        build-ctx (fn [es defer?]
                    (let [t (tax/create-taxonomy)]
                      (binding [tax/*defer-depths?* defer?]
                        (doseq [[a b h] es] (tax/add-genlContext t a b h)))
                      t))]
    (testing "parent-first stays sound with no repair"
      (let [t (build-ctx edges true)]
        (is (not (loose? t :genlContext)))
        (is (sound? t :genlContext))
        (is (tax/sees? t (ctx 40) (ctx 0)))))
    (testing "child-first goes loose, reads survive, and the repair fixes it"
      (let [t (build-ctx (reverse edges) true)]
        (is (loose? t :genlContext))
        (is (tax/sees? t (ctx 40) (ctx 0)))
        (is (not (tax/sees? t (ctx 0) (ctx 40))))
        (tax/restore-depths t)
        (is (sound? t :genlContext))
        (is (not (loose? t :genlContext)))
        (is (tax/sees? t (ctx 40) (ctx 0)))))
    (testing "the two relations go loose independently"
      (let [t (tax/create-taxonomy)]
        (binding [tax/*defer-depths?* true]
          (doseq [[a b h] (reverse edges)] (tax/add-genlContext t a b h))   ; child-first
          (doseq [[a b h] (chain-edges 40 :parent-first)] (tax/add-genl t a b h)))
        (is (loose? t :genlContext))
        (is (not (loose? t :genl)) "a loose genlContext does not drag genl down with it")
        (tax/restore-depths t)
        (is (sound? t :genl))
        (is (sound? t :genlContext))))))

(deftest deferred-and-eager-agree-whatever-the-arrival-order
  ;; Belief must not depend on arrival order.  Depth *numbers* may; the relation the
  ;; potential prunes must not.
  (let [n     30
        base  (chain-edges n :parent-first)
        pairs (for [a (range 0 (inc n)) b (range 0 (inc n))] [(ty a) (ty b)])
        answers (fn [t] (into #{} (filter (fn [[a b]] (tax/genl? t a b))) pairs))
        want  (answers (build base false))]
    (doseq [trial (range 6)
            :let  [order (shuffle base)]]
      (testing (str "shuffled order " trial)
        (is (= want (answers (build order false))) "eager")
        (is (= want (answers (build order true)))  "deferred, mid-batch")
        (let [t (build order true)]
          (tax/restore-depths t)
          (is (= want (answers t)) "deferred, after the repair")
          (is (sound? t :genl)))))))

(deftest a-repair-is-idempotent-and-free-when-nothing-is-loose
  (let [t (build (chain-edges 20 :child-first) true)]
    (is (loose? t :genl))
    (tax/restore-depths t)
    (let [after (:depth (rel t :genl))]
      (tax/restore-depths t)
      (tax/restore-depths t)
      (is (= after (:depth (rel t :genl))))
      (is (sound? t :genl)))))

(deftest an-insert-onto-a-loose-relation-does-not-build-on-the-stale-potential
  ;; `activate` reads `:loose?`, not just the dynamic var: an eager insert arriving
  ;; while the potential is unrepaired must not run `raise-depth` on a stale base
  ;; (its termination argument rests on a cycle check made *with* that base), and
  ;; must not silently re-enable pruning.
  (let [t      (build (chain-edges 20 :child-first) true)
        before (:depth (rel t :genl))]
    (is (loose? t :genl))
    ;; a new *supertype* above the chain's root: the one shape whose eager repair
    ;; would push a lift down through every node already in the relation
    (tax/add-genl t (ty 0) 'droot_t 999)              ; eager: *defer-depths?* is false
    (is (= before (dissoc (:depth (rel t :genl)) 'droot_t))
        "nothing moved — pushing a lift through a stale potential is work that repairs
         nothing, and the cycle check licensing it was made with that same stale base")
    (is (loose? t :genl) "still loose — the repair is `restore-depths`'s to make")
    (is (tax/genl? t (ty 20) 'droot_t) "and the read is still right")
    (tax/restore-depths t)
    (is (sound? t :genl))
    (is (tax/genl? t (ty 20) 'droot_t))))

(deftest a-cycle-is-ranked-as-one-component
  ;; `wff` refuses a cyclic `genl` edge, but the *taxonomy* must hold one anyway: a
  ;; `genlContext` cycle is admitted, and a rebuild replays whatever is stored either
  ;; way.  The pass condenses, so it terminates **and** leaves a sound potential —
  ;; the members level with each other, everything else strictly ranked around them —
  ;; and the depth-pruned reads stay exact, which the old raw-graph pass could not
  ;; promise.
  (let [t (tax/create-taxonomy)]
    (binding [tax/*defer-depths?* true]
      (tax/add-genl t 'ca_t 'cb_t 1)
      (tax/add-genl t 'cb_t 'cc_t 2)
      (tax/add-genl t 'cc_t 'ca_t 3)                  ; closes the cycle
      (tax/add-genl t 'cd_t 'ca_t 4)                  ; below it
      (tax/add-genl t 'cc_t 'ce_t 5))                 ; above it
    (tax/restore-depths t)                            ; terminates, which was the claim
    (is (sound? t :genl) "the potential ranks the condensation")
    (is (not (loose? t :genl)))
    (testing "the cycle is one component, level with itself"
      (let [{:keys [depth scc]} (rel t :genl)]
        (is (= 1 (count (distinct (map scc '[ca_t cb_t cc_t])))))
        (is (every? some? (map scc '[ca_t cb_t cc_t])))
        (is (nil? (scc 'cd_t)) "a lone node is in no component")
        (is (apply = (map depth '[ca_t cb_t cc_t])))
        (is (> (depth 'cd_t) (depth 'ca_t)))
        (is (> (depth 'ca_t) (depth 'ce_t)))))
    (testing "and the pruned reads answer the cycle exactly"
      (is (= '#{ca_t cb_t cc_t ce_t} (tax/genls t 'ca_t)) "reach stays cycle-safe")
      (is (= '#{ca_t cb_t cc_t cd_t} (tax/specs t 'ca_t)))
      (is (tax/genl? t 'ca_t 'cc_t))
      (is (tax/genl? t 'cc_t 'ca_t) "mutual, and answered without a walk")
      (is (tax/genl? t 'cd_t 'ce_t) "through the whole component")
      (is (not (tax/genl? t 'ce_t 'ca_t))))))

(deftest a-belief-move-remakes-a-component-and-surrenders-the-potential
  ;; `refresh-beliefs` is the one path that changes the active edge set with no sentex
  ;; added or removed, and it can move a component both ways: an edge leaving one
  ;; dissolves it, an edge revived into a cycle closes a new one.  Either way the
  ;; relation goes loose and the repair is owed — which is why `settle` cannot repair
  ;; only *before* it reconciles belief (the KB test at the end of this file).
  (let [t   (tax/create-taxonomy)
        scc #(:scc (rel t :genlContext))]
    (tax/add-genlContext t 'CyAContext 'CyBContext 1)
    (tax/add-genlContext t 'CyBContext 'CyAContext 2)
    (tax/restore-depths t)
    (is (= 1 (count (distinct (map (scc) '[CyAContext CyBContext])))))
    (testing "the edge leaving dissolves the component"
      (tax/refresh-beliefs t #(not= % 2))
      (is (loose? t :genlContext))
      (is (empty? (scc)) "not trusted: a split is the one staleness that answers true")
      (tax/restore-depths t)
      (is (empty? (scc)) "and there is genuinely no component to find"))
    (testing "and it coming back closes one again"
      (tax/refresh-beliefs t (constantly true))
      (is (loose? t :genlContext) "the reconcile surrendered the potential")
      (tax/restore-depths t)
      (is (sound? t :genlContext))
      (is (= 1 (count (distinct (map (scc) '[CyAContext CyBContext]))))
          "one component again, and one name for it"))))

;; ---- the same thing through the KB ---------------------------------------

(defn- kb-sound? [kb] (and (sound? (:taxonomy kb) :genl)
                           (sound? (:taxonomy kb) :genlContext)))

(tu/deftest-kb a-batch-through-the-kb-leaves-a-sound-potential
  (tu/with-terms [a_t b_t c_t]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl a_t b_t) 'UniverseContext)
      (v/assert kb (list 'genl b_t c_t) 'UniverseContext))
    (is (kb-sound? kb))
    (is (not (loose? (:taxonomy kb) :genl)))
    (is (v/genl? kb a_t c_t))))

(tu/deftest-kb an-aborted-batch-still-repairs-the-depth-potential
  ;; The settle that would have repaired never runs — a cancelled load is exactly this
  ;; shape — so the macro repairs on the way out.  Left loose, every later `genl?` and
  ;; `sees?` would walk unpruned for the life of the KB.
  (tu/with-terms [p_t q_t r_t s_t]
    (is (thrown? clojure.lang.ExceptionInfo
                 (v/with-deferred-settle kb
                   ;; child-first, so the batch is genuinely loose when it aborts
                   (v/assert kb (list 'genl r_t s_t) 'UniverseContext)
                   (v/assert kb (list 'genl q_t r_t) 'UniverseContext)
                   (v/assert kb (list 'genl p_t q_t) 'UniverseContext)
                   (throw (ex-info "cancelled" {:type :cancelled})))))
    (is (not (loose? (:taxonomy kb) :genl)) "repaired on the way out")
    (is (kb-sound? kb))
    (is (v/genl? kb p_t s_t) "and everything the batch did land is still reachable")))

(tu/deftest-kb a-revived-context-cycle-is-one-place-to-stand-again-in-its-own-settle
  ;; Two contexts that see each other are **one** place for a firing to put its
  ;; conclusion, and which of their names stands for the group is read off `:scc`
  ;; (`placement-rep`).  Both a defeat and a revival surrender the potential, so a settle
  ;; repairing only *before* it reconciles belief would leave the cycle standing with
  ;; `:scc` empty — the group collapsing to whichever member the caller happened to name
  ;; until some later settle repaired it.  That is how many settles have run deciding
  ;; where a conclusion lands, which is exactly what content-keyed placement exists to
  ;; rule out (docs/contexts.md).
  (tu/with-terms [AlphaContext BetaContext]
    (let [tx    (:taxonomy kb)
          place #(tax/maximal-common-descendant-contexts tx [%])]
      (v/assert kb (list 'genlContext BetaContext AlphaContext) 'UniverseContext)
      (v/assert kb (list 'genlContext AlphaContext BetaContext) 'UniverseContext)
      (let [group (place BetaContext)]
        (is (= 1 (count group)) "the cycle is one place to stand")
        (is (= group (place AlphaContext)) "wearing one name")
        (let [h (v/assert kb (list 'not (list 'genlContext AlphaContext BetaContext))
                          'UniverseContext {:strength :monotonic})]
          (is (= #{BetaContext} (place BetaContext))
              "with one edge defeated there is no cycle and no group")
          (v/retract! kb h)
          (is (not (loose? tx :genlContext)) "the revival repaired in the settle that made it")
          (is (= group (place BetaContext)) "and the group answers to one name again")
          (is (= group (place AlphaContext))))))))

(tu/deftest-kb recover-rebuilds-a-sound-potential
  ;; `recover` replays every stored edge, which is a bulk load and is deferred like
  ;; one; the repair runs before anything reads the relation back.
  (tu/with-terms [w_t x_t y_t z_t]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl w_t x_t) 'UniverseContext)
      (v/assert kb (list 'genl x_t y_t) 'UniverseContext)
      (v/assert kb (list 'genl y_t z_t) 'UniverseContext))
    (let [before (into {} (for [t [w_t x_t y_t z_t]] [t (v/genls kb t)]))]
      (v/recover kb)
      (is (not (loose? (:taxonomy kb) :genl)))
      (is (kb-sound? kb))
      (is (= before (into {} (for [t [w_t x_t y_t z_t]] [t (v/genls kb t)])))
          "the closure survives the rebuild"))))

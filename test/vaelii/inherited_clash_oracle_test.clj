;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.inherited-clash-oracle-test
  "The carried inherited clashes are the ones a full re-ask finds.

  A randomized oracle runs one operation stream into two KBs, one with
  `settle/*incremental-preserving*` bound false, and compares believed content, dilemmas,
  conflicts and refusals after every step, so a divergence names its operation.  The
  stream writes claims of a preserved asymmetric predicate in three contexts, the `genl`
  edges and declarations the readings travel, and the `genlCx` edge that brings two
  contexts' claims into one reader (docs/nmtms.md, \"What qualifies as a nogood\")."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

;; ---- the shared ontology ------------------------------------------------
;;
;;   CxIcBase   ibig binary, asymmetric, preserved along genl at both positions
;;     ├─ CxIcLeft
;;     └─ CxIcRight
;;   CxIcJoin sees both once the stream writes its two edges
;;
;;   ic_top ← ic_mid ← ic_low, ic_top ← ic_side, and ic_far on its own

(def ^:private ctxs '[CxIcBase CxIcLeft CxIcRight])
(def ^:private types '[ic_top ic_mid ic_low ic_side ic_far])
(def ^:private edges '[[ic_mid ic_top] [ic_low ic_mid] [ic_side ic_top] [ic_far ic_side]])

(defn- build-ontology! [kb]
  (v/with-deferred-settle kb
    (doseq [c (rest ctxs)]
      (v/assert kb (list 'genlCx c (first ctxs)) 'CxUniverse {:strength :monotonic}))
    (doseq [d '[(binary_predicate ibig) (asymmetric ibig)]]
      (v/assert kb d (first ctxs) {:strength :monotonic}))
    (doseq [t types]
      (v/assert kb (list 'genl t 'thing) (first ctxs) {:strength :monotonic}))))

;; ---- the operation stream -----------------------------------------------

(defn- rand-op
  "One write: a claim or its denial at a random tuple, context and strength, a `genl`
  edge or a declaration asserted or retracted, or a `genlCx` edge to `CxIcJoin`."
  [^java.util.Random rng]
  (let [pick (fn [xs] (nth xs (.nextInt rng (count xs))))
        ctx  #(pick ctxs)
        str8 #(if (zero? (.nextInt rng 2)) {:strength :monotonic} {})
        claim #(list 'ibig (pick types) (pick types))
        edge #(let [[a b] (pick edges)] (list 'genl a b))
        decl #(list 'transitiveInArg 'ibig (inc (.nextInt rng 2)) 'genl)]
    (case (.nextInt rng 12)
      (0 1 2) [:assert (claim) (ctx) (str8)]
      3       [:assert (list 'not (claim)) (ctx) (str8)]
      4       [:retract (claim) (ctx)]
      (5 6)   [:assert (edge) (ctx) (str8)]
      7       [:retract (edge) (ctx)]
      8       [:assert (decl) (first ctxs) (str8)]
      9       [:retract (decl) (first ctxs)]
      10      [:assert (list 'genlCx 'CxIcJoin (nth ctxs 1)) 'CxUniverse {:strength :monotonic}]
      11      [:assert (list 'genlCx 'CxIcJoin (nth ctxs 2)) 'CxUniverse {:strength :monotonic}])))

(defn- apply-op!
  "Run one op, returning a refusal's `:type` as an observation the two KBs must agree on."
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
  "A reported clash as content, without handles, which differ between the two KBs."
  [e]
  [(:priority e) (:kind e) (:sentence e) (:sentence (:inherited e))
   (into #{} (map (juxt :sentence :context :defeat-class)) (:sides e))])

(defn- snapshot [kb]
  {:believed  (into #{}
                    (comp (keep #(p/get-sentex (:records kb) %))
                          (map (juxt :sentence :context)))
                    (jtms/in-datums (reasoning/tms kb)))
   :scoped    (into #{}
                    (for [[vantage hs] @(reasoning/scoped-defeats kb)
                          h hs
                          :let [s (p/get-sentex (:records kb) h)]]
                      [vantage (:sentence s) (:context s)]))
   :dilemmas  (into #{} (map clash-key) (v/contradictions kb))
   :conflicts (into #{} (map clash-key) (v/conflicts kb))
   :joined    (into #{} (map clash-key) (v/contradictions kb 'CxIcJoin))})

(defn- diff [a b]
  (into {} (keep (fn [k]
                   (let [x (get a k) y (get b k)]
                     (when (not= x y)
                       [k {:incremental-only (set/difference x y)
                           :exhaustive-only  (set/difference y x)}]))))
        (keys a)))

(defn- run-stream
  "The same ops into both KBs, comparing after every write.  Returns `[step op
  incremental-snapshot exhaustive-snapshot]` for the first divergence, or nil."
  [ops]
  (let [inc-kb (tu/fresh)
        exh-kb (tu/isolated-fresh)]
    (try
      (binding [settle/*incremental-preserving* true]  (build-ontology! inc-kb))
      (binding [settle/*incremental-preserving* false] (build-ontology! exh-kb))
      (loop [step 0, [op & more] ops]
        (if-not op
          nil
          (let [ri (binding [settle/*incremental-preserving* true]  (apply-op! inc-kb op))
                re (binding [settle/*incremental-preserving* false] (apply-op! exh-kb op))
                si (snapshot inc-kb)
                se (snapshot exh-kb)]
            (if (and (= ri re) (= si se))
              (recur (inc step) more)
              [step op si se]))))
      (finally (tu/clear-kb! inc-kb) (tu/clear-kb! exh-kb)))))

(defn- settled
  "`ops` into one KB under `incremental?`, returning the snapshot after the last."
  [ops incremental?]
  (let [kb (if incremental? (tu/fresh) (tu/isolated-fresh))]
    (try
      (binding [settle/*incremental-preserving* incremental?]
        (build-ontology! kb)
        (run! #(apply-op! kb %) ops)
        (snapshot kb))
      (finally (tu/clear-kb! kb)))))

(defn- divergence [[step op si se]]
  (str "diverged at step " step " on " (pr-str op) "\n" (pr-str (diff si se))))

;; ---- oracle 1: randomized operation streams -----------------------------

(deftest randomized-streams-find-the-same-inherited-clashes
  (doseq [seed (range 10)]
    (let [rng (java.util.Random. (long seed))
          r   (run-stream (repeatedly 40 #(rand-op rng)))]
      (is (nil? r) (str "seed " seed " " (when r (divergence r)))))))

;; ---- oracle 2: directed streams -----------------------------------------

(deftest a-second-known-true-claim-is-read-where-the-first-was-carried
  ;; the declarations and edges `:default`, so the clash is a dilemma and its report names
  ;; the claim read; `(ibig ic_mid ic_side)` arrives reaching the same tuple and sorts
  ;; before `(ibig ic_top ic_side)`, with nothing of the standing clash moving
  (is (nil? (run-stream
             [[:assert '(transitiveInArg ibig 1 genl) 'CxIcBase {}]
              [:assert '(transitiveInArg ibig 2 genl) 'CxIcBase {}]
              [:assert '(genl ic_mid ic_top) 'CxIcBase {}]
              [:assert '(genl ic_low ic_mid) 'CxIcBase {}]
              [:assert '(ibig ic_side ic_low) 'CxIcBase {}]
              [:assert '(ibig ic_top ic_side) 'CxIcBase {:strength :monotonic}]
              [:assert '(ibig ic_far ic_far) 'CxIcBase {}]
              [:assert '(ibig ic_mid ic_side) 'CxIcBase {:strength :monotonic}]
              [:assert '(ibig ic_far ic_top) 'CxIcBase {}]]))))

(deftest a-reading-withdrawn-at-the-vantage-is-read-again-there
  ;; the stored claim is known-true, so the reading's `:default` edge is the pair's unique
  ;; weakest member and loses at CxIcJoin alone; CxIcJoin then reads the second route, and
  ;; every later settle clears the scoped defeats and decides them again
  (is (nil? (run-stream
             [[:assert '(genlCx CxIcJoin CxIcLeft) 'CxUniverse {:strength :monotonic}]
              [:assert '(genlCx CxIcJoin CxIcRight) 'CxUniverse {:strength :monotonic}]
              [:assert '(transitiveInArg ibig 1 genl) 'CxIcBase {:strength :monotonic}]
              [:assert '(transitiveInArg ibig 2 genl) 'CxIcBase {:strength :monotonic}]
              [:assert '(genl ic_low ic_mid) 'CxIcLeft {}]
              [:assert '(genl ic_mid ic_top) 'CxIcLeft {:strength :monotonic}]
              [:assert '(genl ic_low ic_far) 'CxIcLeft {}]
              [:assert '(genl ic_far ic_top) 'CxIcLeft {:strength :monotonic}]
              [:assert '(ibig ic_side ic_low) 'CxIcRight {:strength :monotonic}]
              [:assert '(ibig ic_top ic_side) 'CxIcLeft {:strength :monotonic}]
              [:assert '(ibig ic_far ic_far) 'CxIcBase {}]
              [:assert '(ibig ic_side ic_far) 'CxIcBase {}]]))))

(deftest a-clash-split-across-contexts-is-carried-through-its-scoped-defeat
  ;; the stored default in CxIcRight loses at CxIcJoin only, so every settle re-decides it
  ;; there while it stays believed in CxIcRight
  (is (nil? (run-stream
             [[:assert '(transitiveInArg ibig 1 genl) 'CxIcBase {:strength :monotonic}]
              [:assert '(transitiveInArg ibig 2 genl) 'CxIcBase {:strength :monotonic}]
              [:assert '(genl ic_low ic_mid) 'CxIcLeft {:strength :monotonic}]
              [:assert '(genl ic_mid ic_top) 'CxIcLeft {:strength :monotonic}]
              [:assert '(ibig ic_side ic_low) 'CxIcRight {}]
              [:assert '(genlCx CxIcJoin CxIcLeft) 'CxUniverse {:strength :monotonic}]
              [:assert '(genlCx CxIcJoin CxIcRight) 'CxUniverse {:strength :monotonic}]
              [:assert '(ibig ic_top ic_side) 'CxIcLeft {:strength :monotonic}]
              [:assert '(ibig ic_far ic_far) 'CxIcBase {}]
              [:retract '(genl ic_mid ic_top) 'CxIcLeft]
              [:assert '(ibig ic_far ic_side) 'CxIcBase {}]]))))

(deftest a-route-edge-raised-to-known-true-is-read-again
  ;; the reading rests on the direct `:default` edge until the route through ic_mid is
  ;; raised to `:monotonic`; the claim then opposes the stored converse at that route, and
  ;; the dilemma becomes a defeat with no member of the carried entry changing class
  (let [ops '[[:assert (transitiveInArg ibig 1 genl) CxIcBase {:strength :monotonic}]
              [:assert (transitiveInArg ibig 2 genl) CxIcBase {:strength :monotonic}]
              [:assert (genl ic_low ic_mid) CxIcBase {}]
              [:assert (genl ic_mid ic_top) CxIcBase {}]
              [:assert (genl ic_low ic_top) CxIcBase {}]
              [:assert (ibig ic_side ic_low) CxIcBase {}]
              [:assert (ibig ic_top ic_side) CxIcBase {:strength :monotonic}]
              [:assert (genl ic_low ic_mid) CxIcBase {:strength :monotonic}]
              [:assert (genl ic_mid ic_top) CxIcBase {:strength :monotonic}]]]
    (is (nil? (run-stream ops)))
    (is (= [#{} false]
           ((juxt :dilemmas #(contains? (:believed %) '[(ibig ic_side ic_low) CxIcBase]))
            (settled ops true))))))

(def ^:private joined-last
  "Two known-true claims in CxIcLeft and CxIcRight that clash through `(genl ic_low
  ic_mid)` in a reader that sees both, with that reader's second `genlCx` edge written
  last.  The `icAgeOf` pair gives CxIcLeft a scoped defeat, and the `anti_transitive`
  writes are settles whose region holds nothing of the clash."
  '[[:assert (functional icAgeOf) CxIcBase {:strength :monotonic}]
    [:assert (genl ic_low ic_mid) CxIcBase {:strength :monotonic}]
    [:assert (ibig ic_mid ic_low) CxIcRight {:strength :monotonic}]
    [:assert (icAgeOf IcI2 0) CxIcBase {}]
    [:assert (ibig ic_low ic_low) CxIcLeft {:strength :monotonic}]
    [:assert (icAgeOf IcI2 2) CxIcLeft {:strength :monotonic}]
    [:assert (genlCx CxIcJoin CxIcLeft) CxUniverse {:strength :monotonic}]
    [:assert (transitiveInArg ibig 2 genl) CxIcBase {:strength :monotonic}]
    [:assert (anti_transitive icPrecedes) CxIcBase {:strength :monotonic}]
    [:assert (transitiveInArg ibig 2 genl) CxIcBase {}]
    [:assert (anti_transitive icPrecedes) CxIcBase {:strength :monotonic}]
    [:assert (genlCx CxIcJoin CxIcRight) CxUniverse {:strength :monotonic}]])

(deftest a-genlCx-edge-that-joins-a-denial-and-its-claim-forms-the-pair-in-either-order
  (let [joins?    #(= 'genlCx (first (second %)))
        reference (settled (into (filterv joins? joined-last) (remove joins?) joined-last)
                           true)]
    (is (seq (:conflicts reference)))
    (is (nil? (run-stream joined-last)))
    (is (= reference (settled joined-last true) (settled joined-last false)))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.negation-oracle-test
  "Incremental P/¬P pairing finds the same nogoods an exhaustive pass does.

  A randomized oracle runs one operation stream into two KBs, one with
  `settle/*incremental-negations*` bound false, and compares believed content, dilemmas,
  conflicts and refusals after every step, so a divergence names its operation.  The
  directed tests for `:dirty`, the relabelled region and the visibility verdicts
  (docs/nmtms.md, \"The negation memo\") each go red when that input alone is removed.
  None generates the supersession window `settle/note-supersession-flips!` covers."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.settle :as settle]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

;; ---- the shared ontology ------------------------------------------------

(def ^:private ctxs
  "Three contexts: `CxNegLeft` and `CxNegRight` both inherit `CxNegBase` and neither
  sees the other, so a pair straddling them pairs only once a context below both exists."
  '[CxNegBase CxNegLeft CxNegRight])

(def ^:private preds '[nflies nswims nsings])
(def ^:private inds  '[NA NB NC])

(defn- build-ontology! [kb]
  (v/with-deferred-settle kb
    (doseq [c (rest ctxs)]
      (v/assert kb (list 'genlCx c (first ctxs)) 'CxUniverse))))

;; ---- the operation stream -----------------------------------------------

(defn- rand-op
  "One write: either polarity of a shared body in any context, at either strength,
  retraction of either side, or a `genlCx` edge that makes standing pairs jointly visible."
  [^java.util.Random rng]
  (let [ctx  (nth ctxs (.nextInt rng (count ctxs)))
        pred #(nth preds (.nextInt rng (count preds)))
        ind  #(nth inds  (.nextInt rng (count inds)))
        str8 #(if (zero? (.nextInt rng 3)) {:strength :monotonic} {})
        body #(list (pred) (ind))]
    (case (.nextInt rng 10)
      (0 1 2) [:assert (body) ctx (str8)]
      (3 4 5) [:assert (list 'not (body)) ctx (str8)]
      6       [:retract (body) ctx]
      7       [:retract (list 'not (body)) ctx]
      ;; CxNegJoin below both sides exposes every standing left/right pair at once
      8       [:assert (list 'genlCx 'CxNegJoin (nth ctxs 1)) 'CxUniverse
               {:strength :monotonic}]
      9       [:assert (list 'genlCx 'CxNegJoin (nth ctxs 2)) 'CxUniverse
               {:strength :monotonic}])))

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
  "A reported pair as content, without handles, which differ between the two KBs."
  [e]
  [(:priority e) (:sentence e)
   (into #{} (map (juxt :sentence :context :defeat-class)) (:sides e))])

(defn- snapshot [kb]
  {:believed  (into #{}
                    (comp (keep #(p/get-sentex (:records kb) %))
                          (map (juxt :sentence :context)))
                    (jtms/in-datums (reasoning/tms kb)))
   :dilemmas  (into #{} (map clash-key) (v/contradictions kb))
   :conflicts (into #{} (map clash-key) (v/conflicts kb))})

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
      (binding [settle/*incremental-negations* true]  (build-ontology! inc-kb))
      (binding [settle/*incremental-negations* false] (build-ontology! exh-kb))
      (loop [step 0, [op & more] ops]
        (if-not op
          nil
          (let [ri (binding [settle/*incremental-negations* true]  (apply-op! inc-kb op))
                re (binding [settle/*incremental-negations* false] (apply-op! exh-kb op))
                si (snapshot inc-kb)
                se (snapshot exh-kb)]
            (if (and (= ri re) (= si se))
              (recur (inc step) more)
              [step op si se]))))
      (finally (tu/clear-kb! inc-kb) (tu/clear-kb! exh-kb)))))

;; ---- oracle 1: randomized operation streams -----------------------------

(deftest randomized-streams-pair-the-same-negations
  (doseq [seed (range 12)]
    (let [rng (java.util.Random. (long seed))
          [step op si se] (run-stream (repeatedly 45 #(rand-op rng)))]
      (is (nil? step)
          (str "seed " seed " diverged at step " step " on " (pr-str op) "\n"
               (pr-str (diff si se)))))))

;; ---- oracle 2: the removal whose record is already gone -----------------
;; Only `:dirty` covers this: the retracted handle's record is gone, so the region cannot
;; name its body, and `note-opposed!` has dropped the body's entry.

(deftest a-retraction-re-derives-a-body-that-stays-opposed
  (let [[step op si se]
        (run-stream
         [;; CxNegBase is seen by both of the others, so all three pair
          [:assert '(nflies NA)             (first ctxs) {}]
          [:assert (list 'not '(nflies NA)) (nth ctxs 1) {}]
          [:assert (list 'not '(nflies NA)) (nth ctxs 2) {}]
          ;; unrelated traffic, so the survivors are long out of the region
          [:assert '(nswims NB) (first ctxs) {}]
          [:assert '(nsings NC) (first ctxs) {}]
          ;; one negation goes; the body is still stored in both polarities, so the
          ;; other pair stands and has to be re-derived without it
          [:retract (list 'not '(nflies NA)) (nth ctxs 2)]
          ;; one more settle, where a pair the retraction dropped would stay gone
          [:assert '(nsings NB) (first ctxs) {}]])]
    (is (nil? step)
        (str "diverged at step " step " on " (pr-str op) "\n" (pr-str (diff si se))))))

;; ---- oracle 2b: the revival nothing writes ------------------------------
;; Only the relabelled region covers this.  Retracting `(nq NA)` drops the monotonic route
;; to `(nflies NA)`, which then stands at :default and revives the defeated negation, with
;; nothing stored or removed on the body.  A carried entry's `:priority` cannot go stale
;; visibly: `decide-nogood` reads classes live, so only which pairs exist is tested.

(deftest a-revival-elsewhere-brings-a-pair-back
  (let [[step op si se]
        (run-stream
         [[:assert (list 'set/forwardRule (vr/rule-sentence ['(nq ?x)] '(nflies ?x)))
           (first ctxs) {:strength :monotonic}]
          [:assert (list 'set/forwardRule (vr/rule-sentence ['(nr ?x)] '(nflies ?x)))
           (first ctxs) {:strength :monotonic}]
          ;; known-true route: (nflies NA) is derived at :monotonic
          [:assert '(nq NA) (first ctxs) {:strength :monotonic}]
          ;; a second, defeasible route to the same conclusion — no new sentex, so
          ;; nothing is written about the body
          [:assert '(nr NA) (first ctxs) {}]
          ;; the negation ranks below the monotonic conclusion and is defeated, which
          ;; empties the body's memo entry
          [:assert (list 'not '(nflies NA)) (first ctxs) {}]
          ;; unrelated traffic, so the body is well out of the region
          [:assert '(nswims NB) (first ctxs) {}]
          ;; ...and now the known-true route goes.  (nflies NA) survives on the
          ;; defeasible one at :default, so the negation revives and the pair is a
          ;; dilemma again — with nothing stored or removed on its body.
          [:retract '(nq NA) (first ctxs)]
          [:assert '(nsings NC) (first ctxs) {}]])]
    (is (nil? step)
        (str "diverged at step " step " on " (pr-str op) "\n" (pr-str (diff si se))))))

;; ---- oracle 3: the edge that makes a standing pair visible --------------
;; Only the recorded visibility verdicts cover this: nothing is stored or relabelled on
;; either side.

(deftest a-genlCx-edge-exposes-standing-pairs
  (let [[step op si se]
        (run-stream
         (concat
          (for [p preds] [:assert (list p 'NA) (nth ctxs 1) {}])
          (for [p preds] [:assert (list 'not (list p 'NA)) (nth ctxs 2) {}])
          ;; nothing above pairs: left and right are incomparable
          [[:assert '(genlCx CxNegJoin CxNegLeft) 'CxUniverse
            {:strength :monotonic}]
           ;; ...and this second edge is what puts a context below *both*
           [:assert '(genlCx CxNegJoin CxNegRight) 'CxUniverse
            {:strength :monotonic}]
           [:assert '(nswims NB) (nth ctxs 1) {}]]))]
    (is (nil? step)
        (str "diverged at step " step " on " (pr-str op) "\n" (pr-str (diff si se))))))

(deftest a-genlCx-edge-leaving-withdraws-the-pairs-it-exposed
  ;; A verdict moving from true back to false: retracting one edge withdraws every pair
  ;; the join exposed.
  (let [[step op si se]
        (run-stream
         (concat
          (for [p preds] [:assert (list p 'NA) (nth ctxs 1) {}])
          (for [p preds] [:assert (list 'not (list p 'NA)) (nth ctxs 2) {}])
          [[:assert '(genlCx CxNegJoin CxNegLeft) 'CxUniverse
            {:strength :monotonic}]
           [:assert '(genlCx CxNegJoin CxNegRight) 'CxUniverse
            {:strength :monotonic}]
           ;; a settle in between, so the pairs are standing rather than arriving
           [:assert '(nswims NB) (nth ctxs 1) {}]
           [:retract '(genlCx CxNegJoin CxNegRight) 'CxUniverse]
           ;; one more settle, which is where a pair still carried would keep showing up
           [:assert '(nsings NC) (nth ctxs 1) {}]
           ;; ...and back: the same verdict moving a second time
           [:assert '(genlCx CxNegJoin CxNegRight) 'CxUniverse
            {:strength :monotonic}]
           [:assert '(nflies NB) (nth ctxs 1) {}]]))]
    (is (nil? step)
        (str "diverged at step " step " on " (pr-str op) "\n" (pr-str (diff si se))))))

;; ---- oracle 4: defeat, then revival -------------------------------------

(deftest a-defeated-pair-revives-when-its-defeater-goes
  (let [[step op si se]
        (run-stream
         [[:assert '(nflies NA) (first ctxs) {:strength :monotonic}]
          [:assert (list 'not '(nflies NA)) (first ctxs) {}]      ; default loses
          [:assert '(nswims NB) (first ctxs) {}]                   ; an unrelated settle
          [:retract '(nflies NA) (first ctxs)]                     ; ...and the winner goes
          [:assert '(nsings NC) (first ctxs) {}]])]
    (is (nil? step)
        (str "diverged at step " step " on " (pr-str op) "\n" (pr-str (diff si se))))))

;; ---- oracle 5: the belief change with no relabel behind it -------------
;; A merge supersedes both sides of a standing pair with no relabel, and dropping it
;; hands the spellings back the same way.

(deftest a-merge-and-its-undoing-move-a-pair
  (let [[step op si se]
        (run-stream
         [[:assert '(nflies NA)             (first ctxs) {}]
          [:assert (list 'not '(nflies NA)) (first ctxs) {}]     ; a standing dilemma
          [:assert '(nswims NB) (first ctxs) {}]                  ; unrelated traffic
          ;; NA is deprecated in favour of NB, so both sides of the pair are restated on
          ;; NB's body and the originals are superseded
          [:assert '(rewriteOf NB NA) (first ctxs) {:strength :monotonic}]
          [:assert '(nsings NC) (first ctxs) {}]
          ;; ...and the merge goes, which gives the original spellings back
          [:retract '(rewriteOf NB NA) (first ctxs)]
          [:assert '(nsings NB) (first ctxs) {}]])]
    (is (nil? step)
        (str "diverged at step " step " on " (pr-str op) "\n" (pr-str (diff si se))))))

;; ---- the standing dilemma an unrelated assert must not erase ------------
;; Directed, because the oracle stays green if both KBs lose the dilemma.

(deftest a-standing-dilemma-survives-unrelated-asserts
  (let [kb (tu/fresh)]
    (try
      (build-ontology! kb)
      (v/assert kb '(nflies NA) (first ctxs) {})
      (v/assert kb (list 'not '(nflies NA)) (first ctxs) {})
      (let [reported (fn [] (into #{} (map :sentence) (v/contradictions kb)))
            standing (reported)]
        (is (= 1 (count standing)) "a default against a default is a represented dilemma")
        (doseq [i (range 5)]
          (v/assert kb (list 'nswims (symbol (str "NX" i))) (first ctxs) {})
          (is (= standing (reported))
              (str "the standing dilemma was dropped by unrelated assert " i))))
      (finally (tu/clear-kb! kb)))))

;; ---- order independence -------------------------------------------------

(deftest the-same-dilemmas-in-any-order
  (let [content [['(nflies NA)              (first ctxs) {:strength :monotonic}]
                 [(list 'not '(nflies NA))  (first ctxs) {}]
                 ['(nswims NB)              (nth ctxs 1) {}]
                 [(list 'not '(nswims NB))  (nth ctxs 1) {}]
                 ['(nsings NC)              (nth ctxs 2) {}]
                 [(list 'not '(nsings NC))  (nth ctxs 2) {:strength :monotonic}]]
        run! (fn [ops]
               (let [kb (tu/fresh)]
                 (try
                   (build-ontology! kb)
                   (doseq [[s c o] ops] (v/assert kb s c o))
                   (snapshot kb)
                   (finally (tu/clear-kb! kb)))))
        base (run! content)]
    (doseq [seed (range 6)]
      (let [shuffled (shuffle content)]
        (is (= base (run! shuffled))
            (str "arrival order " seed " changed the answer\n"
                 (pr-str (diff base (run! shuffled)))))))))

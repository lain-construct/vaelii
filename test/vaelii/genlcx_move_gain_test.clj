;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.genlcx-move-gain-test
  "A `genlCx` move's sweeps read per group of readers by what the group gains
  (`tax/context-move`'s `:gains`, `special/move-groups`), and hold what the whole sweep
  holds (`checks/*whole-move-sweeps?*`).

  Each world is one KB loaded twice with the same writes, the second write an edit
  adding `genlCx` edges and the facts of the contexts they bring in, once with the sweeps
  split and once whole.  The judge compares, per context: the stored sentences, the
  believed ones, and each stored sentence's justifications as `[informant antecedents]`
  read by content, a `genlCx` antecedent left out, and a mint drawn over a restated twin
  left out (`over-restatement?`).  The shapes the split must still see are each a case:

  - **the edge shows nothing**: a lower context full of marked and declared facts gains
    an empty context, as `(genlCx CxWell CxData)` does over a large store;
  - **a non-empty new parent** holding the converse of a lower anti-symmetric fact, the
    other half of a functional clash, a declared fact, and a membership a stored mint is
    subsumed by;
  - **a parent stating a mark, a declaration or a `genl` edge**, which makes a pair or a
    meeting of facts the readers already saw (`plain-gain?` refuses the gain side);
  - **an `except`** the readers see, which can hide a fact of the gain;
  - **a defeat** the edge gives a conflict to place;
  - **a membership** the edge shows, which convicts a declared fact under the
    constraint-only reading (the argument holds);
  - **a placement a more general one displaces**, where the edge wires a context that
    already saw both ingredients above it;
  - and a seeded random world over all of them, diamonds included, under either
    argument-type reading.

  `the-gain-guard-is-needed` breaks the guard (`plain-gain?` always true) and asserts
  the judge then disagrees on a world that needs it."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.decide.argument :as argument]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.special :as special]
            [vaelii.impl.types.reasoning :as reasoning])
  (:import [java.util Random]))

;; ---- loading -----------------------------------------------------------

(defonce ^:private space-counter (atom 0))

(def ^:private ^:dynamic *assertive?*
  "The argument-type reading a world loads under: assertive, as the full KB's, or the
  constraint-only reading, where an argument conviction holds a fact out."
  true)

(defn- run-world
  "A fresh KB on a space of its own, `base` asserted one by one and `edit` applied as one
  `v/edit!`, with the move's sweeps split or `whole?`.  Each write is `[sentence context
  strength]`, or in `base` `[:except i context]`, an except of the `i`th write.  Returns
  `{:kb :space}`."
  [base edit whole?]
  (let [space [::gain (swap! space-counter inc)]
        kb    (v/open-kb {:backend :memory :space space :recover? false})]
    (binding [argument/*assertive-arg-types?* *assertive?*
              checks/*whole-move-sweeps?*   whole?]
      (reduce (fn [hs [s c st]]
                (conj hs (if (= :except s)
                           (v/assert kb (list 'except (v/sentex-handle (nth hs c))) st)
                           (v/assert kb s c (if st {:strength st} {})))))
              [] base)
      (v/edit! kb {:add (mapv (fn [[s c st]] (if st [s c {:strength st}] [s c])) edit)}))
    {:kb kb :space space}))

(defn- close! [{:keys [kb space]}]
  (try (v/close! kb)
       (finally (mem/drop-record-space! space) (mem/drop-index-space! space))))

;; ---- reading -----------------------------------------------------------

(defn- render
  "`form` with every `(sentexHandle h)` replaced by the content of the sentex it names."
  [kb form]
  (cond
    (and (seq? form) (= 'sentexHandle (first form)))
    (let [sx (v/sentex kb (second form))]
      [:h (when sx (render kb (v/sentence-of sx))) (:context sx)])
    (seq? form) (apply list (map #(render kb %) form))
    :else form))

(defn- over-restatement?
  "Is the justification `j` a mint drawn over a restated twin: an argument-type
  informant with a fact antecedent the equality closure restated (`rewriteOf`)?  The
  whole sweep reads every fact below the edge again, a twin among them, and draws the
  mints the twin's own arrival does not, so a KB that never swept them holds none (the
  writes asserted singly agree with the split here).  Neither side counts them."
  [tms j]
  (and (contains? '#{arg args argAndRest argArg genlArg argsGenl argAndRestGenl
                     interArg interArgs interArgAndRest interArgEqual}
                  (:informant j))
       (some (fn [a] (some #(= 'rewriteOf (:informant (jtms/justification tms %)))
                           (jtms/supports tms a)))
             (:antecedents j))))

(defn- reading
  "Per context of `ctxs`: `{C {:stored #{S} :in #{S} :justs {S #{[informant #{antecedent}]}}}}`,
  every handle read by content, without the mints drawn over a restated twin
  (`over-restatement?`) and the sentences resting on nothing else."
  [kb ctxs]
  (let [tms  (reasoning/tms kb)
        recs (:records kb)
        ;; a `genlCx` antecedent is the witness path a firing found first, and the two
        ;; sweeps can draw a mint again over another path that stands as well
        ;; (`genlcx_move_oracle_test` leaves them out for the same reason)
        key  (fn [h] (when-let [sx (p/get-sentex recs h)]
                       (let [s (v/sentence-of sx)]
                         (when-not (and (seq? s) (= 'genlCx (first s)))
                           [(render kb s) (:context sx)]))))
        js   (fn [h] (into [] (comp (keep #(jtms/justification tms %))
                                    (remove #(over-restatement? tms %)))
                           (jtms/supports tms h)))
        kept? (fn [sx] (or (jtms/premise? tms (:id sx))
                           (empty? (jtms/supports tms (:id sx)))
                           (seq (js (:id sx)))))]
    (into {}
          (for [c ctxs
                :let [sxs (filterv kept? (v/sentexes-in-context kb c))]]
            [c {:stored (into #{} (map #(render kb (v/sentence-of %))) sxs)
                :in     (into #{} (comp (filter #(jtms/in? tms (:id %)))
                                        (map #(render kb (v/sentence-of %))))
                              sxs)
                :justs  (into {} (for [sx sxs]
                                   [(render kb (v/sentence-of sx))
                                    (into #{} (map (fn [j] [(str (:informant j))
                                                            (into #{} (keep key) (:antecedents j))]))
                                          (js (:id sx)))]))}]))))

(defn- world-contexts
  "Every context of the world: each write's, and each a `genlCx` write names, since a
  context stating nothing can hold a mint."
  [base edit]
  (into (sorted-set) (map str)
        (concat ['CxUniverse]
                (map (fn [[s c st]] (if (= :except s) st c)) base)
                (map second edit)
                (for [[s] (concat base edit)
                      :when (and (seq? s) (= 'genlCx (first s)))
                      c (rest s)]
                  c))))

(defn- disagreements
  "Where the split and the whole reading of the world `base` + `edit` differ, as
  `[context kind split whole]` rows."
  [base edit]
  (let [ctxs  (map symbol (world-contexts base edit))
        split (run-world base edit false)
        whole (run-world base edit true)]
    (try
      (let [a (reading (:kb split) ctxs)
            b (reading (:kb whole) ctxs)]
        (vec (for [c ctxs
                   k [:stored :in :justs]
                   :let [x (get-in a [c k]) y (get-in b [c k])]
                   :when (not= x y)]
               [c k (if (map? x) (into {} (remove (fn [[s j]] (= j (get y s)))) x) (set/difference x y))
                (if (map? y) (into {} (remove (fn [[s j]] (= j (get x s)))) y) (set/difference y x))])))
      (finally (close! split) (close! whole)))))

(defn- reads-of
  "What `pred` holds per context after the edit, split: `{context #{sentence}}` for the
  stored sentences `pred` keeps."
  [base edit pred]
  (let [w (run-world base edit false)]
    (try
      (into {} (for [c (map symbol (world-contexts base edit))]
                 [c (into #{} (comp (map v/sentence-of) (filter pred)) (v/sentexes-in-context (:kb w) c))]))
      (finally (close! w)))))

;; ---- the shapes --------------------------------------------------------

(def ^:private M :monotonic)

(def ^:private upper
  "The marks and declarations every world states in CxUniverse."
  [['(anti_symmetric aboveR) 'CxUniverse nil]
   ['(functional fnR) 'CxUniverse nil]
   ['(genl kind_t thing) 'CxUniverse M]
   ['(genl sub_kind_t kind_t) 'CxUniverse M]
   ['(arg declR 1 kind_t) 'CxUniverse M]
   ['(disjoint dog_t cat_t) 'CxUniverse M]])

(defn- lower
  "`n` of each shape stored in `ctx`: anti-symmetric and functional facts with no partner
  yet, declared facts (each mints a `kind_t` membership) and plain facts."
  [ctx n]
  (vec (mapcat (fn [i]
                 [[(list 'aboveR (symbol (str "A" i)) (symbol (str "B" i))) ctx M]
                  [(list 'fnR (symbol (str "F" i)) (symbol (str "G" i))) ctx M]
                  [(list 'declR (symbol (str "D" i)) 'Dthing) ctx M]
                  [(list 'plainR (symbol (str "P" i)) 'Pthing) ctx nil]])
               (range n))))

(def ^:private chain-edit
  "A large store's edit: two fresh contexts in a chain, the lower one wired under them,
  and facts stated in the upper fresh one."
  (fn [facts]
    (into [['(genlCx CxW CxUniverse) 'CxUniverse M]
           ['(genlCx CxD CxW) 'CxUniverse M]
           ['(genlCx CxL CxD) 'CxUniverse M]]
          facts)))

(def ^:private base-l
  (into (conj upper ['(genlCx CxL CxUniverse) 'CxUniverse M]) (lower 'CxL 6)))

(deftest an-edge-showing-an-empty-context-agrees
  (is (= [] (disagreements base-l (chain-edit [])))))

(deftest an-edge-showing-plain-facts-agrees
  (testing "the converse of a lower anti-symmetric fact, a functional clash, a declared
            fact, and a membership a lower mint is subsumed by"
    (let [edit (chain-edit [['(aboveR B0 A0) 'CxW M]
                            ['(fnR F1 H1) 'CxW M]
                            ['(declR E0 Dthing) 'CxW M]
                            ['(sub_kind_t D2) 'CxW M]
                            ['(plainR Wx Wy) 'CxW nil]
                            ['(comment Wx "a word") 'CxW nil]])]
      (is (= [] (disagreements base-l edit)))
      (testing "and the edge does merge at the lower context"
        (let [eqs (reads-of base-l edit #(= 'equals (first %)))]
          (is (contains? (get eqs 'CxL) '(equals A0 B0)))
          (is (contains? (get eqs 'CxL) '(equals G1 H1))))))))

(deftest a-parent-stating-a-mark-or-an-edge-agrees
  (testing "a mark over two lower facts that already clash under it"
    (let [base (into base-l [['(aboveS C0 C1) 'CxL M] ['(aboveS C1 C0) 'CxL M]])]
      (is (= [] (disagreements base (chain-edit [['(anti_symmetric aboveS) 'CxW nil]]))))))
  (testing "a `genl` edge bringing a lower predicate under a marked one"
    (let [base (into base-l [['(aboveT C0 C1) 'CxL M] ['(aboveR C1 C0) 'CxL M]])]
      (is (= [] (disagreements base (chain-edit [['(genl aboveT aboveR) 'CxW M]]))))))
  (testing "a declaration over lower facts"
    (let [base (into base-l [['(declS C0 C1) 'CxL M]])]
      (is (= [] (disagreements base (chain-edit [['(arg declS 1 kind_t) 'CxW M]])))))))

(deftest an-except-the-readers-see-agrees
  (let [n (count base-l)]
    (testing "an except in the lower context of a fact the readers already see, whose
              converse the edge shows"
      (is (= [] (disagreements (into base-l [['(aboveR B3 A3) 'CxUniverse M] [:except n 'CxL]])
                               (chain-edit [['(aboveR A3 B3) 'CxW M]])))))
    (testing "an except in the lower context of a lower fact, whose converse the edge shows"
      (is (= [] (disagreements (conj base-l [:except 19 'CxL])
                               (chain-edit [['(aboveR B3 A3) 'CxW M]])))))))

(deftest a-defeat-the-edge-places-agrees
  (testing "two default memberships the edge makes clash under a disjointness"
    (let [base (into base-l [['(dog_t Rex) 'CxL :default]])]
      (is (= [] (disagreements base (chain-edit [['(cat_t Rex) 'CxW :default]])))))))

;; ---- a seeded random world ---------------------------------------------

(defn- pick [^Random rng coll] (nth coll (.nextInt rng (count coll))))

(defn- gen-world
  "`[base edit]` for `seed`: lower contexts under CxUniverse and two upper ones, each
  holding facts, marks and declarations of every shape, and an edit adding one to three
  edges from a lower context to an upper one or to another lower one, with a fact more."
  [seed]
  (let [rng   (Random. (long seed))
        olds  '[CxL1 CxL2 CxL3]
        news  '[CxN1 CxN2]
        inds  '[I0 I1 I2 I3]
        fact  (fn [ctx]
                (let [a (pick rng inds) b (pick rng inds)]
                  (case (int (.nextInt rng 9))
                    0 [(list 'aboveR a b) ctx M]
                    1 [(list 'fnR a b) ctx M]
                    2 [(list 'declR a b) ctx M]
                    3 [(list 'sub_kind_t a) ctx M]
                    4 [(list 'kind_t a) ctx M]
                    5 [(list (pick rng '[dog_t cat_t]) a) ctx :default]
                    6 [(list 'aboveQ a b) ctx M]
                    7 [(pick rng '[(genl aboveQ aboveR) (anti_symmetric aboveQ) (arg aboveQ 2 kind_t)]) ctx M]
                    8 [(list 'plainR a b) ctx nil])))
        dag   [['(disjoint kind_t cat_t) 'CxUniverse M]
               ['(genlCx CxL1 CxUniverse) 'CxUniverse M]
               [(list 'genlCx 'CxL2 (pick rng '[CxUniverse CxL1])) 'CxUniverse M]
               [(list 'genlCx 'CxL3 (pick rng '[CxUniverse CxL1 CxL2])) 'CxUniverse M]]
        base  (-> upper (into dag) (into (repeatedly (+ 6 (.nextInt rng 8)) #(fact (pick rng olds)))))
        n1    [(list 'genlCx 'CxN1 (pick rng '[CxUniverse CxL1])) 'CxUniverse M]
        n2    [(list 'genlCx 'CxN2 (pick rng '[CxUniverse CxN1])) 'CxUniverse M]
        ;; diamonds: a second parent of CxN2, and lower contexts already under the fresh
        ;; ones, so a placement can sit below a context the edit wires above it
        extra (into (if (zero? (.nextInt rng 2)) [] [['(genlCx CxN2 CxL1) 'CxUniverse M]])
                    (repeatedly (.nextInt rng 3)
                                #(vector (list 'genlCx (pick rng '[CxL2 CxL3]) (pick rng news))
                                         'CxUniverse M)))
        under (into [] (distinct)
                    (repeatedly (inc (.nextInt rng 3))
                                #(vector (list 'genlCx (pick rng '[CxL2 CxL3]) (pick rng (into news '[CxL1])))
                                         'CxUniverse M)))
        ;; the fresh contexts hold their content before the edit wires the lower ones
        ;; under them, so the move, not each fact's arrival, is what meets it
        base  (-> base (conj n1 n2) (into (distinct) extra)
                  (into (repeatedly (+ 1 (.nextInt rng 4)) #(fact (pick rng news)))))
        edit  (-> []
                  (into (remove (fn [[[_ a b] :as e]] (or (= a b) (and (= a 'CxL2) (= b 'CxL3))
                                                          (some #{e} extra))))
                        under)
                  (into (repeatedly (.nextInt rng 2) #(fact (pick rng news)))))]
    [base edit]))

(deftest a-placement-a-wired-context-displaces-agrees
  ;; CxP and CxR each see the fact's context and the declaration's, so each holds the
  ;; mint; the edge puts CxR above CxP, and CxP's placement goes.  CxP files mints of
  ;; its own, so a sweep reading the gain's records would choose that side and miss it
  (let [base (-> upper
                 (into [['(genlCx CxX CxUniverse) 'CxUniverse M]
                        ['(genlCx CxY CxUniverse) 'CxUniverse M]
                        ['(genlCx CxZ CxUniverse) 'CxUniverse M]
                        ['(genlCx CxP CxX) 'CxUniverse M]
                        ['(genlCx CxP CxY) 'CxUniverse M]
                        ['(genlCx CxP CxZ) 'CxUniverse M]
                        ['(genlCx CxR CxX) 'CxUniverse M]
                        ['(genlCx CxR CxY) 'CxUniverse M]
                        ['(genl y_kind thing) 'CxUniverse M]
                        ['(genl z_kind thing) 'CxUniverse M]
                        ['(arg yRel 1 y_kind) 'CxY M]
                        ['(arg zRel 1 z_kind) 'CxZ M]
                        ['(yRel I0 Z) 'CxX M]
                        ['(plainR Q0 Q1) 'CxR nil]])
                 (into (for [i (range 8)] [(list 'zRel (symbol (str "J" i)) 'Z) 'CxX M])))
        edit [['(genlCx CxP CxR) 'CxUniverse M]]]
    (doseq [prune? [true false]]
      (binding [checks/*prune-subsumed-mints?* prune?]
        (is (= [] (disagreements base edit)) (str "pruning " prune?))
        (is (not (contains? (get (reads-of base edit #{'(y_kind I0)}) 'CxP) '(y_kind I0))))))
    (testing "and a sweep that reads no displaced context disagrees"
      (binding [checks/*prune-subsumed-mints?* false]
        (with-redefs-fn {#'special/edge-mint-plan
                         (let [o @#'special/edge-mint-plan]
                           (fn [& a] (some-> (apply o a) (assoc :displaced #{}))))}
          #(is (seq (disagreements base edit))))))))

(deftest seeded-worlds-agree
  ;; 600 seeds agree under either reading but seed 59 under the assertive one, where
  ;; the whole sweep withholds a mint at CxL2 that the split holds, as the fact's own
  ;; arrival after the edges does.  Before the diamonds, seed 134 differed the same
  ;; way: two functional clashes compete through one term and the sweep merges the one
  ;; it meets first, as their arrival in either order does
  (doseq [assertive? [true false]
          seed (range 24)
          :let [[base edit] (gen-world seed)
                d (binding [*assertive?* assertive?] (disagreements base edit))]]
    (is (= [] d) (str "seed " seed (when-not assertive? ", constraint-only")))))

(defn- placements
  "The contexts of `ctxs` storing `s` once `writes` are loaded in order, the last as the
  edit, with the sweeps split or `whole?`."
  [writes whole? s ctxs]
  (let [w (run-world (pop writes) [(peek writes)] whole?)]
    (try
      (into (sorted-set)
            (filter (fn [c] (some #{s} (map v/sentence-of (v/sentexes-in-context (:kb w) c)))))
            ctxs)
      (finally (close! w)))))

(defn- merge-world
  "The writes of a world where the context `hi` and the context `lo` under it both see
  the pair `f0` (in CxL1) and `f1` (in `hi`) under `mark`: `hi` through the edge
  `(genlCx hi CxL1)`, `lo` through `hi` and through CxN2 under `n2-super`."
  [mark f0 f1 hi lo n2-super]
  [['(genlCx CxL1 CxUniverse) 'CxUniverse M]
   [f0 'CxL1 M]
   [(list 'genlCx lo hi) 'CxUniverse M]
   [(list 'genlCx 'CxN2 n2-super) 'CxUniverse M]
   [(list 'genlCx lo 'CxN2) 'CxUniverse M]
   [f1 hi M]
   [mark 'CxUniverse nil]
   [(list 'genlCx hi 'CxL1) 'CxUniverse M]])

(defn- rotations [ws] (for [i (range (count ws))] (into (subvec ws i) (subvec ws 0 i))))

(def ^:private merge-pairs
  [['(anti_symmetric aboveR) '(aboveR I2 I0) '(aboveR I0 I2)]
   ['(functional fnR) '(fnR A1 I0) '(fnR A1 I2)]])

(deftest a-merge-lands-at-the-most-general-reader-in-every-order
  ;; The edge `(genlCx hi CxL1)` gives the two readers different gains, so they are two
  ;; groups, and `lo` sees the merge `hi` holds.  The second spelling of the pair is
  ;; there because an unordered iteration of `#{CxH4 CxK4}` visits the lower context first
  (doseq [[mark f0 f1] merge-pairs
          [hi lo]      '[[CxL2 CxL3] [CxH4 CxK4]]
          :let [ws  (merge-world mark f0 f1 hi lo 'CxUniverse)
                got (for [w      (rotations ws)
                          whole? [false true]]
                      (placements w whole? '(equals I0 I2) [hi lo 'CxL1 'CxN2]))]]
    (is (= (repeat (* 2 (count ws)) #{hi}) got) (str (first mark) " " hi))))

(defn- believed-below-except
  "Whether `lo` believes `(equals I0 I2)` once `writes` are loaded in order, the last as
  the edit, and an `except` of the merge `hi` stores is asserted in `hi`; nil when `hi`
  stores none."
  [writes whole? hi lo]
  (let [w  (run-world (pop writes) [(peek writes)] whole?)
        kb (:kb w)]
    (try
      (when-let [h (v/handle-of kb '(equals I0 I2) hi)]
        (binding [checks/*whole-move-sweeps?* whole?]
          (v/assert kb (list 'except (list 'sentexHandle h)) hi {:strength M}))
        (boolean (seq (v/ask kb '(equals I0 I2) lo))))
      (finally (close! w)))))

(deftest a-merge-below-a-more-general-one-is-retired-in-every-order
  ;; CxN2 sits under CxL1, so `lo` sees both facts and the mark through CxN2 before `hi`
  ;; sees CxL1, and stores the merge first in the orders that write `(genlCx hi CxL1)`
  ;; late.  `hi`'s merge then covers it, and an `except` of `hi`'s merge hides the pair
  ;; at `lo` in every order.  In the second world `lo` holds its own merge as a sibling
  ;; of `hi` until the edge `(genlCx lo hi)` puts it under `hi`
  (doseq [[mark f0 f1] merge-pairs
          :let [sibling [['(genlCx CxA CxUniverse) 'CxUniverse M]
                         ['(genlCx CxB CxUniverse) 'CxUniverse M]
                         [f0 'CxA M]
                         [f1 'CxB M]
                         [mark 'CxUniverse nil]
                         ['(genlCx CxQ CxA) 'CxUniverse M]
                         ['(genlCx CxQ CxB) 'CxUniverse M]
                         ['(genlCx CxL3 CxA) 'CxUniverse M]
                         ['(genlCx CxL3 CxB) 'CxUniverse M]
                         ['(genlCx CxL3 CxQ) 'CxUniverse M]]]
          [ws hi lo] [[(merge-world mark f0 f1 'CxL2 'CxL3 'CxL1) 'CxL2 'CxL3]
                      [sibling 'CxQ 'CxL3]]
          :let [got (for [w      (rotations ws)
                          whole? [false true]]
                      [(placements w whole? '(equals I0 I2) [hi lo]) (believed-below-except w whole? hi lo)])]]
    (is (= (repeat (* 2 (count ws)) [#{hi} false]) got) (str (first mark) " " hi))))

(defn- stored-in
  "The contexts of `ctxs` storing `s` in `kb`."
  [kb s ctxs]
  (into (sorted-set) (filter (fn [c] (some #{s} (map v/sentence-of (v/sentexes-in-context kb c))))) ctxs))

(deftest a-merge-whose-cover-an-except-hides-is-derived-again-in-every-order
  ;; CxL3 sees the pair through CxL2 and through CxN2 under CxL1.  An `except` of the
  ;; edge `(genlCx CxL2 CxL1)` stated in CxL2 hides CxL2's merge from CxL3, since the
  ;; merge rests on that edge, so the merge covers nothing at CxL3 and CxL3 derives its own
  (doseq [[mark f0 f1] merge-pairs
          :let [ws  (merge-world mark f0 f1 'CxL2 'CxL3 'CxL1)
                got (for [w      (rotations ws)
                          whole? [false true]]
                      (let [{:keys [kb] :as world} (run-world (pop w) [(peek w)] whole?)]
                        (try
                          (binding [checks/*whole-move-sweeps?* whole?]
                            (v/assert kb (list 'except (v/sentex-handle (v/handle-of kb '(genlCx CxL2 CxL1) 'CxUniverse)))
                                      'CxL2 {:strength M}))
                          [(stored-in kb '(equals I0 I2) '[CxL2 CxL3]) (boolean (seq (v/ask kb '(equals I0 I2) 'CxL3)))]
                          (finally (close! world)))))]]
    (is (= (repeat (* 2 (count ws)) ['#{CxL2 CxL3} true]) got) (str (first mark)))))

(deftest a-merge-a-class-above-covers-is-retired-in-every-order
  ;; CxL2 merges I0 and I1, and CxL1 holds I1 and I2 in one class by a merge or by a
  ;; stated equality, so CxL3 sees I0 and I2 in one class: it derives no merge of the pair
  ;; when the class arrives first, and its merge is retired when the class arrives last
  (doseq [[label i12] [[:merged '[[(aboveR I2 I1) CxL1 :monotonic] [(aboveR I1 I2) CxL1 :monotonic]]]
                       [:stated '[[(equals I1 I2) CxL1 :monotonic]]]]
          :let [ws  (into '[[(genlCx CxL1 CxUniverse) CxUniverse :monotonic]
                            [(genlCx CxL2 CxL1) CxUniverse :monotonic]
                            [(genlCx CxL3 CxL2) CxUniverse :monotonic]
                            [(anti_symmetric aboveR) CxUniverse nil]
                            [(aboveR I1 I0) CxL1 :monotonic]
                            [(aboveR I0 I1) CxL2 :monotonic]
                            [(aboveR I2 I0) CxL1 :monotonic]
                            [(aboveR I0 I2) CxL3 :monotonic]]
                          i12)
                got (for [w      (rotations ws)
                          whole? [false true]]
                      (placements w whole? '(equals I0 I2) '[CxL1 CxL2 CxL3]))]]
    (is (= (repeat (* 2 (count ws)) #{}) got) (str label))))

(deftest a-recover-retires-a-stored-merge-a-more-general-one-covers
  ;; with `special/covered-merges` answering nil, the orders that write
  ;; `(genlCx CxL2 CxL1)` late store CxL3's merge beside CxL2's.  `recover` retires
  ;; CxL3's, and an `except` of CxL2's merge then hides the pair at CxL3
  (doseq [[mark f0 f1] merge-pairs
          :let [ws  (merge-world mark f0 f1 'CxL2 'CxL3 'CxL1)
                got (for [w (rotations ws)]
                      (let [{:keys [kb] :as world} (with-redefs [special/covered-merges (constantly nil)]
                                                     (run-world (pop w) [(peek w)] false))]
                        (try
                          (let [written (stored-in kb '(equals I0 I2) '[CxL2 CxL3])]
                            (v/recover kb)
                            (let [recovered (stored-in kb '(equals I0 I2) '[CxL2 CxL3])]
                              (v/assert kb (list 'except (v/sentex-handle (v/handle-of kb '(equals I0 I2) 'CxL2)))
                                        'CxL2 {:strength M})
                              [written recovered (boolean (seq (v/ask kb '(equals I0 I2) 'CxL3)))]))
                          (finally (close! world)))))]]
    (is (some #(= '#{CxL2 CxL3} (first %)) got) (str (first mark) ": an order stores both merges"))
    (is (= (repeat (count ws) ['#{CxL2} false]) (map rest got)) (str (first mark)))))

(deftest a-seeded-world-edited-or-asserted-singly-in-another-order-believes-alike
  ;; `seeded-worlds-agree` loads each world in its generated order, the edit as one
  ;; `v/edit!`; this asserts every write of the world singly in a shuffled order.  Seed 7
  ;; stores a merge at CxL3 that a merge at CxL2 covers in the shuffled order
  (doseq [seed [7]
          :let [[base edit] (gen-world seed)
                ctxs (map symbol (world-contexts base edit))
                l    (java.util.ArrayList. ^java.util.Collection (into base edit))
                _    (java.util.Collections/shuffle l (Random. (+ 1000 seed)))
                ws   (vec l)
                a    (run-world base edit false)
                b    (run-world ws [] false)]]
    (try
      (let [ra (reading (:kb a) ctxs)
            rb (reading (:kb b) ctxs)]
        (is (= [] (vec (for [c ctxs
                             :let [x (get-in ra [c :in]) y (get-in rb [c :in])]
                             :when (not= x y)]
                         [c (set/difference x y) (set/difference y x)])))
            (str "seed " seed)))
      (finally (close! a) (close! b)))
    (is (= [] (disagreements (pop ws) [(peek ws)])) (str "seed " seed ": split and whole"))))

(deftest an-edge-giving-a-membership-convicts-alike
  ;; constraint-only: the edge shows the lower context a membership that convicts a
  ;; declared fact stated there, through the disjointness of the declared type
  (let [base (into upper [['(genl cat_t thing) 'CxUniverse M]
                          ['(disjoint kind_t cat_t) 'CxUniverse M]
                          ['(genlCx CxL CxUniverse) 'CxUniverse M]
                          ['(genlCx CxW CxUniverse) 'CxUniverse M]
                          ['(cat_t I0) 'CxW M]
                          ['(declR I0 Y) 'CxL M]
                          ['(declR I1 Y) 'CxL M]])
        edit [['(genlCx CxL CxW) 'CxUniverse M]]
        in   (fn [] (let [w (run-world base edit false)]
                      (try (:in (get (reading (:kb w) ['CxL]) 'CxL)) (finally (close! w)))))]
    (binding [*assertive?* false]
      (is (= [] (disagreements base edit)))
      (testing "the edge holds the convicted fact out and leaves the other in"
        (let [in (in)]
          (is (not (contains? in '(declR I0 Y))))
          (is (contains? in '(declR I1 Y)))))
      (testing "and a sweep that reads no hold the gain moves disagrees"
        (with-redefs-fn {#'checks/gained-ends-candidates
                         (fn [& _] (when-not checks/*whole-move-sweeps?* []))}
          #(is (seq (disagreements base edit))))))))

(deftest the-gain-guard-is-needed
  ;; with the guard broken, a mark stated where the edge brings the reader is read as a
  ;; plain fact, and the pair it convicts among the facts the reader already saw goes
  ;; unmerged.  The mark is stated before the edge, so its own arrival merged nothing.
  (let [base (into base-l [['(genlCx CxW CxUniverse) 'CxUniverse M]
                           ['(anti_symmetric aboveS) 'CxW nil]
                           ['(aboveS C0 C1) 'CxL M] ['(aboveS C1 C0) 'CxL M]])
        edit [['(genlCx CxL CxW) 'CxUniverse M]]]
    (is (= [] (disagreements base edit)))
    (is (contains? (get (reads-of base edit #(= 'equals (first %))) 'CxL) '(equals C0 C1)))
    (with-redefs-fn {#'special/plain-gain? (fn [_ _ _] true)}
      #(is (seq (disagreements base edit))))))

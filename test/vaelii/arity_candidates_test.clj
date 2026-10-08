;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.arity-candidates-test
  "The arity candidate index (`arity/recompute-arity`) against its own definition.

  A shape `[f n]` is a candidate when a predicate above `f` stores an exact length other
  than `n`, or `f` stores an `arityMin` above `n`; a pair `[f g]` is one when `g` is above
  `f` and the two store different exact lengths.  The index keeps the lengths above each
  type and moves them per write, and names a functor's pairs from its closure cut to the
  bound predicates (`tax/genls-global-among`), so the oracle here reads the whole closure
  per functor and every index the KB holds must match it: after each write, rebuilt from
  storage, and rebuilt with the whole closure in place of the cut."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.arity :as arity]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(defn- held
  "The arity half of `kb`'s candidate index."
  [kb]
  (let [c @(reasoning/nogood-candidates kb)]
    {:cand-shapes (set (::arity/cand-shapes c))
     :pairs       (set (::arity/pairs c))
     :arity       (set (:arity c))
     :arity-pairs (set (:arity-pairs c))}))

(defn- oracle
  "The arity candidates by definition, off the bindings the index tracks, one whole
  `genls-global` closure per functor, and every stored record's shape."
  [kb]
  (let [c     @(reasoning/nogood-candidates kb)
        bs    (::arity/bindings c)
        tax   (reasoning/taxonomy kb)
        recs  (:records kb)
        shape @#'arity/fact-shape
        own   (fn [q kind] (into #{} (keep (fn [[_ [k v]]] (when (= k kind) v))) (get bs q)))
        cand  (into #{}
                    (filter (fn [[f n]]
                              (or (some (fn [g] (some #(not= n %) (own g :exact)))
                                        (tax/genls-global tax f))
                                  (some #(> % n) (own f :min)))))
                    (into #{} (keep #(some-> (p/get-sentex recs %) shape)) (p/sentex-ids recs)))
        pairs (into #{}
                    (for [f (keys bs)
                          :let [o (own f :exact)]
                          :when (seq o)
                          g (tax/genls-global tax f)
                          :let [og (own g :exact)]
                          :when (and (not= g f) (seq og) (some (fn [a] (some #(not= a %) og)) o))]
                      [f g]))]
    {:cand-shapes cand
     :pairs       pairs
     :arity       (into #{} (filter #(contains? cand (some-> (p/get-sentex recs %) shape)))
                        (p/sentex-ids recs))
     :arity-pairs (into #{} (for [pr pairs, q pr, [h [k]] (get bs q) :when (= :exact k)] h))}))

(defn- random-stream
  "A seeded shuffle of predicate and type `genl` edges (mostly downhill, some closing a
  cycle), length bindings in every spelling, and tuples of one to three arguments."
  [^java.util.Random rnd]
  (let [pick  (fn [v] (v (.nextInt rnd (count v))))
        preds (vec (repeatedly 8 #(tu/fresh-term :predicate 'rel)))
        types (vec (repeatedly 10 #(tu/fresh-term :predicate 'kind)))
        inds  (vec (repeatedly 4 #(tu/fresh-term :individual 'Thing)))
        edge  (fn [v] (let [i (.nextInt rnd (count v))
                            j (if (< (.nextInt rnd 10) 1)
                                (.nextInt rnd (count v))
                                (+ i (.nextInt rnd (- (count v) i))))]
                        (when (not= i j) (list 'genl (v i) (v j)))))
        bind  (fn [] (let [q (pick (if (< (.nextInt rnd 4) 1) types preds))]
                       (case (int (.nextInt rnd 5))
                         0 (list 'arity q (inc (.nextInt rnd 3)))
                         1 (list 'arity q (inc (.nextInt rnd 3)))
                         2 (list 'binary_predicate q)
                         3 (list 'arityMin q (inc (.nextInt rnd 3)))
                         4 (list 'variable_arity q))))
        tuple (fn [] (let [q (pick (if (< (.nextInt rnd 2) 1) types preds))]
                       (apply list q (repeatedly (inc (.nextInt rnd 3)) #(pick inds)))))]
    (->> (concat (keep (fn [_] (edge preds)) (range 10))
                 (keep (fn [_] (edge types)) (range 14))
                 (repeatedly 8 bind)
                 (repeatedly 24 tuple))
         (sort-by (fn [_] (.nextInt rnd))))))

(defn- assert-all!
  "Assert each of `stream`, and answer the handles stored, by sentence."
  [kb stream]
  (into {}
        (keep (fn [s]
                ;; a refused sentence (a cycle a wff check turns away) is simply not stored
                (when-let [h (try (v/assert kb s 'CxUniverse) (catch clojure.lang.ExceptionInfo _))]
                  [s h])))
        stream))

(def ^:private binding-functors '#{arity arityMin binary_predicate variable_arity})

(deftest the-arity-index-matches-its-definition-kept-rebuilt-and-read-whole
  (let [rnd     (java.util.Random. 5772)
        seen    (atom {:cand-shapes 0 :pairs 0 :pairs-dropped 0})
        handles (volatile! {})]
    (doseq [deferred? [false true], trial (range 10)]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (let [stream (random-stream rnd)
              where  (str (if deferred? "deferred" "plain") " trial " trial)]
          (let [stored (if deferred?
                         (v/with-deferred-settle kb (assert-all! kb stream))
                         (assert-all! kb stream))]
            (vreset! handles stored))
          (let [o (oracle kb)]
            (swap! seen #(merge-with + % {:cand-shapes (count (:cand-shapes o))
                                          :pairs       (count (:pairs o))})))
          (testing "kept up as facts arrive"
            (is (= (oracle kb) (held kb)) where))
          (decide/rebuild-candidates! kb)
          (let [rebuilt @(reasoning/nogood-candidates kb)]
            (testing "rebuilt from storage"
              (is (= (oracle kb) (held kb)) where))
            (testing "rebuilt with the whole closure in place of the cut"
              (with-redefs [tax/genls-global-among (fn [tax t _ _] (tax/genls-global tax t))]
                (decide/rebuild-candidates! kb))
              (is (= rebuilt @(reasoning/nogood-candidates kb)) where)))
          (testing "kept up as bindings leave, which replaces the pairs of what is below them"
            (let [before (:pairs (held kb))]
              (doseq [[s h] (sort-by (fn [_] (.nextInt rnd)) @handles)
                      :when (and (binding-functors (first s)) (< (.nextInt rnd 2) 1))]
                (v/retract! kb h))
              (swap! seen update :pairs-dropped + (count (remove (:pairs (held kb)) before)))
              (is (= (oracle kb) (held kb)) where)
              (decide/rebuild-candidates! kb)
              (is (= (oracle kb) (held kb)) (str where ", rebuilt")))))))
    (is (every? pos? (vals @seen)) (str "the streams reach both halves: " @seen))))

;; The index keeps what a rebuild computes per call (the exact lengths above each type, the
;; pairs by lower end) and moves it per write: a length arriving walks down only to the
;; types missing it, and a functor below it that held it changes only by the pair it forms
;; with the arriving binding.  Each write is checked, so a walk that stops early, a pair
;; not joined or a length a departure leaves behind shows at the write that caused it,
;; where the end-of-stream comparison above sees only what the later writes did not
;; repair.

(defn- write-checked!
  "Write each step of `steps` (a sentence to assert, or `[:retract s]`) and answer the
  steps after which the index differs from its definition."
  [kb steps]
  (let [stored (volatile! {})]
    (into []
          (keep (fn [step]
                  (if (vector? step)
                    (when-let [h (get @stored (second step))] (v/retract! kb h))
                    (when-let [h (try (v/assert kb step 'CxUniverse) (catch clojure.lang.ExceptionInfo _))]
                      (vswap! stored assoc step h)))
                  (when (not= (oracle kb) (held kb)) step)))
          steps)))

(def ^:private fixed-streams
  "Shapes a random stream reaches rarely, over the types `a` < `b` < `c` and the
  individuals `x`, `y`."
  {:joins-the-pair-of-a-functor-that-held-the-length
   (fn [a b c x _] [(list 'genl a b) (list 'genl b c) (list 'arity a 2) (list 'arity b 1)
                    (list 'arity c 1) (list a x) (list b x)])
   :joins-it-when-the-edge-arrives-last
   (fn [a b c _ _] [(list 'genl b c) (list 'arity a 2) (list 'arity b 1) (list 'arity c 3)
                    (list 'genl a b)])
   :joins-an-upper-end-with-no-new-length-for-a-conflict-below
   (fn [a b c _ _] [(list 'genl a b) (list 'arity a 2) (list 'arity b 1) (list 'arity c 1)
                    (list 'genl b c)])
   :keeps-a-length-from-above-after-the-binding-that-stopped-its-walk-leaves
   (fn [a b c x _] [(list 'genl a b) (list 'genl b c) (list a x) (list 'arity b 2)
                    (list 'arity c 2) [:retract (list 'arity b 2)] [:retract (list 'arity c 2)]])
   :two-lengths-on-one-predicate
   (fn [a b _ x y] [(list 'genl a b) (list 'arity b 1) (list 'arity b 2) (list a x)
                    (list 'arity a 1) [:retract (list 'arity b 2)] (list a x y)])
   :a-cycle
   (fn [a b c x y] [(list 'genl a b) (list 'arity c 2) (list 'genl b c) (list b x y)
                    (list 'genl b a) (list 'arity a 1) (list a x) [:retract (list 'genl b c)]])
   :a-cover-arriving-after-the-tuple
   (fn [a b c x _] [(list 'arity c 2) (list a x) (list 'covering c a b) (list b x)
                    [:retract (list 'covering c a b)]])
   :a-tuple-arriving-after-the-cover
   (fn [a b c x _] [(list 'arity c 2) (list 'covering c a b) (list a x)])
   :an-edge-leaving-below-a-conflict
   (fn [a b c x _] [(list 'arity c 2) (list 'arity b 1) (list 'genl b c) (list 'genl a b)
                    (list 'arity a 3) (list a x) [:retract (list 'genl a b)]])})

(deftest the-arity-index-matches-its-definition-after-every-write
  (testing "the fixed shapes"
    (doseq [[k stream] fixed-streams]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (let [[a b c] (repeatedly 3 #(tu/fresh-term :predicate 'kind))
              [x y]   (repeatedly 2 #(tu/fresh-term :individual 'Thing))]
          (is (= [] (write-checked! kb (stream a b c x y))) (name k))))))
  (testing "seeded streams, their edges and bindings then leaving in a random order"
    (let [rnd (java.util.Random. 1729)
          bad (atom [])]
      (doseq [trial (range 12)]
        (tu/with-neutral-kb [kb tu/isolated-fresh]
          (let [stream (concat (random-stream rnd) (random-stream rnd))
                leave  (->> stream
                            (filter #(or (= 'genl (first %)) (binding-functors (first %))))
                            (sort-by (fn [_] (.nextInt rnd)))
                            (keep #(when (< (.nextInt rnd 3) 2) [:retract %])))]
            (swap! bad into (map #(vector trial %)) (write-checked! kb (concat stream leave))))))
      (is (= [] @bad)))))

(deftest a-cover-binds-its-parts-in-every-order
  ;; A cover installs a `genl` edge per part against its own handle, so a length bound on
  ;; the whole binds a part as an asserted edge would, whichever of the three arrives last.
  (let [answers (atom #{})]
    (doseq [order [[:bind :tuple :cover] [:bind :cover :tuple] [:cover :bind :tuple]
                   [:tuple :bind :cover] [:tuple :cover :bind] [:cover :tuple :bind]]]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (let [[whole part other] (repeatedly 3 #(tu/fresh-term :predicate 'kind))
              [x y]              (repeatedly 2 #(tu/fresh-term :individual 'Thing))
              s                  {:bind  (list 'arity whole 1)
                                  :cover (list 'covering whole part other)
                                  :tuple (list part x y)}
              hs                 (into {} (for [k order] [k (v/assert kb (s k) 'CxUniverse)]))]
          (swap! answers conj [(v/believed? kb (:tuple hs) 'CxUniverse)
                               (= (oracle kb) (held kb))]))))
    (is (= #{[false true]} @answers))))

(deftest a-rebuild-reads-no-supertype-closure
  ;; A rebuild recomputes every tracked functor, and every type with an instance is one,
  ;; so a closure per functor there is the whole taxonomy materialized.  The cut reads
  ;; parents' cuts instead.
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [types (vec (repeatedly 30 #(tu/fresh-term :predicate 'kind)))
          [parentOf fatherOf] (repeatedly 2 #(tu/fresh-term :predicate 'rel))
          [a b c] (repeatedly 3 #(tu/fresh-term :individual 'Thing))]
      (doseq [i (range 1 (count types))]
        (v/assert kb (list 'genl (types i) (types (quot (dec i) 2))) 'CxUniverse)
        (v/assert kb (list (types i) a) 'CxUniverse))
      (v/assert kb (list 'arity parentOf 2) 'CxUniverse)
      (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
      (v/assert kb (list fatherOf a b c) 'CxUniverse)
      (let [before (held kb)
            reads  (atom 0)
            real   tax/genls-global]
        (with-redefs [tax/genls-global (fn [tax t] (swap! reads inc) (real tax t))]
          (decide/rebuild-candidates! kb))
        (is (zero? @reads) "no closure is read")
        (is (= before (held kb)) "and the index is the one kept up as facts arrived")
        (is (contains? (:cand-shapes before) [fatherOf 3])
            "which holds the ternary tuple under the binary super")))))

(deftest a-rebuild-reads-the-bound-predicates-only-under-a-conflict
  ;; Where every type binds its own length, as a converted ontology whose every collection
  ;; is a unary predicate does, the predicates bound to a length above a type are all its
  ;; supertypes, and cutting its closure to them is the closure again.  The lengths bound
  ;; above it are one, `{1}`: only a functor whose own length differs from one above it
  ;; reads the predicates, to name its pairs.
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [types (vec (repeatedly 30 #(tu/fresh-term :predicate 'kind)))
          [parentOf fatherOf] (repeatedly 2 #(tu/fresh-term :predicate 'rel))
          [a b c] (repeatedly 3 #(tu/fresh-term :individual 'Thing))]
      (doseq [i (range (count types))]
        (when (pos? i) (v/assert kb (list 'genl (types i) (types (quot (dec i) 2))) 'CxUniverse))
        (v/assert kb (list 'arity (types i) 1) 'CxUniverse)
        (v/assert kb (list (types i) a) 'CxUniverse))
      (v/assert kb (list 'arity parentOf 2) 'CxUniverse)
      (v/assert kb (list 'arity fatherOf 3) 'CxUniverse)
      (v/assert kb (list 'genl fatherOf parentOf) 'CxUniverse)
      (v/assert kb (list fatherOf a b c) 'CxUniverse)
      (let [before (held kb)
            reads  (atom [])
            union  tax/genls-global-union]
        ;; `genls-global-among` reads through `genls-global-union`, so this sees both
        (with-redefs [tax/genls-global-union (fn [tax t xf memo] (swap! reads conj t) (union tax t xf memo))]
          (decide/rebuild-candidates! kb))
        (is (= [fatherOf] @reads) "the one functor under a conflict reads the predicates")
        (is (= before (held kb)) "and the index is the one kept up as facts arrived")
        (is (= #{[fatherOf parentOf]} (:pairs before)) "which holds the pair")))))

(deftest a-functor-under-a-conflict-reads-only-the-predicates-binding-another-length
  ;; Every type binds 1 and sits under a root binding 2, so every type is under a
  ;; conflict and names one pair, with the root.  Cut to every bound predicate its read is
  ;; its whole chain; cut to the predicates binding a length other than its own it is the
  ;; root alone.
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [types (vec (repeatedly 30 #(tu/fresh-term :predicate 'kind)))
          root  (tu/fresh-term :predicate 'top)
          a     (tu/fresh-term :individual 'Thing)]
      (v/assert kb (list 'arity root 2) 'CxUniverse)
      (doseq [i (range (count types))]
        (v/assert kb (list 'genl (types i) (if (pos? i) (types (quot (dec i) 2)) root)) 'CxUniverse)
        (v/assert kb (list 'arity (types i) 1) 'CxUniverse)
        (v/assert kb (list (types i) a) 'CxUniverse))
      (let [before (held kb)
            cuts   (atom [])
            union  tax/genls-global-union]
        ;; `genls-global-among` reads through `genls-global-union`, so this sees both
        (with-redefs [tax/genls-global-union (fn [tax t xf memo] (let [r (union tax t xf memo)] (swap! cuts conj r) r))]
          (decide/rebuild-candidates! kb))
        (is (= (count types) (count @cuts)) "every type reads once")
        (is (every? #(= #{root} %) @cuts) "and reads the root alone")
        (is (= before (held kb)) "and the index is the one kept up as facts arrived")
        (is (= (into #{} (map (fn [t] [t root])) types) (:pairs before))
            "which pairs every type with the root")))))

(defn- edge-reach-tests
  "The `genl?-global` calls one `genl` edge makes, putting a fresh tracked type under the
  bottom of a chain of twelve types bound to one argument, on a KB holding `n` predicates
  under a conflict: each binds one argument under a root binding two."
  [n]
  (let [calls (atom nil)]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (let [root  (tu/fresh-term :predicate 'top)
            chain (vec (repeatedly 12 #(tu/fresh-term :predicate 'kind)))
            leaf  (tu/fresh-term :predicate 'kind)
            a     (tu/fresh-term :individual 'Thing)]
        (v/assert kb (list 'arity root 2) 'CxUniverse)
        (dotimes [_ n]
          (let [p (tu/fresh-term :predicate 'rel)]
            (v/assert kb (list 'genl p root) 'CxUniverse)
            (v/assert kb (list 'arity p 1) 'CxUniverse)))
        (doseq [i (range 1 (count chain))]
          (v/assert kb (list 'genl (chain i) (chain (dec i))) 'CxUniverse))
        (v/assert kb (list 'arity (chain 0) 1) 'CxUniverse)
        (v/assert kb (list leaf a) 'CxUniverse)
        (is (= n (count (::arity/at-conflict @(reasoning/nogood-candidates kb)))))
        (let [k    (atom 0)
              real tax/genl?-global]
          (with-redefs [tax/genl?-global (fn [tax sub super] (swap! k inc) (real tax sub super))]
            (v/assert kb (list 'genl leaf (peek chain)) 'CxUniverse))
          (reset! calls @k))
        (is (= (oracle kb) (held kb)))))
    @calls))

(deftest an-edge-arriving-asks-no-reachability-of-the-functors-under-a-conflict
  (is (= (edge-reach-tests 4) (edge-reach-tests 64))))

(defn- conflicts-below-mismatches
  "The terms `t` of `kb`'s taxonomy whose functors under a conflict below `t`, as
  `arity/conflicts-below` reads them, differ from `::at-conflict` filtered by
  `genl?-global`."
  [kb]
  (let [tax (reasoning/taxonomy kb)
        c   @(reasoning/nogood-candidates kb)
        ac  (::arity/at-conflict c)]
    (into []
          (remove (fn [t]
                    (= (into #{} (filter #(or (= t %) (tax/genl?-global tax % t))) ac)
                       (second (@#'arity/conflicts-below (decide/write-view tax) c t #{})))))
          (tax/types tax))))

(deftest the-functors-under-a-conflict-below-a-type-are-the-reachability-filter-s
  ;; A hub type above half the terms, bound to a length, puts most functors under a
  ;; conflict and most types above one.  Edges then leave, which leaves the kept set of
  ;; types above a conflict a superset.
  (let [rnd   (java.util.Random. 4099)
        found (atom 0)]
    (doseq [trial (range 8)]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (let [hub    (tu/fresh-term :predicate 'kind)
              stream (random-stream rnd)
              terms  (into #{} (comp (filter #(#{'genl 'arity 'arityMin} (first %))) (mapcat rest)
                                     (filter symbol?))
                           stream)
              hubbed (concat stream
                             [(list 'arity hub (inc (.nextInt rnd 2)))]
                             (keep #(when (< (.nextInt rnd 2) 1) (list 'genl % hub)) (sort terms)))
              stored (assert-all! kb (sort-by (fn [_] (.nextInt rnd)) hubbed))
              where  (str "trial " trial)]
          (swap! found + (count (::arity/at-conflict @(reasoning/nogood-candidates kb))))
          (is (= [] (conflicts-below-mismatches kb)) where)
          (doseq [[s h] (sort-by (fn [_] (.nextInt rnd)) stored)
                  :when (and (= 'genl (first s)) (< (.nextInt rnd 3) 1))]
            (v/retract! kb h))
          (is (= [] (conflicts-below-mismatches kb)) (str where ", edges left"))
          (decide/rebuild-candidates! kb)
          (is (= [] (conflicts-below-mismatches kb)) (str where ", rebuilt")))))
    (is (pos? @found) "the streams put functors under a conflict")))

;; A reader's binding for a functor with none of its own is read off the bound predicates
;; above it (`arity/bound-above`), each kept when the reader's ancestor set reaches it
;; (`tax/genls-asserted-among`).  The oracle is the definition: the closure over the edges
;; stated in the ancestor set, read whole (`tax/genls-asserted-in`).

(defn- reader-binding-by-definition
  "What binds `q`'s length at a reader with ancestor set `up`, read off `q`'s whole scoped
  closure."
  [kb bindings q up]
  (let [vis (fn [p] (@#'arity/visible-bindings kb bindings p up nil))
        own (vis q)]
    (cond
      (seq (:var own))   (when (= 1 (count (:min own)))
                           (let [[m hs] (first (:min own))] {:min m :grounds hs}))
      (seq (:exact own)) (when (= 1 (count (:exact own)))
                           (let [[n hs] (first (:exact own))] {:exact n :grounds hs}))
      :else
      (let [sup (into [] (keep (fn [p] (let [b (vis p)] (when (or (seq (:var b)) (seq (:exact b))) b))))
                      (sort (disj (tax/genls-asserted-in (reasoning/taxonomy kb) q up) q)))
            ns  (into #{} (mapcat (comp keys :exact)) sup)]
        (when (and (= 1 (count ns)) (not-any? #(seq (:var %)) sup))
          {:exact (first ns) :grounds (into #{} (mapcat #(mapcat val (:exact %))) sup)})))))

(deftest a-reader-s-binding-reads-the-bound-predicates-its-ancestor-set-reaches
  (let [rnd  (java.util.Random. 4111)
        seen (atom 0)
        bad  (atom [])]
    (doseq [trial (range 8)]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (tu/with-terms [CxAr CxBr CxCr]
          (doseq [[c up] [[CxAr 'CxUniverse] [CxBr CxAr] [CxCr 'CxUniverse]]]
            (v/assert kb (list 'genlCx c up) 'CxUniverse))
          (let [ctxs ['CxUniverse CxAr CxBr CxCr]]
            (doseq [s (random-stream rnd)]
              (try (v/assert kb s (ctxs (.nextInt rnd (count ctxs))))
                   (catch clojure.lang.ExceptionInfo _)))
            (let [c     @(reasoning/nogood-candidates kb)
                  bs    (::arity/bindings c)
                  tax   (reasoning/taxonomy kb)
                  above (@#'arity/bound-above tax bs)
                  recs  (:records kb)
                  fs    (into (into #{} (keep #(some-> (p/get-sentex recs %) (@#'arity/fact-shape) first))
                                    (p/sentex-ids recs))
                              (keys bs))]
              (doseq [cx ctxs
                      :let [up (tax/context-up-global tax cx)]
                      q (sort fs)
                      :let [want (reader-binding-by-definition kb bs q up)
                            got  (@#'arity/reader-binding kb bs above q up nil)]]
                (when want (swap! seen inc))
                (when (not= want got)
                  (swap! bad conj {:trial trial :context cx :functor q :want want :got got}))))))))
    (is (pos? @seen) "the streams bind a length at some reader")
    (is (= [] @bad))))

(deftest a-reader-s-bound-predicates-are-read-off-one-walk-from-the-functor
  ;; q → p0 → … → p5 stated in CxAr, each p bound to two arguments, and an edge stated in
  ;; CxCr, so CxAr's ancestor set misses a context stating a `genl` edge and the cut is
  ;; checked against the edges it states: one walk up from q answers the whole cut, where
  ;; a walk per bound predicate costs the cut times the reach
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (tu/with-terms [CxAr CxCr]
      (doseq [c [CxAr CxCr]] (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
      (let [q     (tu/fresh-term :predicate 'rel)
            ps    (vec (repeatedly 6 #(tu/fresh-term :predicate 'rel)))
            other (vec (repeatedly 2 #(tu/fresh-term :predicate 'rel)))]
        (doseq [[a b] (partition 2 1 (cons q ps))] (v/assert kb (list 'genl a b) CxAr))
        (v/assert kb (list 'genl (first other) (second other)) CxCr)
        (doseq [p ps] (v/assert kb (list 'arity p 2) 'CxUniverse))
        (let [tax   (reasoning/taxonomy kb)
              up    (tax/context-up-global tax CxAr)
              walks (atom {})
              count! (fn [k real] (fn [& args] (swap! walks update k (fnil inc 0)) (apply real args)))]
          (with-redefs [tax/genl-path            (count! :path @#'tax/genl-path)
                        tax/reachable-filtered?  (count! :walk @#'tax/reachable-filtered?)
                        tax/visible-neighbours   (count! :nodes @#'tax/visible-neighbours)]
            (let [bs (::arity/bindings @(reasoning/nogood-candidates kb))]
              (is (= 6 (count (:grounds (@#'arity/reader-binding kb bs (@#'arity/bound-above tax bs)
                                                                 q up nil))))
                  "every bound predicate above q grounds the conviction")))
          (is (nil? (:path @walks)) "no path is read per bound predicate")
          (is (nil? (:walk @walks)) "and no pair walks")
          (is (<= (:nodes @walks 0) 6) "one walk enters each node below the top once"))))))

;; A pair `[f g]` is a nogood at a reader whose ancestor set reaches `g` from `f` over
;; the edges it states and whose own visible exact lengths differ, `variable_arity`
;; neither.  The settle places one `contradicts` per exact binding of each end
;; (`chain/place-arities!`); the oracle reads `f`'s scoped closure whole.

(defn- descensions-by-definition
  [kb cands up]
  (let [bs  (::arity/bindings cands)
        tax (reasoning/taxonomy kb)
        vis (fn [p] (@#'arity/visible-bindings kb bs p up nil))]
    (into #{}
          (mapcat (fn [[f g]]
                    (let [bf (vis f) bg (vis g)]
                      (when (and (empty? (:var bf)) (empty? (:var bg))
                                 (= 1 (count (:exact bf))) (= 1 (count (:exact bg)))
                                 (not= (key (first (:exact bf))) (key (first (:exact bg))))
                                 (contains? (tax/genls-asserted-in tax f up) g))
                        (for [hf (val (first (:exact bf))), hg (val (first (:exact bg)))]
                          #{hf hg})))))
          (::arity/pairs cands))))

(defn- descensions-believed
  "The member sets of the placed `:arity-descension` nogoods whose `contradicts` the reader
  `cx` sees and believes."
  [kb cands cx]
  (into #{} (comp (filter #(and (v/sees? kb cx (:context %)) (v/believed? kb (:id %) cx)))
                  (map #(into #{} (map second) (rest (:sentence %))))
                  (filter #(= :arity-descension (arity/kind-of cands %))))
        (v/sentexes-with-functor kb 'contradicts)))

(deftest a-reader-s-arity-pairs-are-the-ones-its-ancestor-set-reaches
  (let [rnd  (java.util.Random. 6421)
        seen (atom 0)
        bad  (atom [])]
    (doseq [trial (range 10)]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (tu/with-terms [CxAr CxBr CxCr]
          (doseq [[c up] [[CxAr 'CxUniverse] [CxBr CxAr] [CxCr 'CxUniverse]]]
            (v/assert kb (list 'genlCx c up) 'CxUniverse))
          (let [ctxs ['CxUniverse CxAr CxBr CxCr]]
            (doseq [s (random-stream rnd)]
              (try (v/assert kb s (ctxs (.nextInt rnd (count ctxs))))
                   (catch clojure.lang.ExceptionInfo _)))
            (let [cands (decide/synced kb)
                  tax   (reasoning/taxonomy kb)]
              (doseq [cx   ctxs
                      :let [up   (tax/context-up-global tax cx)
                            want (descensions-by-definition kb cands up)
                            got  (descensions-believed kb cands cx)]]
                (swap! seen + (count want))
                (when (not= want got)
                  (swap! bad conj {:trial trial :context cx :want want :got got}))))))))
    (is (pos? @seen) "the streams relate some pairs of differing lengths")
    (is (= [] @bad))))

(deftest a-reader-stops-reading-the-bindings-above-once-two-lengths-show
  ;; q binds nothing and sits under a chain of twenty predicates bound to one argument
  ;; with one bound to two at its top: two lengths above leave q unbound, which the
  ;; reader learns from two of the twenty-one bindings
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [q     (tu/fresh-term :predicate 'rel)
          chain (vec (repeatedly 20 #(tu/fresh-term :predicate 'rel)))
          top   (tu/fresh-term :predicate 'rel)
          ind   #(tu/fresh-term :individual 'Thing)]
      (doseq [[a b] (partition 2 1 (concat [q] chain [top]))]
        (v/assert kb (list 'genl a b) 'CxUniverse))
      (doseq [p chain] (v/assert kb (list 'arity p 1) 'CxUniverse))
      (v/assert kb (list 'arity top 2) 'CxUniverse)
      (v/assert kb (list q (ind) (ind) (ind)) 'CxUniverse)
      (let [tax   (reasoning/taxonomy kb)
            cands (decide/synced kb)
            bs    (::arity/bindings cands)
            calls (atom 0)
            real  @#'arity/visible-bindings]
        (is (contains? (::arity/cand-shapes cands) [q 3]) "the ternary shape is a candidate")
        (with-redefs [arity/visible-bindings (fn [& args] (swap! calls inc) (apply real args))]
          (is (nil? (@#'arity/reader-binding kb bs (@#'arity/bound-above tax bs) q
                                             (tax/context-up-global tax 'CxUniverse) nil))
              "q is unbound, so its tuple breaks nothing"))
        (is (<= @calls 3) (str @calls " bindings read"))))))

(defn- descension-pairs
  "Six predicates bound to three arguments under one bound to two, every binding and
  edge a `:monotonic` premise in CxUniverse: six `:arity-descension` pairs."
  [kb]
  (let [M   {:strength :monotonic}
        hi  (tu/fresh-term :predicate 'rel)
        los (vec (repeatedly 6 #(tu/fresh-term :predicate 'rel)))]
    (v/assert kb (list 'arity hi 2) 'CxUniverse M)
    (doseq [lo los]
      (v/assert kb (list 'arity lo 3) 'CxUniverse M)
      (v/assert kb (list 'genl lo hi) 'CxUniverse M))))

(deftest a-reader-reads-each-pair-of-monotonic-bindings-as-hard
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (descension-pairs kb)
    (is (= 6 (count (filter #(= :arity-descension (:kind %)) (v/conflicts kb)))))
    (is (= 6 (count (v/sentexes-with-functor kb 'contradicts))) "each pair is placed")
    (is (empty? (v/sentexes-with-functor kb 'defeat)) "and defeats no binding")))

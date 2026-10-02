;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.separable-frame-test
  "An unscoped separation frame reads its type's supertypes cut to the separable ones.

  `separation-frame*` asks of `a`'s supertypes only which are declared disjoint from
  something, members of a disjoint metatype, sibling-disjoint parents or partition parts,
  save the sibling arm's chain under a marked parent.  Unscoped it reads the closure cut
  to those (`tax/separable-genls`), built from the parents' cuts, where it read the whole
  closure of every type it framed: the first membership sync of a large KB's recover
  framed nearly every type and overran the closure cache.  Every answer must be the one
  the whole closure gives."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(defn- whole-closure-frames
  "Run `f` with every unscoped frame reading the whole closure, as before the cut."
  [f]
  (with-redefs [tax/separable-genls (fn [tax a] (tax/genls-global tax a))]
    (f)))

(defn- shuffle-with [^java.util.Random rnd coll]
  (sort-by (fn [_] (.nextInt rnd)) coll))

(defn- random-forest!
  "Three hierarchies of fifteen types, each type under one or two earlier types of its
  own block, and separations of every kind: declared pairs across blocks, a disjoint
  metatype, sibling-disjoint parents and a partition.  Answers the types."
  [kb ^java.util.Random rnd]
  (let [blocks (vec (for [_ (range 3)] (vec (repeatedly 15 #(tu/fresh-term :type 'kind_t)))))
        types  (into [] cat blocks)
        pick   (fn [v] (v (.nextInt rnd (count v))))
        try!   (fn [s] (try (v/assert kb s 'CxUniverse) (catch clojure.lang.ExceptionInfo _)))]
    (doseq [blk blocks, i (range 1 (count blk))]
      (try! (list 'genl (blk i) (blk (.nextInt rnd i))))
      (when (< (.nextInt rnd 3) 1) (try! (list 'genl (blk i) (blk (.nextInt rnd i))))))
    (dotimes [_ 2]
      (let [[x y] (take 2 (shuffle-with rnd blocks))]
        (try! (list 'disjoint (pick x) (pick y)))))
    (let [species (tu/fresh-term :type 'species_t)]
      (doseq [ty (repeatedly 3 #(pick types))] (try! (list species ty)))
      (try! (list 'disjoint_metatype species)))
    (dotimes [_ 2] (try! (list 'sibling_disjoint (pick types))))
    (let [blk (pick blocks)]
      (try! (list 'partition (blk 0) (pick blk) (pick blk))))
    types))

(deftest an-unscoped-frame-answers-what-the-whole-closure-answers
  (let [rnd  (java.util.Random. 4669)
        seen (atom 0)]
    (dotimes [trial 8]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (let [types (random-forest! kb rnd)
              tax   (reasoning/taxonomy kb)
              ask   (fn [] (into {} (for [a types, b types] [[a b] (tax/disjoint? tax a b)])))
              cut   (ask)
              whole (whole-closure-frames ask)]
          (swap! seen + (count (filter val cut)))
          (is (= whole cut) (str "trial " trial))
          (testing "and asked again, off the cuts the cache now holds"
            (is (= whole (ask)) (str "trial " trial))))))
    (is (pos? @seen) "the forests separate some pairs")))

(deftest a-frame-over-types-under-no-separation-reads-no-closure
  ;; A type under no separable type answers false without its closure: the cut of every
  ;; type is built from its parents' and is empty.
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [types (vec (repeatedly 30 #(tu/fresh-term :type 'kind_t)))
          [x y] (repeatedly 2 #(tu/fresh-term :type 'apart_t))]
      (doseq [i (range 1 (count types))]
        (v/assert kb (list 'genl (types i) (types (quot (dec i) 2))) 'CxUniverse))
      (v/assert kb (list 'disjoint x y) 'CxUniverse)
      (let [tax   (reasoning/taxonomy kb)
            reads (atom 0)
            real  tax/genls-global]
        (with-redefs [tax/genls-global (fn [t a] (swap! reads inc) (real t a))]
          (is (not-any? #(tax/disjoint? tax % (types 0)) types) "no type there is separated"))
        (is (zero? @reads) "and no closure is read to find that")))))

(defn- whole-scoped-frames
  "Run `f` with every scoped frame reading the whole scoped closure, as before the cut."
  [f]
  (let [genls-at @#'tax/genls-at]
    (with-redefs [tax/separable-genls-at (fn [tax a context] (genls-at tax a context))]
      (f))))

(defn- in-pass
  "Run `f` inside a read-only pass: the caches a reader's re-read binds."
  [f]
  (binding [tax/*closure-pass-cache*       (atom {})
            tax/*visible-neighbours-cache* (atom {})
            tax/*separation-frame-cache*   (atom {})]
    (f)))

(defn- filtered!
  "Give `child` a `genl` scope that filters: it excepts an edge between two fresh types,
  so its reads go through the scoped walk rather than the unscoped one."
  [kb child]
  (let [[u w] (repeatedly 2 #(tu/fresh-term :type 'aside_t))
        h     (v/assert kb (list 'genl u w) 'CxUniverse)]
    (v/assert kb (list 'except (list 'sentexHandle h)) child)
    (is (some? (#'tax/relation-scope (reasoning/taxonomy kb) :genl child))
        "the child's genl scope filters")))

(defn- cycle!
  "Make `x` and `y` subtypes of each other, the `x` → `y` edge stated in `cx` and the
  `y` → `x` one in `cy`.  `wff` refuses the edge closing a cycle, so it is formed the way
  a belief race forms one (docs/taxonomy.md): the first edge is defeated while the second
  arrives, then revived.  Answers the two edges' handles, nil for one refused."
  [kb x y cx cy]
  (let [try! (fn [s c o] (try (v/assert kb s c o) (catch clojure.lang.ExceptionInfo _)))
        h1   (try! (list 'genl x y) cx {})
        d    (try! (list 'not (list 'genl x y)) cx {:strength :monotonic})
        h2   (try! (list 'genl y x) cy {})]
    (when d (v/retract! kb d))
    [h1 h2]))

(deftest a-scoped-frame-answers-what-the-whole-scoped-closure-answers
  ;; the forest above, `genl` edges only a child context sees, and `except`s in a context
  ;; below it hiding some of them: each reader sees another hierarchy
  (let [rnd    (java.util.Random. 1618)
        seen   (atom 0)
        cyclic (atom 0)]
    (dotimes [trial 8]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (let [types (random-forest! kb rnd)
              child (tu/fresh-term :context 'CxChild)
              grand (tu/fresh-term :context 'CxGrand)
              try!  (fn [s c] (try (v/assert kb s c) (catch clojure.lang.ExceptionInfo _)))
              pick  #(types (.nextInt rnd (count types)))]
          (try! (list 'genlCx child 'CxUniverse) 'CxUniverse)
          (try! (list 'genlCx grand child) 'CxUniverse)
          (let [hs (vec (keep (fn [_] (try! (list 'genl (pick) (pick)) child)) (range 10)))]
            (doseq [h hs :when (zero? (.nextInt rnd 3))]
              (try! (list 'except (list 'sentexHandle h)) grand)))
          ;; components: one every reader sees whole, one closed by an edge only the child
          ;; sees, and one whose edge the lowest context excepts
          (cycle! kb (pick) (pick) 'CxUniverse 'CxUniverse)
          (cycle! kb (pick) (pick) 'CxUniverse child)
          (let [[h] (cycle! kb (pick) (pick) 'CxUniverse 'CxUniverse)]
            (when h (try! (list 'except (list 'sentexHandle h)) grand)))
          (when (seq (:scc (:genl @(reasoning/taxonomy kb)))) (swap! cyclic inc))
          (try! (list 'disjoint (pick) (pick)) child)
          (let [tax   (reasoning/taxonomy kb)
                ask   (fn [] (into {} (for [cx ['CxUniverse child grand], a types, b types]
                                        [[cx a b] (tax/disjoint? tax a b cx)])))
                whole (whole-scoped-frames ask)]
            (swap! seen + (count (filter val whole)))
            (is (= whole (ask)) (str "trial " trial ", off a pass"))
            (is (= whole (in-pass ask)) (str "trial " trial ", in a pass"))
            (testing "and asked again in the same pass, off the cuts it holds"
              (in-pass (fn [] (ask) (is (= whole (ask)) (str "trial " trial)))))))))
    (is (pos? @seen) "the forests separate some pairs")
    (is (pos? @cyclic) "and hold `genl` components")))

(deftest a-scoped-frame-in-a-pass-reads-a-component-every-reader-sees-as-one-unit
  ;; the chain below again, under a cycle of two types every context sees: the build
  ;; reads the component as one unit rather than handing back
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [types (vec (repeatedly 30 #(tu/fresh-term :type 'kind_t)))
          [p q] (repeatedly 2 #(tu/fresh-term :type 'loop_t))
          [x y] (repeatedly 2 #(tu/fresh-term :type 'apart_t))
          child (tu/fresh-term :context 'CxChild)]
      (v/assert kb (list 'genlCx child 'CxUniverse) 'CxUniverse)
      (cycle! kb p q 'CxUniverse 'CxUniverse)
      (v/assert kb (list 'genl (types 0) p) 'CxUniverse)
      (doseq [i (range 1 (count types))]
        (v/assert kb (list 'genl (types i) (types (quot (dec i) 2)))
                  (if (even? i) child 'CxUniverse)))
      (v/assert kb (list 'disjoint x y) 'CxUniverse)
      (filtered! kb child)
      (is (seq (:scc (:genl @(reasoning/taxonomy kb)))) "the two types are one component")
      (let [tax   (reasoning/taxonomy kb)
            reads (atom 0)
            real  tax/genls]
        (with-redefs [tax/genls (fn [t a c] (when (some #{a} types) (swap! reads inc)) (real t a c))]
          (in-pass #(is (not-any? (fn [t] (tax/disjoint? tax t x child)) types)
                        "no type there is separated")))
        (is (zero? @reads) "and no scoped closure is read to find that")))))

(deftest a-scoped-frame-in-a-pass-reads-no-closure-of-a-type-under-no-separation
  ;; `specs`/`genls` of the chain's types are never read: every cut is built from its
  ;; parents' and is empty
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [types (vec (repeatedly 30 #(tu/fresh-term :type 'kind_t)))
          [x y] (repeatedly 2 #(tu/fresh-term :type 'apart_t))
          child (tu/fresh-term :context 'CxChild)]
      (v/assert kb (list 'genlCx child 'CxUniverse) 'CxUniverse)
      (doseq [i (range 1 (count types))]
        (v/assert kb (list 'genl (types i) (types (quot (dec i) 2)))
                  (if (even? i) child 'CxUniverse)))
      (v/assert kb (list 'disjoint x y) 'CxUniverse)
      (filtered! kb child)
      (let [tax   (reasoning/taxonomy kb)
            reads (atom 0)
            real  tax/genls]
        (with-redefs [tax/genls (fn [t a c] (when (some #{a} types) (swap! reads inc)) (real t a c))]
          (in-pass #(is (not-any? (fn [t] (tax/disjoint? tax t (types 0) child)) types)
                        "no type there is separated")))
        (is (zero? @reads) "and no scoped closure is read to find that")))))

(deftest a-component-the-scope-breaks-reads-the-scoped-closure
  ;; `p`, `q` and `r` are one component, and the child excepts `q` → `r`: it still sees
  ;; the `p` ↔ `q` cycle, but not the whole component, so a build through it hands back
  ;; and the frame reads the scoped closure.  `a` sits under `p`, and `q` is declared
  ;; disjoint from `z`.
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [[p q r a z] (map #(tu/fresh-term :type %) '[p_t q_t r_t a_t z_t])
          child       (tu/fresh-term :context 'CxChild)]
      (v/assert kb (list 'genlCx child 'CxUniverse) 'CxUniverse)
      (cycle! kb p q 'CxUniverse 'CxUniverse)
      (let [[qr] (cycle! kb q r 'CxUniverse 'CxUniverse)]
        (v/assert kb (list 'except (list 'sentexHandle qr)) child))
      (v/assert kb (list 'genl a p) 'CxUniverse)
      (v/assert kb (list 'disjoint q z) 'CxUniverse)
      (is (= 3 (count (:scc (:genl @(reasoning/taxonomy kb))))) "the three types are one component")
      (let [tax   (reasoning/taxonomy kb)
            ask   (fn [] (into {} (for [cx ['CxUniverse child], [x y] [[a z] [z a] [p z] [r z]]]
                                    [[cx x y] (tax/disjoint? tax x y cx)])))
            whole (whole-scoped-frames ask)]
        (is (get whole [child a z]) "`a` is separated from `z` at the child, through `q`")
        (is (= whole (in-pass ask)) "and read so in a pass")))))

(deftest a-frame-from-an-ancestor-set-answers-what-the-whole-closure-answers
  ;; the scoped forests again, each question asked from a reader's ancestor set, off a
  ;; pass: the cuts are held in the closure cache, so an edge that moves between two
  ;; reads must retire them
  (let [rnd  (java.util.Random. 2178)
        seen (atom 0)]
    (dotimes [trial 8]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (let [types (random-forest! kb rnd)
              child (tu/fresh-term :context 'CxChild)
              try!  (fn [s c] (try (v/assert kb s c) (catch clojure.lang.ExceptionInfo _)))
              pick  #(types (.nextInt rnd (count types)))]
          (try! (list 'genlCx child 'CxUniverse) 'CxUniverse)
          (dotimes [_ 6] (try! (list 'genl (pick) (pick)) child))
          (cycle! kb (pick) (pick) 'CxUniverse 'CxUniverse)
          (cycle! kb (pick) (pick) 'CxUniverse child)
          (let [tax  (reasoning/taxonomy kb)
                ups  (fn [] (for [cx ['CxUniverse child]] (tax/context-up-global tax cx)))
                ask  (fn [] (into {} (for [up (ups), a types, b types]
                                       [[up a b] (tax/disjoint? tax a b up)])))
                once (fn [phase]
                       (let [whole (whole-scoped-frames ask)]
                         (swap! seen + (count (filter val whole)))
                         (is (= whole (ask)) (str "trial " trial " " phase))
                         (is (= whole (ask)) (str "trial " trial " " phase ", held"))))]
            (once :before)
            (try! (list 'genl (pick) (pick)) child)
            (once :after)))))
    (is (pos? @seen) "the forests separate some pairs")))

(deftest a-frame-from-an-ancestor-set-reads-no-closure
  ;; the chain under a component, asked from an ancestor set holding only some of the
  ;; contexts asserting `genl` edges: no scoped or global closure of a chain type is read
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [types (vec (repeatedly 30 #(tu/fresh-term :type 'kind_t)))
          [p q] (repeatedly 2 #(tu/fresh-term :type 'loop_t))
          [x y] (repeatedly 2 #(tu/fresh-term :type 'apart_t))
          [child other] (repeatedly 2 #(tu/fresh-term :context 'CxChild))]
      (v/assert kb (list 'genlCx child 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx other 'CxUniverse) 'CxUniverse)
      (cycle! kb p q 'CxUniverse 'CxUniverse)
      (v/assert kb (list 'genl (types 0) p) 'CxUniverse)
      (doseq [i (range 1 (count types))]
        (v/assert kb (list 'genl (types i) (types (quot (dec i) 2)))
                  (if (even? i) child 'CxUniverse)))
      (v/assert kb (list 'genl x y) other)
      (v/assert kb (list 'disjoint x y) 'CxUniverse)
      (let [tax   (reasoning/taxonomy kb)
            up    (tax/context-up-global tax child)
            reads (atom 0)
            note! (fn [a] (when (some #{a} types) (swap! reads inc)))
            vis   @#'tax/closure-of-vis
            glob  @#'tax/closure-of]
        (is (some? (tax/asserting-contexts-in tax :genl up)) "the set omits a genl context")
        (with-redefs [tax/closure-of-vis (fn [t r d n s] (note! n) (vis t r d n s))
                      tax/closure-of     (fn [t r d n] (note! n) (glob t r d n))]
          (is (not-any? (fn [t] (tax/disjoint? tax t x up)) types) "no type there is separated"))
        (is (zero? @reads) "and no closure of a chain type is read to find that")))))

(deftest two-ancestor-sets-read-a-component-by-their-own-edges
  ;; `p`, `q` and `r` are one component; `r` → `q` is stated in `other`, which one
  ;; reader's ancestor set holds and the other's does not.  `t` sits under `r`, and `q`
  ;; is declared disjoint from `z`: the first reader separates `t` from `z` through `q`,
  ;; the second reaches nothing from `r`, whichever asks first
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [[p q r t z]   (map #(tu/fresh-term :type %) '[p_t q_t r_t t_t z_t])
          [other child] (repeatedly 2 #(tu/fresh-term :context 'CxChild))]
      (v/assert kb (list 'genlCx other 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx child 'CxUniverse) 'CxUniverse)
      (cycle! kb p q 'CxUniverse 'CxUniverse)
      (cycle! kb q r 'CxUniverse other)
      (v/assert kb (list 'genl t r) 'CxUniverse)
      (v/assert kb (list 'disjoint q z) 'CxUniverse)
      (let [tax (reasoning/taxonomy kb)
            ua  (tax/context-up-global tax other)
            ub  (tax/context-up-global tax child)]
        (is (= 3 (count (:scc (:genl @tax)))) "the three types are one component")
        (is (tax/disjoint? tax t z ua) "the reader seeing `r` → `q` separates `t`")
        (is (not (tax/disjoint? tax t z ub)) "and the other does not, after it")
        (is (tax/disjoint? tax t z ua) "nor does its reading move the first")))))

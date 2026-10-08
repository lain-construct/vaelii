;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.inherit-membership-test
  "A claim read off the extent tests a term's reach for membership and builds no closure.

  The claims bearing on a goal lie in the product of its preserved arguments' reaches.
  Reading the extent keeps the stored tuples in the product, one membership test per
  preserved argument, and weighing the extent against the product needs the product's
  size only up to the extent.  So a `genl` reach, scoped or not, is walked only up to a
  bound and held as a set, past which a membership is a reachability walk and the size a count
  that stops at a limit (`inherit/reaches?`, `inherit/reach-size`), and no closure is
  built through the closure cache.  The settle's discovery pass asks
  this of every stored claim of a preserving predicate, where a closure per argument term
  overran the closure cache on a large KB.  Every answer must be the one the whole reach
  gives."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu]))

(defn- whole-reach
  "Run `f` with every membership test and size read off the whole reach, as before."
  [f]
  (let [reach (deref #'inherit/reach)]
    (with-redefs [inherit/reaches?   (fn [kb poss x t context] (contains? (reach kb poss x context) t))
                  inherit/reach-size (fn [kb poss x context limit]
                                       (let [n (count (reach kb poss x context))]
                                         (if (> n limit) ##Inf n)))]
      (f))))

(defn- comparable [claims]
  (->> claims
       (map #(select-keys % [:polarity :tuple :handle :sentence :context :class]))
       (sort-by pr-str)
       vec))

(defn- world!
  "Two random hierarchies with diamonds, a binary predicate preserved along `genl` at
  both positions (the second inverted in half the worlds, and asymmetric in half), claims scattered over the
  hierarchies in either polarity and strength, and a child context whose own `genl`
  edges only it sees.  Answers `[pred as bs child]`."
  [kb ^java.util.Random rnd]
  (let [as    (vec (repeatedly 8 #(tu/fresh-term :type 'ia_t)))
        bs    (vec (repeatedly 8 #(tu/fresh-term :type 'ib_t)))
        pred  (tu/fresh-term :predicate 'relOf)
        child (tu/fresh-term :context 'CxChild)
        pick  (fn [v] (v (.nextInt rnd (count v))))
        try!  (fn [s c opts] (try (v/assert kb s c opts) (catch clojure.lang.ExceptionInfo _)))]
    (try! (list 'genlCx child 'CxUniverse) 'CxUniverse {})
    (doseq [v [as bs], i (range 1 (count v))]
      (try! (list 'genl (v i) (v (.nextInt rnd i))) 'CxUniverse {})
      (when (< (.nextInt rnd 3) 1) (try! (list 'genl (v i) (v (.nextInt rnd i))) 'CxUniverse {}))
      (when (< (.nextInt rnd 4) 1) (try! (list 'genl (v i) (v (.nextInt rnd i))) child {})))
    (try! (list 'transitiveInArgInverse pred 1 'genl) 'CxUniverse {})
    (try! (list (if (zero? (.nextInt rnd 2)) 'transitiveInArgInverse 'transitiveInArg) pred 2 'genl)
          'CxUniverse {})
    (when (zero? (.nextInt rnd 2)) (try! (list 'asymmetric pred) 'CxUniverse {}))
    (dotimes [_ 14]
      (let [s (list pred (pick as) (pick bs))]
        (try! (if (zero? (.nextInt rnd 3)) (list 'not s) s)
              (if (zero? (.nextInt rnd 4)) child 'CxUniverse)
              {:strength (if (zero? (.nextInt rnd 2)) :monotonic :default)})))
    [pred as bs child]))

(deftest a-claim-read-off-the-extent-is-the-one-the-whole-reach-reads
  (let [rnd  (java.util.Random. 8128)
        seen (atom 0)]
    (dotimes [trial 6]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (let [[pred as bs child] (world! kb rnd)
              goals (for [a as, b bs] (list pred a b))
              ask   (fn []
                      {:claims    (into {} (for [retrieval [:auto :extent :product]
                                                 from      ['CxUniverse child]
                                                 g         goals]
                                             [[retrieval from g]
                                              (binding [inherit/*retrieval* retrieval]
                                                (comparable (inherit/claims kb g from)))]))
                       :surviving (into {} (for [from ['CxUniverse child], g goals]
                                             [[from g] (comparable (inherit/surviving kb g from))]))
                       :denials   (into {} (for [g goals, s [g (list 'not g)]]
                                             [s (inherit/denial-readings kb s)]))})
              now   (ask)
              ;; every reach past the bound, so each membership is a walk
              walks (with-redefs [inherit/bounded-reach-limit 1] (ask))
              ;; and each term's reach read whole after its first membership
              whole (with-redefs [inherit/bounded-reach-limit 1 inherit/walks-before-reach 0] (ask))
              ;; with the whole reaches capped per term, and in all, so some fall back
              capped (with-redefs [inherit/bounded-reach-limit 1 inherit/walks-before-reach 0
                                   inherit/whole-reach-limit 3]
                       (ask))
              spent  (with-redefs [inherit/bounded-reach-limit 1 inherit/walks-before-reach 0
                                   inherit/whole-reach-budget 5]
                       (ask))
              ;; every question under one memo, as a discovery pass asks from many contexts
              shared (with-redefs [inherit/bounded-reach-limit 1 inherit/walks-before-reach 0]
                       (binding [inherit/*memo* (atom {})] (ask)))
              was   (whole-reach ask)]
          (swap! seen + (count (remove empty? (vals (:claims now)))))
          (doseq [k [:claims :surviving :denials]]
            (is (= (get was k) (get now k)) (str "trial " trial " " k))
            (is (= (get was k) (get walks k)) (str "trial " trial " " k ", walked"))
            (is (= (get was k) (get whole k)) (str "trial " trial " " k ", read whole"))
            (is (= (get was k) (get capped k)) (str "trial " trial " " k ", capped"))
            (is (= (get was k) (get spent k)) (str "trial " trial " " k ", budget spent"))
            (is (= (get was k) (get shared k)) (str "trial " trial " " k ", one memo"))))))
    (is (pos? @seen) "the worlds hold claims bearing on their goals")))

(deftest a-discovery-read-off-the-extent-builds-no-closure-within-the-bound-or-past-it
  ;; A deep chain on each side and a few claims: the extent is smaller than the product,
  ;; so the claims are read off the extent, and every reach is tested for membership.
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [as   (vec (repeatedly 40 #(tu/fresh-term :type 'ia_t)))
          bs   (vec (repeatedly 40 #(tu/fresh-term :type 'ib_t)))
          pred (tu/fresh-term :predicate 'relOf)]
      (doseq [v [as bs], i (range 1 (count v))]
        (v/assert kb (list 'genl (v i) (v (dec i))) 'CxUniverse))
      (v/assert kb (list 'transitiveInArgInverse pred 1 'genl) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse pred 2 'genl) 'CxUniverse)
      (v/assert kb (list pred (as 3) (bs 5)) 'CxUniverse)
      (v/assert kb (list 'not (list pred (as 30) (bs 30))) 'CxUniverse)
      ;; the matcher still reads predicates' closures for its fan; an argument's reach
      ;; is what the extent path no longer builds
      (let [terms (into (set as) bs)
            reads (atom 0)
            genls tax/genls
            specs tax/specs
            note! (fn [x] (when (contains? terms x) (swap! reads inc)))]
        (doseq [limit [1024 1]]
          (with-redefs [tax/genls (fn [t x c] (note! x) (genls t x c))
                        tax/specs (fn [t x c] (note! x) (specs t x c))
                        inherit/bounded-reach-limit limit]
            (is (seq (inherit/denial-readings kb (list pred (as 39) (bs 39))))
                "the leaves are denied by the negated claim above them")))
        (is (zero? @reads) "and no argument's closure is built to find that")))))

(deftest a-bounded-walk-reads-the-closure-it-stops-short-of
  ;; `tax/genls-within` / `specs-within` answer the closure a reader reads when it holds
  ;; at most the limit, else nil: edges only a child sees, and edges an `except` hides
  ;; from it
  (let [rnd (java.util.Random. 6174)]
    (dotimes [trial 6]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (let [ts    (vec (repeatedly 12 #(tu/fresh-term :type 'wk_t)))
              child (tu/fresh-term :context 'CxChild)
              try!  (fn [s c] (try (v/assert kb s c) (catch clojure.lang.ExceptionInfo _)))
              _     (try! (list 'genlCx child 'CxUniverse) 'CxUniverse)
              hs    (vec (keep (fn [i]
                                 (try! (list 'genl (ts i) (ts (.nextInt rnd i)))
                                       (if (zero? (.nextInt rnd 4)) child 'CxUniverse)))
                               (mapcat #(repeat 2 %) (range 1 (count ts)))))]
          (dotimes [_ 3] (try! (list 'except (list 'sentexHandle (hs (.nextInt rnd (count hs))))) child))
          (let [tx (reasoning/taxonomy kb)]
            (doseq [t ts, cx ['CxUniverse child nil], lim [0 1 2 3 5 8 100]
                    [within whole] [[tax/genls-within #(if %3 (tax/genls %1 %2 %3) (tax/genls-global %1 %2))]
                                    [tax/specs-within #(if %3 (tax/specs %1 %2 %3) (tax/specs-global %1 %2))]]]
              (let [c (whole tx t cx)]
                (is (= (when (<= (count c) lim) c) (within tx t cx lim))
                    (str "trial " trial " " t " at " cx " within " lim))))))))))

(deftest a-scoped-discovery-read-off-the-extent-builds-no-closure
  ;; the extent test above, asked from a context that sees one more edge
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [as    (vec (repeatedly 40 #(tu/fresh-term :type 'ia_t)))
          bs    (vec (repeatedly 40 #(tu/fresh-term :type 'ib_t)))
          pred  (tu/fresh-term :predicate 'relOf)
          child (tu/fresh-term :context 'CxChild)]
      (v/assert kb (list 'genlCx child 'CxUniverse) 'CxUniverse)
      (doseq [v [as bs], i (range 1 (count v))]
        (v/assert kb (list 'genl (v i) (v (dec i))) 'CxUniverse))
      (v/assert kb (list 'genl (as 39) (as 2)) child)
      (v/assert kb (list 'transitiveInArgInverse pred 1 'genl) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse pred 2 'genl) 'CxUniverse)
      (v/assert kb (list pred (as 3) (bs 5)) 'CxUniverse)
      (v/assert kb (list 'not (list pred (as 30) (bs 30))) 'CxUniverse)
      (let [terms (into (set as) bs)
            reads (atom 0)
            genls tax/genls
            specs tax/specs
            note! (fn [x] (when (contains? terms x) (swap! reads inc)))]
        (doseq [limit [1024 1]]
          (with-redefs [tax/genls (fn [t x c] (note! x) (genls t x c))
                        tax/specs (fn [t x c] (note! x) (specs t x c))
                        inherit/bounded-reach-limit limit]
            (is (seq (inherit/claims kb (list pred (as 39) (bs 39)) child))
                "the leaf reaches the negated claim above it")))
        (is (zero? @reads) "and no argument's closure is built to find that")))))

(deftest a-question-filters-each-edge-of-its-scoped-walks-once
  ;; past the bound every membership from a context is a walk of the edges it sees, and
  ;; each edge asks whether a supporter is believed there: the question keeps the
  ;; filtered neighbours, so a chain walked for many claims is filtered once per edge
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [as    (vec (repeatedly 30 #(tu/fresh-term :type 'ia_t)))
          bs    (vec (repeatedly 30 #(tu/fresh-term :type 'ib_t)))
          pred  (tu/fresh-term :predicate 'relOf)
          child (tu/fresh-term :context 'CxChild)
          [u w] (repeatedly 2 #(tu/fresh-term :type 'aside_t))]
      (v/assert kb (list 'genlCx child 'CxUniverse) 'CxUniverse)
      (doseq [v [as bs], i (range 1 (count v))]
        (v/assert kb (list 'genl (v i) (v (dec i))) 'CxUniverse))
      ;; the child excepts an edge elsewhere, so its genl scope filters
      (let [h (v/assert kb (list 'genl u w) 'CxUniverse)]
        (v/assert kb (list 'except (list 'sentexHandle h)) child))
      (v/assert kb (list 'transitiveInArgInverse pred 1 'genl) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse pred 2 'genl) 'CxUniverse)
      (doseq [i (range 0 30 3)]
        (v/assert kb (list pred (as i) (bs i)) 'CxUniverse))
      (let [filters (atom 0)
            ctxs    @#'tax/ctxs-visible?
            admits  @#'tax/scope-admits-supporter?]
        (with-redefs [tax/ctxs-visible?            (fn [& a] (swap! filters inc) (apply ctxs a))
                      tax/scope-admits-supporter? (fn [& a] (swap! filters inc) (apply admits a))
                      inherit/bounded-reach-limit 1]
          (is (seq (inherit/claims kb (list pred (as 29) (bs 29)) child))
              "the leaves reach the claims above them"))
        (is (<= @filters 150) (str @filters " edge filters for chains of 60 edges"))))))

(deftest a-term-asked-many-memberships-reads-its-reach-whole
  ;; twenty claims below one goal term, each argument a membership past the bound: the
  ;; question walks the first few and then reads the term's reach whole
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [as   (vec (repeatedly 30 #(tu/fresh-term :type 'ia_t)))
          bs   (vec (repeatedly 30 #(tu/fresh-term :type 'ib_t)))
          pred (tu/fresh-term :predicate 'relOf)]
      (doseq [v [as bs], i (range 1 (count v))]
        (v/assert kb (list 'genl (v i) (v (dec i))) 'CxUniverse))
      (v/assert kb (list 'transitiveInArgInverse pred 1 'genl) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse pred 2 'genl) 'CxUniverse)
      (doseq [i (range 20)]
        (v/assert kb (list pred (as i) (bs 0)) 'CxUniverse))
      (let [walks  (atom 0)
            global tax/genl?-global
            scoped tax/genl?]
        (with-redefs [tax/genl?-global            (fn [& a] (swap! walks inc) (apply global a))
                      tax/genl?                   (fn [& a] (swap! walks inc) (apply scoped a))
                      inherit/bounded-reach-limit 1
                      inherit/walks-before-reach  2]
          (binding [inherit/*retrieval* :extent]
            (is (= 20 (count (inherit/claims kb (list pred (as 29) (bs 29)) 'CxUniverse)))
                "every claim above the leaf is found")))
        (is (<= @walks 4) (str @walks " membership walks for twenty claims"))))))

(deftest a-reach-past-its-cap-is-never-held-whole
  ;; the twenty claims again, the goal term's reach thirty types and the cap five: every
  ;; membership stays a walk, and no whole reach is held
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [as   (vec (repeatedly 30 #(tu/fresh-term :type 'ia_t)))
          bs   (vec (repeatedly 30 #(tu/fresh-term :type 'ib_t)))
          pred (tu/fresh-term :predicate 'relOf)]
      (doseq [v [as bs], i (range 1 (count v))]
        (v/assert kb (list 'genl (v i) (v (dec i))) 'CxUniverse))
      (v/assert kb (list 'transitiveInArgInverse pred 1 'genl) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse pred 2 'genl) 'CxUniverse)
      (doseq [i (range 20)]
        (v/assert kb (list pred (as i) (bs 0)) 'CxUniverse))
      (let [walks  (atom 0)
            scoped tax/genl?]
        (with-redefs [tax/genl?                   (fn [& a] (swap! walks inc) (apply scoped a))
                      inherit/bounded-reach-limit 1
                      inherit/walks-before-reach  2
                      inherit/whole-reach-limit   5]
          (binding [inherit/*retrieval* :extent
                    inherit/*memo*      (atom {})]
            (is (= 20 (count (inherit/claims kb (list pred (as 29) (bs 29)) 'CxUniverse))))
            (is (every? #(= ::inherit/past %)
                        (vals (:map (get @inherit/*memo* [:whole-reach]))))
                "no whole reach is held")))
        (is (<= 20 @walks) "every membership walks")))))

(deftest a-pass-keeps-the-recent-whole-reaches-past-its-budget
  ;; one pass asks ten goal terms in turn, each reach about twenty-five types, with room
  ;; for one: the pass drops the oldest reach rather than leave every later term a walk
  ;; per membership
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [as   (vec (repeatedly 30 #(tu/fresh-term :type 'ia_t)))
          bs   (vec (repeatedly 30 #(tu/fresh-term :type 'ib_t)))
          pred (tu/fresh-term :predicate 'relOf)]
      (doseq [v [as bs], i (range 1 (count v))]
        (v/assert kb (list 'genl (v i) (v (dec i))) 'CxUniverse))
      (v/assert kb (list 'transitiveInArgInverse pred 1 'genl) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse pred 2 'genl) 'CxUniverse)
      (doseq [i (range 20)]
        (v/assert kb (list pred (as i) (bs 0)) 'CxUniverse))
      (let [walks  (atom 0)
            global tax/genl?-global
            scoped tax/genl?]
        (with-redefs [tax/genl?-global            (fn [& a] (swap! walks inc) (apply global a))
                      tax/genl?                   (fn [& a] (swap! walks inc) (apply scoped a))
                      inherit/bounded-reach-limit 1
                      inherit/walks-before-reach  2
                      inherit/whole-reach-budget  40]
          (binding [inherit/*retrieval* :extent
                    inherit/*memo*      (atom {})]
            (doseq [j (range 29 19 -1)]
              (is (= 20 (count (inherit/claims kb (list pred (as j) (bs 29)) 'CxUniverse)))
                  (str "every claim above " j " is found")))))
        (is (<= @walks 40) (str @walks " membership walks for ten goal terms"))))))

(deftest a-term-reads-its-reach-whole-after-a-couple-of-walks
  ;; the twenty claims below one goal term with the bounds as shipped but the bounded
  ;; reach: each preserved argument walks twice and then reads its reach whole
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [as   (vec (repeatedly 30 #(tu/fresh-term :type 'ia_t)))
          bs   (vec (repeatedly 30 #(tu/fresh-term :type 'ib_t)))
          pred (tu/fresh-term :predicate 'relOf)]
      (doseq [v [as bs], i (range 1 (count v))]
        (v/assert kb (list 'genl (v i) (v (dec i))) 'CxUniverse))
      (v/assert kb (list 'transitiveInArgInverse pred 1 'genl) 'CxUniverse)
      (v/assert kb (list 'transitiveInArgInverse pred 2 'genl) 'CxUniverse)
      (doseq [i (range 20)]
        (v/assert kb (list pred (as i) (bs 0)) 'CxUniverse))
      (let [walks  (atom 0)
            global tax/genl?-global
            scoped tax/genl?]
        (with-redefs [tax/genl?-global            (fn [& a] (swap! walks inc) (apply global a))
                      tax/genl?                   (fn [& a] (swap! walks inc) (apply scoped a))
                      inherit/bounded-reach-limit 1]
          (binding [inherit/*retrieval* :extent]
            (is (= 20 (count (inherit/claims kb (list pred (as 29) (bs 29)) 'CxUniverse))))))
        (is (<= @walks 4) (str @walks " membership walks for twenty claims"))))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.qcn-queue-test
  "The arc queue against the reference sweep — a parity oracle, not a behaviour test.

  `qcn/path-consistent` visits every triple once and then revisits only the ones a
  narrowing could have affected (PC-2).  `qcn/path-consistent-naive` re-sweeps all
  n(n-1)(n-2) triples every pass.  They must agree on **every** input: the same tightened
  network, constraint for constraint, and the same inconsistency verdict.  They can,
  because both compute the unique greatest fixpoint below the network they were handed —
  tightening only narrows and composition is monotone in ⊆, so which triples are visited
  in which order decides how many revisits it takes and nothing else.

  Randomized, over four algebras of different sizes (3, 8, 9 and 13 base relations) and
  several node counts, seeded so a failure reproduces from the seed printed with it.  The
  networks are deliberately harsh — random disjunctions on random pairs, so a good share
  of them are unsatisfiable and the verdict path is exercised as hard as the fixpoint."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing]]
            [vaelii.impl.interval :as iv]
            [vaelii.impl.orientation :as dir]
            [vaelii.impl.qcn :as qcn]
            [vaelii.impl.space :as space]))

;; ---- a toy point algebra, alongside the three that ship ------------------

(def ^:private point-universe #{:lt :eq :gt})

(def ^:private point-converse {:lt :gt, :eq :eq, :gt :lt})

(def ^:private point-composition
  {:lt {:lt #{:lt}    :eq #{:lt}    :gt point-universe}
   :eq {:lt #{:lt}    :eq #{:eq}    :gt #{:gt}}
   :gt {:lt point-universe  :eq #{:gt}    :gt #{:gt}}})

(def ^:private point-algebra
  {:universe point-universe
   :identity #{:eq}
   :compose  (fn [s1 s2]
               (into #{} (mapcat (fn [a] (mapcat (fn [b] (get-in point-composition [a b])) s2))) s1))
   :converse (fn [rels] (into #{} (map point-converse) rels))})

(def ^:private algebras
  {:point    point-algebra
   :rcc8     space/rcc8-algebra
   :cardinal dir/direction-algebra
   :allen    iv/allen-algebra})

;; ---- randomized networks -------------------------------------------------

(defn- rand-subset
  "A non-empty random subset of `universe`, skewed small — a network of near-universe
  constraints would tighten to nothing interesting, and one of singletons is almost always
  unsatisfiable, so the interesting shapes are in between."
  [^java.util.Random rnd universe]
  (let [v (vec (sort-by str universe))
        n (inc (.nextInt rnd (max 1 (quot (count v) 2))))]
    (loop [s #{}]
      (if (>= (count s) n) s (recur (conj s (nth v (.nextInt rnd (count v)))))))))

(defn- rand-network
  "A converse-consistent network over `nodes`: each of `edges` random pairs gets a random
  relation set and its mirror gets the converse, exactly as a reader writes them."
  [^java.util.Random rnd {:keys [universe converse]} nodes edges]
  (let [v (vec nodes)]
    (loop [net {}, e edges]
      (if (zero? e)
        net
        (let [i (nth v (.nextInt rnd (count v)))
              j (nth v (.nextInt rnd (count v)))]
          (if (= i j)
            (recur net (dec e))
            (let [rels (rand-subset rnd universe)]
              (recur (assoc net [i j] rels [j i] (converse rels)) (dec e)))))))))

(defn- nodes-of [net] (into #{} (mapcat identity) (keys net)))

(defn- compare-run
  "Run both implementations over one network and report the disagreement, if any."
  [algebra net]
  (let [ns    (nodes-of net)
        quick (qcn/path-consistent net ns algebra)
        naive (qcn/path-consistent-naive net ns algebra)]
    (when (not= quick naive)
      {:net net :queue quick :naive naive})))

(deftest the-queue-and-the-sweep-agree-over-randomized-networks
  (doseq [[nm algebra] algebras
          n            [4 6 9 13]
          seed         [1 2 3 4 5 6 7 8]]
    (let [rnd   (java.util.Random. (+ seed (* 100 n) (* 10000 (hash nm))))
          nodes (mapv #(symbol (str "N" %)) (range n))
          cases (for [_ (range 12)]
                  (rand-network rnd algebra nodes (inc (.nextInt rnd (* 2 n)))))
          bad   (keep #(compare-run algebra %) cases)]
      (is (empty? bad)
          (str nm " n=" n " seed=" seed " — the queue and the sweep disagree: "
               (pr-str (first bad)))))))

(deftest both-report-the-same-inconsistency-verdict
  ;; the verdict is what a query actually keys on, and it is the half a network-equality
  ;; check would silently pass if both implementations returned `:inconsistent` for
  ;; different reasons.  Counted, so the case is known to be exercised rather than hoped
  ;; to be.
  (let [algebra (:allen algebras)
        nodes   (mapv #(symbol (str "I" %)) (range 7))
        rnd     (java.util.Random. 4242)
        results (for [_ (range 200)]
                  (let [net (rand-network rnd algebra nodes 14)
                        ns  (nodes-of net)]
                    [(= :inconsistent (qcn/path-consistent net ns algebra))
                     (= :inconsistent (qcn/path-consistent-naive net ns algebra))]))]
    (is (every? (fn [[a b]] (= a b)) results))
    (is (some (fn [[a _]] a) results) "some of them really are unsatisfiable")
    (is (some (fn [[a _]] (not a)) results) "and some of them really are not")))

(deftest the-support-carrying-pass-tightens-to-the-same-network
  ;; the support variant runs the queue too, so it has to agree with the reference as
  ;; well — support rides along, it does not change what is derived
  (let [algebra (:rcc8 algebras)
        nodes   (mapv #(symbol (str "R" %)) (range 8))
        rnd     (java.util.Random. 7)]
    (doseq [_ (range 40)]
      (let [net (rand-network rnd algebra nodes 12)
            ns  (nodes-of net)
            sup (into {} (map-indexed (fn [i pair] [pair #{i}])) (keys net))
            a   (qcn/path-consistent-naive net ns algebra)
            b   (qcn/path-consistent-with-support net sup ns algebra)]
        (if (= :inconsistent a)
          (is (:inconsistent b))
          (is (= a (:network b))))))))

(deftest the-queue-does-not-depend-on-the-order-of-the-nodes
  ;; the property the queue must not have cost us: the node order decides which triples
  ;; are visited first and which pairs seed the queue, and it must still land on the same
  ;; fixpoint
  (let [algebra (:cardinal algebras)
        rnd     (java.util.Random. 99)
        nodes   (mapv #(symbol (str "P" %)) (range 6))]
    (doseq [_ (range 20)]
      (let [net (rand-network rnd algebra nodes 10)
            ns  (vec (nodes-of net))]
        (is (= 1 (count (set (for [_ (range 6)]
                               (qcn/path-consistent net (shuffle ns) algebra))))))))))

(deftest a-network-a-sweep-cannot-report-is-refused-by-both
  ;; the two shapes that are unsatisfiable *as given*, which no triple ever visits: both
  ;; drivers must take the same up-front exit
  (let [algebra (:point algebras)]
    (testing "a constraint handed in already empty"
      (let [net '{[A B] #{:lt} [B A] #{:gt} [X Y] #{} [Y X] #{}}]
        (is (= :inconsistent (qcn/path-consistent net (nodes-of net) algebra)))
        (is (= :inconsistent (qcn/path-consistent-naive net (nodes-of net) algebra)))))
    (testing "a diagonal claim that excludes the identity"
      (let [net '{[A A] #{:lt}}]
        (is (= :inconsistent (qcn/path-consistent net (nodes-of net) algebra)))
        (is (= :inconsistent (qcn/path-consistent-naive net (nodes-of net) algebra)))))))

;; ---- the warm start -------------------------------------------------------
;; `path-consistent-from` closes a network by starting from the answer for a network it
;; narrows and revisiting only the triples reading a pair that moved.  It has to agree with
;; the reference sweep at every step of a narrowing sequence — which is what a KB being
;; loaded produces, one arriving fact at a time.

(defn- narrowed
  "One arriving fact: intersect a random pair of `net` with a random relation set, writing
  the converse mirror, exactly as `qcn-kb`'s reader does.  Never widens, which is the
  precondition the warm start rests on."
  [^java.util.Random rnd {:keys [universe converse]} v net]
  (let [i (nth v (.nextInt rnd (count v)))
        j (nth v (.nextInt rnd (count v)))]
    (if (= i j)
      net
      (let [rels (rand-subset rnd universe)]
        (assoc net
               [i j] (set/intersection (get net [i j] universe) rels)
               [j i] (set/intersection (get net [j i] universe) (converse rels)))))))

(deftest the-warm-start-agrees-with-the-sweep-at-every-step-of-a-narrowing
  (doseq [[nm algebra] algebras
          n            [4 7 10]
          seed         [1 2 3 4 5]]
    (let [rnd   (java.util.Random. (+ seed (* 100 n) (* 10000 (hash nm))))
          ;; the nodes arrive over the walk rather than all at once, which is what a KB
          ;; being loaded does — a pair naming a node the previous network never held is
          ;; the ordinary case, not the corner one
          v     (mapv #(symbol (str "N" %)) (range n))
          ;; walk a narrowing sequence, warm-starting each step off the last answer and
          ;; checking it against a run that starts from nothing
          bad   (loop [net {}, prior nil, step 0, bad nil]
                  (if (or bad (= step (* 3 n)))
                    bad
                    (let [net'  (narrowed rnd algebra v net)
                          fresh (qcn/path-consistent-naive net' (nodes-of net') algebra)
                          ;; **no node set** on the warm call: a warm start is taken when
                          ;; facts have arrived, and an arriving fact names nodes neither
                          ;; the previous network nor the caller holds, so reading them off
                          ;; the merged network is part of the contract rather than a
                          ;; convenience.  Passing `nodes-of` here would hide a miss.
                          warm  (if (and prior (qcn/narrowing-of? net' net algebra))
                                  (qcn/path-consistent-from net' prior nil algebra)
                                  (qcn/path-consistent net' (nodes-of net') algebra))]
                      (recur net'
                             (when-not (= :inconsistent warm) warm)
                             (inc step)
                             (when (not= fresh warm)
                               {:step step :net net' :warm warm :fresh fresh})))))]
      (is (nil? bad)
          (str nm " n=" n " seed=" seed " — the warm start disagrees with the sweep: "
               (pr-str bad))))))

(deftest a-widening-is-not-a-narrowing
  ;; the precondition, stated as a test because a caller getting it wrong is the one way
  ;; the warm start returns a network tighter than the facts license
  (let [algebra (:point algebras)]
    (is (qcn/narrowing-of? '{[A B] #{:lt}} '{[A B] #{:lt :eq}} algebra))
    (is (qcn/narrowing-of? '{[A B] #{:lt}} '{[A B] #{:lt}} algebra))
    (is (not (qcn/narrowing-of? '{[A B] #{:lt :eq}} '{[A B] #{:lt}} algebra)))
    (testing "a pair that has gone away is the universe, so it widens unless it was one"
      (is (not (qcn/narrowing-of? '{} '{[A B] #{:lt}} algebra)))
      (is (qcn/narrowing-of? '{} {'[A B] point-universe} algebra)))
    (testing "and a new pair is a narrowing of the universe it was not recorded at"
      (is (qcn/narrowing-of? '{[A B] #{:lt} [C D] #{:gt}} '{[A B] #{:lt}} algebra)))))

(deftest the-warm-start-reaches-an-inconsistency-the-sweep-reaches
  ;; the verdict half, as for the queue: a narrowing that empties a constraint only by
  ;; composition must be found from a warm start too, where no triple sweep runs at all
  (let [algebra (:point algebras)
        ;; A < B < C, then C ≤ A — unsatisfiable, and only the composition says so
        prior-net '{[A B] #{:lt} [B A] #{:gt} [B C] #{:lt} [C B] #{:gt}}
        prior     (qcn/path-consistent prior-net (nodes-of prior-net) algebra)
        net       (assoc prior-net '[C A] #{:lt :eq} '[A C] #{:gt :eq})]
    (is (map? prior) "the starting network is satisfiable")
    (is (qcn/narrowing-of? net prior-net algebra))
    (is (= :inconsistent (qcn/path-consistent-naive net (nodes-of net) algebra)))
    (is (= :inconsistent (qcn/path-consistent-from net prior (nodes-of net) algebra)))))

(deftest an-algebra-whose-universe-does-not-compose-to-itself-is-still-tightened
  ;; the loop skips a triple whose two inputs are both unknown, and only when the algebra
  ;; makes that provably a no-op.  Here it does not — composing the universe with itself
  ;; loses a relation — so nothing may be skipped, and the unknown pair must still narrow.
  (let [universe #{:a :b}
        algebra  {:universe universe
                  :identity #{:a}
                  :compose  (fn [_ _] #{:a})        ; every composition is :a
                  :converse identity}
        net      '{[X Y] #{:a :b} [Y X] #{:a :b}
                   [Y Z] #{:a :b} [Z Y] #{:a :b}}
        ns       (nodes-of net)]
    (is (= (qcn/path-consistent-naive net ns algebra)
           (qcn/path-consistent net ns algebra)))
    (is (= #{:a} (qcn/constraint (qcn/path-consistent net ns algebra) algebra 'X 'Z))
        "X?Z was unknown and both routes to it are unknown, and it still tightens")))

;; ---- the first look need not be a sweep ---------------------------------
;; A network read out of a KB records a constraint at a handful of pairs, and under a
;; jointly-exhaustive algebra a triple reading two unknowns narrows nothing — so the
;; recorded pairs are the only ones a first pass can learn from, and a sweep of every
;; triple is n(n-1)(n-2) visits to find that out.  The queue starts from them instead,
;; under a budget, and falls back to sweeping when the network turns out to close dense.

(defn- sweeps
  "`[answer sweep-count]` for one pass — how many full sweeps of every triple it made."
  [net ns algebra]
  ;; the same primitive signature `sweep` has (`[step ^long n changed]`), because its call
  ;; site invokes it through `IFn$OLOO` — a varargs stand-in does not satisfy it and the
  ;; redef would fail on the first call rather than count it
  (let [calls (atom 0)
        real  @#'qcn/sweep]
    (with-redefs-fn {#'qcn/sweep (fn [step ^long n changed]
                                   (swap! calls inc)
                                   (real step n changed))}
      (fn [] [(qcn/path-consistent net ns algebra) @calls]))))

(defn- containment-tree
  "`(ntpp child parent)` over a branching-3 tree of `n` regions — sparse: only pairs
  sharing an ancestor line compose."
  [n]
  (let [node #(symbol (str "R" %))]
    (reduce (fn [net i]
              (assoc net [(node i) (node (quot (dec i) 3))] #{:ntpp}
                     [(node (quot (dec i) 3)) (node i)] #{:ntppi}))
            {} (range 1 n))))

(defn- total-order
  "`(before Ii Ii+1)` over `n` intervals — dense: path consistency pins every pair."
  [n]
  (let [node #(symbol (str "I" %))]
    (reduce (fn [net i]
              (assoc net [(node (dec i)) (node i)] #{:before}
                     [(node i) (node (dec i))] #{:after}))
            {} (range 1 n))))

(deftest a-sparse-network-closes-without-a-sweep
  (let [net          (containment-tree 40)
        ns           (nodes-of net)
        [answer swept] (sweeps net ns space/rcc8-algebra)]
    (is (zero? swept)
        (str "the queue seeded from the recorded pairs reached the fixpoint, got "
             swept " sweeps"))
    (is (= (qcn/path-consistent-naive net ns space/rcc8-algebra) answer)
        "and it is the answer the re-sweeping reference reaches")))

(deftest an-algebra-that-composes-the-universe-smaller-is-not-seeded-from-recorded-pairs
  ;; The seed rests entirely on `no-op?`: only where the universe composes to itself is an
  ;; unrecorded pair provably incapable of narrowing on a first look.  Where it does not,
  ;; a network recording *nothing at all* still tightens — every pair to what the universe
  ;; composes to — and a run that seeded from the recorded pairs would seed from nothing,
  ;; drain nothing, and answer that the network was already closed.
  (let [algebra {:universe #{:a :b}
                 :identity #{:a}
                 :compose  (fn [_ _] #{:a})       ; the universe composes to a proper subset
                 :converse identity}
        net     {}                                ; nothing recorded — the whole point
        ns      '#{X Y Z}
        [answer swept] (sweeps net ns algebra)]
    (is (pos? swept) "nothing is recorded, so there is nothing to seed from and it sweeps")
    (is (= #{:a} (qcn/constraint answer algebra 'X 'Z))
        "and every pair tightens, though no pair was written down")
    (is (= (qcn/path-consistent-naive net ns algebra) answer))))

(deftest a-dense-network-falls-back-to-sweeping
  ;; the estimate cannot see how much a network will narrow, so the budget is what bounds
  ;; how wrong it can be — the drain gives up, keeps what it narrowed, and the sweep route
  ;; finishes from there
  (let [net            (total-order 40)
        ns             (nodes-of net)
        [answer swept] (sweeps net ns iv/allen-algebra)]
    (is (pos? swept) "a network that pins every pair does not drain inside the budget")
    (is (= (qcn/path-consistent-naive net ns iv/allen-algebra) answer)
        "and the fallback reaches the same fixpoint, which is the whole point of a budget")))

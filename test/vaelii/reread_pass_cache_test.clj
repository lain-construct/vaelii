;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.reread-pass-cache-test
  "A reader's re-read of its definitional nogoods holds the pass caches.

  Once a reader withdraws a ground, `decide/losers` re-asks every definitional nogood of
  the round at the reader (`clashes/reread-at`), each through the membership lookup and the
  separation frame.  The nogoods of a round share their types and contexts, so the
  re-read binds `tax/*closure-pass-cache*`, `*visible-neighbours-cache*` and
  `*separation-frame-cache*` for its span, which holds a detached taxonomy and one reading
  still.  Nothing bound them after the closing settle's clash pass went, and a large KB's
  open re-walked the same `genl?` pair once per instance.  Every answer must be the one
  the uncached re-read (`clashes/reread-each`) gives."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.clashes :as clashes]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]))

(def ^:private reread-each @#'clashes/reread-each)
(def ^:private reread-at @#'clashes/reread-at)

(defn- try! [kb s cx]
  (try (v/assert kb s cx) (catch clojure.lang.ExceptionInfo _ nil)))

(defn- shuffle-with [^java.util.Random rnd coll]
  (sort-by (fn [_] (.nextInt rnd)) coll))

(defn- random-world!
  "Two hierarchies of twelve types under two disjoint roots, individuals holding a type
  of each in either of two contexts, and `except`s in the lower context hiding some
  `genl` edges and a declaration: grounds the lower reader withdraws.  Answers the two
  contexts, the blocks and the edges' handles."
  [kb ^java.util.Random rnd]
  (let [base   (tu/tmp-ctx)
        sub    (tu/tmp-ctx)
        roots  (vec (repeatedly 2 #(tu/fresh-term :type 'root_t)))
        blocks (vec (for [r roots] (into [r] (repeatedly 12 #(tu/fresh-term :type 'kind_t)))))
        pick   (fn [v] (v (.nextInt rnd (count v))))
        edges  (atom [])]
    (v/assert kb (list 'genlCx sub base) 'CxUniverse)
    (doseq [blk blocks, i (range 1 (count blk)), _ (range (inc (.nextInt rnd 2)))]
      (when-let [h (try! kb (list 'genl (blk i) (blk (.nextInt rnd i))) base)]
        (swap! edges conj h)))
    (let [decl (try! kb (list 'disjoint (roots 0) (roots 1)) base)]
      (try! kb (list 'disjoint (pick (blocks 0)) (pick (blocks 1))) base)
      (dotimes [_ 16]
        (let [x (tu/fresh-term :individual 'Ind)]
          (doseq [blk blocks]
            (try! kb (list (pick blk) x) (if (zero? (.nextInt rnd 3)) sub base)))))
      (doseq [h (cons decl (take 3 (shuffle-with rnd @edges)))
              :when (and h (zero? (.nextInt rnd 2)))]
        (try! kb (list 'except (list 'sentexHandle h)) sub)))
    {:base base :sub sub :blocks blocks :edges @edges}))

(deftest a-cached-re-read-convicts-what-the-uncached-one-does
  ;; the reader reads again after edges move under it, so a cache outliving its re-read
  ;; would answer from the taxonomy before the move
  (let [rnd   (java.util.Random. 1729)
        asked (atom 0)
        kept  (atom 0)]
    (dotimes [trial 12]
      (tu/with-neutral-kb [kb tu/isolated-fresh]
        (let [{:keys [base sub blocks edges]} (random-world! kb rnd)
              read! (fn [phase]
                      (res/clear-withdrawn! kb)
                      (binding [res/*reread*
                                (fn [kb reader provisional ngs]
                                  (let [cached (reread-at kb reader provisional ngs)]
                                    (swap! asked + (count ngs))
                                    (swap! kept + (count cached))
                                    (is (= (reread-each kb reader provisional ngs) cached)
                                        (str "trial " trial " " phase))
                                    cached))]
                        (res/withdrawal kb sub)))]
          (read! :before)
          (doseq [h (take 2 (shuffle-with rnd edges))]
            (v/retract! kb h))
          (let [blk (blocks (.nextInt rnd 2))]
            (try! kb (list 'genl (blk (inc (.nextInt rnd 12))) (blk 0)) base))
          (read! :after))))
    (is (pos? @asked) "the worlds re-read some nogoods")
    (is (pos? @kept) "and still convict some of them")))

(deftest a-re-read-walks-each-type-pair-once
  ;; `k` individuals each hold one type of either side of a separation, the same two
  ;; types, and the reader hides an edge the pairs do not rest on: every nogood is
  ;; re-asked, and each asks `genl?` of the one pair.
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [k     12
          base  (tu/tmp-ctx)
          sub   (tu/tmp-ctx)
          [ra rb a b other] (map #(tu/fresh-term :type %) '[ra_t rb_t a_t b_t other_t])]
      (v/assert kb (list 'genlCx sub base) 'CxUniverse)
      (v/assert kb (list 'genl a ra) base)
      (v/assert kb (list 'genl b rb) base)
      (v/assert kb (list 'disjoint ra rb) base)
      (let [edge (v/assert kb (list 'genl other ra) base)]
        (dotimes [_ k]
          (let [x (tu/fresh-term :individual 'Ind)]
            (v/assert kb (list a x) base)
            (v/assert kb (list b x) base)))
        (v/assert kb (list 'except (list 'sentexHandle edge)) sub))
      (res/clear-withdrawn! kb)
      (let [walks (atom 0)
            ngs   (atom 0)
            real  tax/genl?
            rr    res/*reread*]
        (with-redefs [tax/genl? (fn [& args] (swap! walks inc) (apply real args))]
          (binding [res/*reread* (fn [kb reader provisional nogoods]
                                   (swap! ngs + (count nogoods))
                                   (rr kb reader provisional nogoods))]
            (res/withdrawal kb sub)))
        (is (<= k @ngs) "every pair is re-asked")
        (is (<= @walks 4) (str @walks " genl? walks for " k " nogoods over one type pair"))))))

(defn- hidden-edge-world!
  "A reader `sub` below `base` that hides, by an `except`, a `genl` edge no clash rests on,
  so its first round withdraws a ground and re-reads every definitional nogood.  Answers
  the two contexts."
  [kb]
  (let [base  (tu/tmp-ctx)
        sub   (tu/tmp-ctx)
        [other root] (map #(tu/fresh-term :type %) '[other_t root_t])]
    (v/assert kb (list 'genlCx sub base) 'CxUniverse)
    (let [edge (v/assert kb (list 'genl other root) base)]
      (v/assert kb (list 'except (list 'sentexHandle edge)) sub))
    {:base base :sub sub}))

(defn- violation-asks
  "`checks/arbitrable-violations` calls and nogoods re-asked while `sub`'s withdrawal is
  computed, as `[calls nogoods]`."
  [kb sub]
  (res/clear-withdrawn! kb)
  (let [calls (atom 0)
        ngs   (atom 0)
        real  checks/arbitrable-violations
        rr    res/*reread*]
    (with-redefs [checks/arbitrable-violations (fn [& args] (swap! calls inc) (apply real args))]
      (binding [res/*reread* (fn [kb reader provisional nogoods]
                               (swap! ngs + (count nogoods))
                               (rr kb reader provisional nogoods))]
        (res/withdrawal kb sub)))
    [@calls @ngs]))

(deftest a-re-read-asks-each-member-s-violations-once
  ;; one individual holds `p` types pairwise disjoint: p(p-1)/2 hard nogoods over p
  ;; members, each member a member of p-1 of them
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [p     6
          {:keys [base sub]} (hidden-edge-world! kb)
          types (vec (repeatedly p #(tu/fresh-term :type 'sep_t)))
          x     (tu/fresh-term :individual 'Ind)]
      (doseq [i (range p) j (range (inc i) p)]
        (v/assert kb (list 'disjoint (types i) (types j)) base {:strength :monotonic}))
      (doseq [t types] (v/assert kb (list t x) base {:strength :monotonic}))
      (let [[calls ngs] (violation-asks kb sub)]
        (is (= (quot (* p (dec p)) 2) ngs) "every nogood is re-asked")
        (is (<= calls p) (str calls " violation reads for " p " members"))))))

(deftest a-round-that-withdraws-no-new-ground-re-asks-no-nogood
  ;; `k` hard nogoods and one whose `:default` member loses: the round that adds the loser
  ;; withdraws the hidden edge alone, and the next round withdraws no other ground
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [k 5
          {:keys [base sub]} (hidden-edge-world! kb)
          [a b] (map #(tu/fresh-term :type %) '[a_t b_t])
          mono  {:strength :monotonic}]
      (v/assert kb (list 'disjoint a b) base mono)
      (dotimes [_ k]
        (let [x (tu/fresh-term :individual 'Ind)]
          (v/assert kb (list a x) base mono)
          (v/assert kb (list b x) base mono)))
      (let [y     (tu/fresh-term :individual 'Ind)
            loser (v/assert kb (list a y) base)]
        (v/assert kb (list b y) base mono)
        (let [[_ ngs] (violation-asks kb sub)]
          (is (false? (v/believed? kb loser sub)) "the premise: the reader defeats a member")
          (is (= (inc k) ngs) (str ngs " nogoods re-asked for " (inc k) " nogoods")))))))

(deftest a-guard-round-reads-no-enclosing-pass-cache
  ;; a round binds its reading for the reader, and a cache an enclosing pass filled read
  ;; the edges under the reading before it
  (tu/with-neutral-kb [kb tu/isolated-fresh]
    (let [seen (atom nil)]
      (binding [tax/*closure-pass-cache*       (atom {})
                tax/*visible-neighbours-cache* (atom {})
                tax/*separation-frame-cache*   (atom {})
                res/*guard-withdrawals*        (fn [_ _ _]
                                                 (reset! seen [tax/*closure-pass-cache*
                                                               tax/*visible-neighbours-cache*
                                                               tax/*separation-frame-cache*])
                                                 {:justs [] :rules #{}})]
        (@#'res/guard-reading* kb 'CxUniverse #{'CxUniverse} #{}))
      (is (= [nil nil nil] @seen)))))

(defn- head-move-verdicts
  "A KB where `(sameAs Pa Qb)` and `(rewriteOf Qb Pa)` make `Qb` the head, and `Qb` holds
  two disjoint types `:monotonic`: a hard clash.  `CxSub` holds an `except` of the
  `rewriteOf`, so its first round takes the `rewriteOf` OUT and elects `Pa`, retiring both
  members' spelling.  With `hide-edge?`, `CxSub` also hides a `genl` edge, a ground its
  first round withdraws and re-reads under.  Answers the verdicts each reader reads, the
  hard clash's members, and the reader's election."
  [kb hide-edge?]
  (tu/with-terms [dog_ cat_ other_ root_ Pa Qb CxBase CxSub]
    (let [mono {:strength :monotonic}]
      (v/assert kb (list 'genlCx CxSub CxBase) 'CxUniverse)
      (when hide-edge?
        (let [edge (v/assert kb (list 'genl other_ root_) CxBase)]
          (v/assert kb (list 'except (list 'sentexHandle edge)) CxSub)))
      (v/assert kb (list 'disjoint dog_ cat_) CxBase mono)
      (v/assert kb (list 'sameAs Pa Qb) CxBase mono)
      (let [rw (v/assert kb (list 'rewriteOf Qb Pa) CxBase)]
        (v/assert kb (list 'except (list 'sentexHandle rw)) CxSub))
      (let [clash #{(v/assert kb (list dog_ Qb) CxBase mono)
                    (v/assert kb (list cat_ Qb) CxBase mono)}]
        (res/clear-withdrawn! kb)
        {:base     (:verdicts (res/withdrawal kb CxBase))
         :sub      (:verdicts (res/withdrawal kb CxSub))
         :clash    clash
         :heads    [(v/representative kb Pa CxBase) (v/representative kb Pa CxSub)]
         :expected [Qb Pa]}))))

(deftest a-round-that-withdraws-an-equality-supporter-re-reads
  ;; the re-read reads which spellings the reader retires through the scoped equality
  ;; partition, so a round withdrawing only an equality supporter re-asks the
  ;; definitional nogoods: with no ground withdrawn, and after a ground's re-read
  (doseq [hide-edge? [false true]]
    (tu/with-neutral-kb [kb tu/isolated-fresh]
      (let [{:keys [base sub clash heads expected]} (head-move-verdicts kb hide-edge?)]
        (is (= expected heads) "the premise: the reader's round moves the head")
        (is (= :hard (get base clash)) "the reader above the except reads the clash")
        (is (not (contains? sub clash))
            (str "the reader retires both members' spelling, hide-edge? " hide-edge?))))))

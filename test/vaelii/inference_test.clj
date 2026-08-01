(ns vaelii.inference-test
  "The node engine's own contract (`vaelii.impl.inference`): the residual transformation,
  per-literal depth, binding flow, guards, the claimed-key set, the frontier's order,
  and the shape of the tree it leaves behind.

  Answer-set agreement with the DFS is the criterion that actually decides whether this
  engine is right, and it lives next door in `inference_parity_test`.  What is here is the
  diagnosis when that one goes red."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.inference :as inf]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- answers
  "Every solution the node engine finds for `goals` in `context`, as a set."
  ([kb goals context] (answers kb goals context 8))
  ([kb goals context depth]
   (set (inf/solutions kb goals context {:max-depth depth}))))

(defn- values [sols var] (set (map #(get % var) sols)))

;; ---- shape ---------------------------------------------------------------

(tu/deftest-kb a-node-that-solves-against-facts-alone-is-a-completed-proof
  (tu/with-terms [parentOf ShapeContext]
    (tu/with-terms [ShapeA ShapeB]
      (v/assert kb (list parentOf ShapeA ShapeB) ShapeContext)
      (testing "depth 0 — no rewrite is possible, and the root still answers"
        (is (= #{{'?y ShapeB}} (answers kb [(list parentOf ShapeA '?y)] ShapeContext 0))))
      (testing "a ground goal that holds proves once, with an empty binding"
        (is (= #{{}} (answers kb [(list parentOf ShapeA ShapeB)] ShapeContext))))
      (testing "a goal nothing answers drains the frontier and returns nothing"
        (let [sess (inf/session kb [(list parentOf ShapeB '?y)] ShapeContext {:max-depth 2})]
          (is (empty? (doall (inf/search-seq sess))))
          (is (zero? (:frontier (inf/tree-stats sess))) "the queue was not drained")
          (is (zero? (:solutions (inf/tree-stats sess)))))))))

(tu/deftest-kb a-rule-is-rewritten-into-its-antecedents
  (tu/with-terms [parentOf anc ShapeContext]
    (tu/with-terms [RwA RwB]
      (v/assert kb (list parentOf RwA RwB) ShapeContext)
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) ShapeContext
                     {:direction :backward})
      (testing "one rewrite reaches it, none does not"
        (is (= #{RwB} (values (answers kb [(list anc RwA '?z)] ShapeContext 1) '?z)))
        (is (empty? (answers kb [(list anc RwA '?z)] ShapeContext 0)))))))

;; ---- residuals and per-literal depth -------------------------------------

(defn- chain-of-rules!
  "`(p0 ?x)` concluded from `(p1 ?x)` concluded from … from a stored `(base Ind)`, so
  proving `(p0 Ind)` takes exactly `n` rewrites."
  [kb base ind pred n context]
  (v/assert kb (list base ind) context)
  (doseq [i (range n)]
    (v/assert-rule kb [(list (symbol (str pred (inc i))) '?x)]
                   (list (symbol (str pred i)) '?x) context {:direction :backward}))
  (v/assert-rule kb [(list base '?x)] (list (symbol (str pred n)) '?x) context
                 {:direction :backward}))

(tu/deftest-kb depth-bounds-the-rewrites-a-literal-may-take
  (tu/with-terms [base DepthContext]
    (tu/with-terms [DepthInd]
      (chain-of-rules! kb base DepthInd "tmpDepthP" 2 DepthContext)
      (let [goal (list 'tmpDepthP0 DepthInd)]
        (is (empty? (answers kb [goal] DepthContext 2)) "3 rewrites are needed")
        (is (= #{{}} (answers kb [goal] DepthContext 3)))
        (is (= #{{}} (answers kb [goal] DepthContext 5)) "a larger bound finds the same")))))

(tu/deftest-kb each-conjunct-carries-its-own-depth
  ;; The DFS gives a conjunction one budget for all of it, so whichever literal is
  ;; expanded first can spend the lot.  A node gives each conjunct its own, decremented
  ;; only for the one actually rewritten — so a cheap conjunct beside an expensive one
  ;; does not have to pay for it.
  (tu/with-terms [base PerLitContext]
    (tu/with-terms [PerLitInd]
      (chain-of-rules! kb base PerLitInd "tmpShallow" 0 PerLitContext)   ; 1 rewrite
      (chain-of-rules! kb base PerLitInd "tmpDeeper" 2 PerLitContext)    ; 3 rewrites
      (let [conj-goal [(list 'tmpShallow0 PerLitInd) (list 'tmpDeeper0 PerLitInd)]]
        (is (empty? (answers kb conj-goal PerLitContext 2)))
        (is (= #{{}} (answers kb conj-goal PerLitContext 3))
            "3 is what the deeper conjunct needs; the shallow one must not have spent it")))))

(tu/deftest-kb two-copies-of-one-sentence-keep-independent-counters
  (tu/with-terms [base DupContext]
    (tu/with-terms [DupInd]
      (chain-of-rules! kb base DupInd "tmpDup" 1 DupContext)       ; 2 rewrites each
      (let [g (list 'tmpDup0 DupInd)]
        (is (empty? (answers kb [g g] DupContext 1)))
        (is (= #{{}} (answers kb [g g] DupContext 2))
            "the first copy's rewrites must not be charged to the second")))))

(tu/deftest-kb a-multi-antecedent-rule-gives-every-conjunct-the-same-remaining-depth
  (tu/with-terms [leftOf rightOf between BetweenContext]
    (tu/with-terms [BwA BwB BwC]
      (v/assert kb (list leftOf BwA BwB) BetweenContext)
      (v/assert kb (list rightOf BwC BwB) BetweenContext)
      (v/assert-rule kb [(list leftOf '?a '?b) (list rightOf '?c '?b)]
                     (list between '?a '?b '?c) BetweenContext {:direction :backward})
      (is (= #{{'?a BwA '?b BwB '?c BwC}}
             (answers kb [(list between '?a '?b '?c)] BetweenContext 1))))))

;; ---- binding flow --------------------------------------------------------

(tu/deftest-kb a-rewrite-carries-bindings-into-and-out-of-the-query-variables
  (tu/with-terms [edgeOf hop BindContext]
    (tu/with-terms [BnP BnQ BnR]
      (v/assert kb (list edgeOf BnP BnQ) BindContext)
      (v/assert kb (list edgeOf BnQ BnR) BindContext)
      (v/assert-rule kb [(list edgeOf '?x '?y)] (list hop '?x '?y) BindContext
                     {:direction :backward})
      (testing "the first argument bound, the second open"
        (is (= #{BnQ} (values (answers kb [(list hop BnP '?y)] BindContext) '?y))))
      (testing "the second bound, the first open"
        (is (= #{BnP} (values (answers kb [(list hop '?x BnQ)] BindContext) '?x))))
      (testing "both open"
        (is (= #{{'?x BnP '?y BnQ} {'?x BnQ '?y BnR}}
               (answers kb [(list hop '?x '?y)] BindContext))))
      (testing "both ground and disagreeing"
        (is (empty? (answers kb [(list hop BnP BnR)] BindContext))))
      (testing "a conjunctive query joins on the shared variable"
        (is (= #{{'?x BnP '?y BnQ '?z BnR}}
               (answers kb [(list hop '?x '?y) (list hop '?y '?z)] BindContext)))))))

(tu/deftest-kb two-rules-concluding-one-goal-both-answer-it
  (tu/with-terms [byLand bySea reachable MultiContext]
    (tu/with-terms [MtA MtB]
      (v/assert kb (list byLand MtA) MultiContext)
      (v/assert kb (list bySea MtB) MultiContext)
      (v/assert-rule kb [(list byLand '?x)] (list reachable '?x) MultiContext
                     {:direction :backward})
      (v/assert-rule kb [(list bySea '?x)] (list reachable '?x) MultiContext
                     {:direction :backward})
      (is (= #{MtA MtB} (values (answers kb [(list reachable '?x)] MultiContext) '?x))))))

;; ---- joins and the diamond -----------------------------------------------

(tu/deftest-kb a-diamond-answers-once-and-claims-the-shared-node-once
  ;; Two rules concluding `top` whose antecedents converge on one `base` literal.  The
  ;; two routes reach the same residual, and the second arrival is dropped before it is
  ;; enqueued rather than expanded again.
  (tu/with-terms [base mid1 mid2 top DiaContext]
    (tu/with-terms [DiaX]
      (v/assert kb (list base DiaX) DiaContext)
      (v/assert-rule kb [(list base '?x)] (list mid1 '?x) DiaContext {:direction :backward})
      (v/assert-rule kb [(list base '?x)] (list mid2 '?x) DiaContext {:direction :backward})
      (v/assert-rule kb [(list mid1 '?x)] (list top '?x) DiaContext {:direction :backward})
      (v/assert-rule kb [(list mid2 '?x)] (list top '?x) DiaContext {:direction :backward})
      (let [sess (inf/session kb [(list top '?x)] DiaContext {:max-depth 3})
            sols (set (doall (inf/search-seq sess)))
            st   (inf/tree-stats sess)]
        (is (= #{{'?x DiaX}} sols) "one answer, not two")
        (is (pos? (:dropped st)) "the converging arrival was never dropped")
        (is (= (:nodes st) (:expanded st)) "a claimed node must be expanded exactly once")))))

(tu/deftest-kb a-four-literal-conjunction-joins-across-all-of-them
  (tu/with-terms [pA pB pC pD JoinContext]
    (tu/with-terms [JnOne JnTwo]
      (doseq [[p i] [[pA JnOne] [pB JnOne] [pC JnOne] [pD JnOne]
                     [pA JnTwo] [pB JnTwo] [pC JnTwo]]]
        (v/assert kb (list p i) JoinContext))
      (is (= #{JnOne}
             (values (answers kb [(list pA '?x) (list pB '?x) (list pC '?x) (list pD '?x)]
                              JoinContext)
                     '?x))))))

;; ---- guards --------------------------------------------------------------

(tu/deftest-kb an-exception-is-asked-at-the-nodes-own-solve
  ;; A node has no rule frame to check a guard in, and needs none: its inline solve is
  ;; the moment the argument is complete.
  (tu/with-terms [wings flies odd GuardContext]
    (tu/with-terms [GdBird GdPenguin]
      (v/assert kb (list wings GdBird) GuardContext)
      (v/assert kb (list wings GdPenguin) GuardContext)
      (v/assert kb (list odd GdPenguin) GuardContext)
      (v/assert kb (list 'exceptWhen (list odd '?x)
                         (list 'set/defaultRule
                               (list 'implies (list wings '?x) (list flies '?x))))
                GuardContext)
      (testing "a variable exception blocks exactly the bindings it holds of"
        (is (= #{GdBird} (values (answers kb [(list flies '?x)] GuardContext) '?x))))
      (testing "and the same asked of the excepted individual directly"
        (is (empty? (answers kb [(list flies GdPenguin)] GuardContext)))
        (is (= #{{}} (answers kb [(list flies GdBird)] GuardContext)))))))

;; ---- termination ---------------------------------------------------------

(tu/deftest-kb a-cyclic-rule-set-drains-the-frontier
  (tu/with-terms [pingOf pongOf CycleContext]
    (tu/with-terms [CycInd]
      (v/assert-rule kb [(list pongOf '?x)] (list pingOf '?x) CycleContext
                     {:direction :backward})
      (v/assert-rule kb [(list pingOf '?x)] (list pongOf '?x) CycleContext
                     {:direction :backward})
      (let [sess (inf/session kb [(list pingOf CycInd)] CycleContext {:max-depth 6})]
        (is (empty? (doall (inf/search-seq sess))) "nothing supports either predicate")
        (is (zero? (:frontier (inf/tree-stats sess))) "the search did not terminate")))))

;; ---- deferred literals ---------------------------------------------------

(tu/deftest-kb a-deferred-literal-is-computed-and-never-rewritten
  ;; `different` / `evaluate` / `unknown` are not stored facts and not rule heads.  A
  ;; node must route them through the registry and must not build residual children for
  ;; them, or a rule with such an antecedent silently proves nothing.
  (tu/with-terms [pairOf distinctPair DeferContext]
    (tu/with-terms [DfA DfB]
      (v/assert kb (list pairOf DfA DfB) DeferContext)
      (v/assert kb (list pairOf DfA DfA) DeferContext)
      (v/assert-rule kb [(list pairOf '?x '?y) (list 'different '?x '?y)]
                     (list distinctPair '?x '?y) DeferContext {:direction :backward})
      (is (= #{{'?x DfA '?y DfB}}
             (answers kb [(list distinctPair '?x '?y)] DeferContext))
          "the reflexive pair must be computed away, not matched"))))

;; ---- structure: the queue, the claim, the tree ---------------------------

(tu/deftest-kb the-frontier-pops-the-lowest-estimate-first
  (let [q (-> (inf/empty-queue) (inf/queue-push 90 1) (inf/queue-push 10 2)
              (inf/queue-push 50 3))]
    (is (nil? (inf/queue-pop (inf/empty-queue))) "an empty queue must pop nil")
    (let [[e1 q1] (inf/queue-pop q)
          [e2 q2] (inf/queue-pop q1)
          [e3 q3] (inf/queue-pop q2)]
      (is (= [[10 2] [50 3] [90 1]] [e1 e2 e3]))
      (is (nil? (inf/queue-pop q3))))))

(tu/deftest-kb a-key-is-claimed-once-and-the-claim-is-what-stops-a-re-arrival
  (tu/with-terms [parentOf anc KeyContext]
    (tu/with-terms [KyA KyB]
      (v/assert kb (list parentOf KyA KyB) KeyContext)
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) KeyContext
                     {:direction :backward})
      (let [sess (inf/session kb [(list anc '?x '?z)] KeyContext {:max-depth 2})
            root (get @(:nodes sess) 0)]
        (is (= 1 (count @(:claimed sess))) "the root claims its key when it is enqueued")
        (is (contains? @(:claimed sess) (inf/node-key root)))
        (testing "the root is the asker's question canonicalized, and keeps their names"
          (is (= [(list anc '?var0 '?var1)] (mapv :sentence (:literals root))))
          (is (= '{?x ?var0, ?z ?var1} (:answer-terms root))))
        (testing "two alpha-variant questions are one conjunction — that is what canonical buys"
          (let [other (inf/session kb [(list anc '?who '?whom)] KeyContext {:max-depth 2})]
            (is (= (mapv :sentence (:literals root))
                   (mapv :sentence (:literals (get @(:nodes other) 0)))))))
        (testing "a constant reaching a literal changes the key, because it changes the question"
          (is (not= (inf/node-key root)
                    (inf/node-key (assoc root :literals [{:sentence (list anc KyA '?var1)
                                                          :depth 2}])))))
        (testing "and one conjunction asked on behalf of a different answer is a different node"
          ;; same literals, opposite projection: collapsing these loses an answer set
          (is (not= (inf/node-key root)
                    (inf/node-key (assoc root :answer-terms '{?x ?var1, ?z ?var0})))))))))

(tu/deftest-kb the-search-tree-outlives-the-search
  (tu/with-terms [parentOf anc TreeContext]
    (tu/with-terms [TrA TrB]
      (v/assert kb (list parentOf TrA TrB) TreeContext)
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) TreeContext
                     {:direction :backward})
      (let [sess (inf/session kb [(list anc '?x '?z)] TreeContext {:max-depth 2})
            sols (doall (inf/search-seq sess))
            st   (inf/tree-stats sess)]
        (is (seq sols))
        (is (>= (:nodes st) 2) "root plus at least one child")
        (is (= (:nodes st) (:expanded st)))
        (is (pos? (:max-depth st)) "no rewrite was recorded")
        (testing "every node still names the one it came from"
          (let [ns (vals @(:nodes sess))]
            (is (= 1 (count (filter #(nil? (:parent-id %)) ns))) "exactly one root")
            (is (every? #(contains? @(:nodes sess) (:parent-id %))
                        (remove #(nil? (:parent-id %)) ns)))))
        (testing "and carries the rules that licensed it"
          (is (some #(seq (:supports %)) (vals @(:nodes sess)))))))))

;; ---- purity --------------------------------------------------------------

(tu/deftest-kb a-query-leaves-the-kb-exactly-as-it-found-it
  ;; An engine that materializes its conclusions is a forward chainer in disguise.
  (tu/with-terms [parentOf anc PureContext]
    (tu/with-terms [PrA PrB PrC]
      (v/assert kb (list parentOf PrA PrB) PureContext)
      (v/assert kb (list parentOf PrB PrC) PureContext)
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) PureContext
                     {:direction :backward})
      (v/assert-rule kb [(list parentOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z)
                     PureContext {:direction :backward})
      (let [before (tu/content-count kb)]
        (is (seq (answers kb [(list anc '?x '?z)] PureContext)))
        (is (= before (tu/content-count kb))
            "the search created sentexes or justifications")))))

;; ---- laziness ------------------------------------------------------------

(tu/deftest-kb the-result-stream-expands-a-node-per-pull
  (tu/with-terms [wideOf WideContext]
    (let [inds (mapv #(symbol (str "TmpWide" % "Node")) (range 6))]
      (doseq [i inds] (v/assert kb (list wideOf i) WideContext))
      (let [sess (inf/session kb [(list wideOf '?x)] WideContext {:max-depth 2})
            two  (doall (take 2 (inf/search-seq sess)))]
        (is (= 2 (count two)))
        (is (<= (:expanded (inf/tree-stats sess)) 2)
            "a bounded consumer must not have driven the whole search"))
      (testing "and reading it dry returns everything"
        (is (= (set inds)
               (values (answers kb [(list wideOf '?x)] WideContext) '?x)))))))

;; ---- the selector --------------------------------------------------------

(tu/deftest-kb the-selector-routes-and-defaults-to-the-dfs
  (tu/with-terms [parentOf anc SelContext]
    (tu/with-terms [SlA SlB]
      (v/assert kb (list parentOf SlA SlB) SelContext)
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) SelContext
                     {:direction :backward})
      (when-not (tu/query-engine-override)
        (is (= :dfs v/*query-engine*) "the default must stay :dfs"))
      (let [goal (list anc SlA '?z)]
        (testing ":inference answers what :dfs answers"
          (is (= #{SlB} (values (set (v/prove kb goal SelContext)) '?z)))
          (is (= #{SlB} (values (binding [v/*query-engine* :inference, inf/*max-depth* 8]
                                  (set (v/prove kb goal SelContext)))
                                '?z))))
        (testing ":hybrid sends a depth-0 budget to the DFS and anything deeper to the node engine"
          (binding [v/*query-engine* :hybrid]
            (is (= :complete (:status (v/prove-within kb goal SelContext {:max-depth 0}))))
            (let [r (v/prove-within kb goal SelContext {:max-depth 3})]
              (is (= :complete (:status r)))
              (is (= #{SlB} (values (set (:results r)) '?z))))))
        (testing "a bounded run is a prefix, and resume continues it"
          (binding [v/*query-engine* :inference, inf/*max-depth* 8]
            (let [r (v/prove-within kb goal SelContext {:max-results 0})]
              (is (= :capped (:status r)))
              (is (= #{SlB} (values (set (:results (v/resume r {}))) '?z))))))))))

;; ---- the proof tree ------------------------------------------------------
;; `query` with `{:proof? true}` returns the derivation the search took, replayed out of
;; the node registry.  What is checked here is that it is a *faithful* replay: the rules
;; it names are the rules that fired, its leaves are literals the search really did hand
;; to the leaf solver, and one variable name means one thing across the whole tree —
;; which is the property a per-node namespace makes non-obvious.

(defn- rules-in
  "Every rule handle a proof tree names, depth-first.  A leaf names none."
  [tree]
  (mapcat (fn [n] (when (= :rule (:via n)) (cons (:rule n) (rules-in (:because n)))))
          tree))

(defn- leaves-in [tree]
  (mapcat (fn [n] (if (= :leaf (:via n)) [(:goal n)] (leaves-in (:because n)))) tree))

(tu/deftest-kb a-proof-names-the-rule-that-fired-and-the-literals-under-it
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann PfContext]
    (v/assert kb (list parentOf Tom Bob) PfContext)
    (v/assert kb (list parentOf Bob Ann) PfContext)
    (let [rh (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                            (list grandparentOf '?x '?z) PfContext
                            {:direction :backward})
          [r & more] (v/query kb (list grandparentOf Tom '?w) PfContext
                              {:max-depth 2 :proof? true})]
      (testing "one answer, and it comes back with its bindings beside its proof"
        (is (empty? more))
        (is (= {'?w Ann} (:bindings r)))
        (is (vector? (:proof r)) "one tree per conjunct of the query"))
      (let [[top] (:proof r)]
        (testing "the root of the tree is the query's own conjunct, derived by the rule"
          (is (= :rule (:via top)))
          (is (= rh (:rule top)) "the handle of the rule that actually fired")
          (is (= grandparentOf (first (:goal top)))))
        (testing "and the rule reads as its author wrote it, not in canonical variables"
          (is (= (list 'implies
                       (list 'and (list parentOf '?x '?y) (list parentOf '?y '?z))
                       (list grandparentOf '?x '?z))
                 (:sentence top))))
        (testing "its children are the antecedents, and nothing below them was rewritten"
          (is (= 2 (count (:because top))))
          (is (every? #(= :leaf (:via %)) (:because top)))
          (is (every? #(= parentOf (first (:goal %))) (:because top))))))))

(tu/deftest-kb one-variable-name-means-one-thing-across-a-nested-proof
  ;; Each node canonicalizes to `?var0 ?var1 …` in a namespace of its own, so a tree
  ;; assembled straight from the nodes would use `?var0` for a different variable at
  ;; every level.  The replay pushes each level forward into the next node's numbering,
  ;; which is what makes the finished tree readable as one derivation.
  (tu/with-terms [parentOf anc Tom Bob Ann Zed PfContext]
    (doseq [[a b] [[Tom Bob] [Bob Ann] [Ann Zed]]]
      (v/assert kb (list parentOf a b) PfContext))
    (let [base (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) PfContext
                              {:direction :backward})
          step (v/assert-rule kb [(list parentOf '?x '?y) (list anc '?y '?z)]
                              (list anc '?x '?z) PfContext {:direction :backward})
          by-answer (into {} (map (juxt (comp '?w :bindings) :proof))
                          (v/query kb (list anc Tom '?w) PfContext
                                   {:max-depth 4 :proof? true}))]
      (testing "every reachable ancestor is answered, each with a proof"
        (is (= #{Bob Ann Zed} (set (keys by-answer)))))
      (testing "the one-hop answer uses the base rule alone"
        (is (= [base] (rules-in (by-answer Bob)))))
      (testing "the three-hop answer stacks the recursive rule twice over the base"
        (is (= [step step base] (rules-in (by-answer Zed)))))
      (testing "and its leaves chain end to end — the join variables line up"
        ;; (parentOf Tom ?a) (parentOf ?a ?b) (parentOf ?b ?c), one namespace throughout
        (let [ls (vec (leaves-in (by-answer Zed)))]
          (is (= 3 (count ls)))
          (is (= Tom (second (first ls))))
          (is (= (nth (nth ls 0) 2) (second (nth ls 1))) "first hop feeds the second")
          (is (= (nth (nth ls 1) 2) (second (nth ls 2))) "second feeds the third"))))))

(tu/deftest-kb without-the-option-nothing-changes-shape
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann PfContext]
    (v/assert kb (list parentOf Tom Bob) PfContext)
    (v/assert kb (list parentOf Bob Ann) PfContext)
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                   (list grandparentOf '?x '?z) PfContext {:direction :backward})
    (let [goal (list grandparentOf Tom '?w)]
      (testing "the default result is binding maps, with no proof key anywhere"
        (is (= [{'?w Ann}] (vec (v/query kb goal PfContext {:max-depth 2})))))
      (testing "and asking for proofs does not change which answers come back"
        (is (= (set (v/query kb goal PfContext {:max-depth 2}))
               (set (map :bindings (v/query kb goal PfContext
                                            {:max-depth 2 :proof? true}))))))
      (testing "`query?` ignores it rather than testing a map for emptiness"
        (is (v/query? kb goal PfContext {:max-depth 2 :proof? true}))))))

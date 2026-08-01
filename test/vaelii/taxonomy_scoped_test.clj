(ns vaelii.taxonomy-scoped-test
  "The scoped read arities: a closure read asked from context K uses exactly the
  edges K can see — some believed supporter asserts them from K's genlContext
  up-cone, or from no recorded context at all (nil, which constrains everywhere).

  Pure unit tests over a raw taxonomy, like taxonomy_test: handles are bare
  integers, belief is whatever set `refresh-beliefs` is handed.  The oracle at the
  end is the reference: filter the active edge set by visibility *first*, hand it
  to the materialized `closures` build, and every scoped read must agree — after
  every edit of a random sequence, from every reader, so a stale memo or vis-index
  entry has nowhere to hide.

  The context lattice used throughout ((genlContext Sub Super) = Sub sees Super):

      UContext            EContext
      /      \\               |
  AContext  BContext      OContext
      \\      /
      WContext
         |
      DContext"
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.taxonomy :as tax]))

(def ^:private lattice-handles
  "The handles of the context lattice's own supporters — `refresh-beliefs`
  reconciles every relation at once, so a believed set that omits these would
  deactivate the lattice out from under the reader's cone."
  #{901 902 903 904 905 906})

(defn- lattice
  "A fresh taxonomy holding the context lattice above (handles 901-906)."
  []
  (let [t (tax/create-taxonomy)]
    (tax/add-genlContext t 'AContext 'UContext 901)
    (tax/add-genlContext t 'BContext 'UContext 902)
    (tax/add-genlContext t 'WContext 'AContext 903)
    (tax/add-genlContext t 'WContext 'BContext 904)
    (tax/add-genlContext t 'DContext 'WContext 905)
    (tax/add-genlContext t 'OContext 'EContext 906)
    t))

;; ---- the visibility sets --------------------------------------------------

(deftest visible-ctxs-is-a-function-of-the-cone-and-the-census
  (let [t (lattice)]
    (tax/add-genl t 'dog 'animal 1 'AContext)
    (tax/add-genl t 'cat 'animal 2 'BContext)
    (testing "a reader seeing every asserting context gets nil — the global path"
      (is (nil? (tax/visible-ctxs t :genl 'WContext)))
      (is (nil? (tax/visible-ctxs t :genl 'DContext))))
    (testing "a reader seeing some of them gets exactly those"
      (is (= '#{AContext} (tax/visible-ctxs t :genl 'AContext)))
      (is (= '#{BContext} (tax/visible-ctxs t :genl 'BContext))))
    (testing "a reader seeing none gets the empty set, not nil"
      (is (= #{} (tax/visible-ctxs t :genl 'OContext)))
      (is (= #{} (tax/visible-ctxs t :genl 'ZContext))))
    (testing "no context, or a variable, is unscoped"
      (is (nil? (tax/visible-ctxs t :genl nil)))
      (is (nil? (tax/visible-ctxs t :genl '?ctx))))
    (testing "an empty census is unscoped: nothing to filter by"
      (is (nil? (tax/visible-ctxs (tax/create-taxonomy) :genl 'AContext))))))

(deftest visible-ctxs-is-interned-per-epoch
  (let [t (lattice)]
    (tax/add-genl t 'dog 'animal 1 'AContext)
    (testing "two reads from one context share one set object"
      (is (identical? (tax/visible-ctxs t :genl 'AContext)
                      (tax/visible-ctxs t :genl 'AContext))))
    (testing "a new asserting context re-stamps and recomputes"
      (let [before (tax/visible-ctxs t :genl 'WContext)]
        (is (nil? before) "W saw every asserting context")
        (tax/add-genl t 'fish 'animal 2 'EContext)
        (is (= '#{AContext} (tax/visible-ctxs t :genl 'WContext))
            "E asserts now, W does not see it, so W is scoped")))
    (testing "a genlContext edge re-stamps too — the cone itself moved"
      (tax/add-genlContext t 'WContext 'EContext 907)
      (is (nil? (tax/visible-ctxs t :genl 'WContext))
          "W sees EContext now, so it sees every asserting context again"))))

;; ---- the scoped closures --------------------------------------------------

(deftest a-scoped-closure-walks-only-visible-edges
  (let [t (lattice)]
    (tax/add-genl t 'dog 'animal 1 'AContext)
    (tax/add-genl t 'animal 'thing 2 'BContext)
    (testing "a reader seeing both contexts composes the chain"
      (is (= '#{dog animal thing} (tax/genls t 'dog 'WContext))))
    (testing "a reader seeing only the first link stops there"
      (is (= '#{dog animal} (tax/genls t 'dog 'AContext)))
      (is (= '#{animal dog} (tax/specs t 'animal 'AContext))))
    (testing "a reader seeing only the second link never leaves the node"
      (is (= '#{dog} (tax/genls t 'dog 'BContext))))
    (testing "a reader seeing neither sees a bare node"
      (is (= '#{dog} (tax/genls t 'dog 'OContext)))
      (is (= '#{animal} (tax/specs t 'animal 'OContext))))
    (testing "the unscoped read is unchanged"
      (is (= '#{dog animal thing} (tax/genls t 'dog))))))

(deftest a-nil-context-supporter-constrains-everywhere
  (let [t (lattice)]
    (tax/add-genl t 'dog 'animal 1)                     ; no context recorded
    (tax/add-genl t 'animal 'thing 2 'AContext)
    (testing "the contextless edge is visible even where nothing else is"
      (is (= '#{dog animal} (tax/genls t 'dog 'OContext)))
      (is (= '#{dog animal} (tax/genls t 'dog 'ZContext))))
    (testing "and composes with visible edges where they are visible"
      (is (= '#{dog animal thing} (tax/genls t 'dog 'AContext))))))

(deftest scoped-genl?-agrees-and-rejects-a-direct-invisible-edge
  (let [t (lattice)]
    (tax/add-genl t 'dog 'animal 1 'AContext)
    (testing "the direct-edge shortcut carries the visibility test"
      ;; the one-step case: dog→animal exists and is invisible from O.  A walk
      ;; that filtered only transitive steps but tested the raw neighbour set
      ;; directly would answer true here.
      (is (tax/genl? t 'dog 'animal 'AContext))
      (is (not (tax/genl? t 'dog 'animal 'OContext)))
      (is (not (tax/genl? t 'dog 'animal 'BContext))))
    (testing "reflexive from anywhere"
      (is (tax/genl? t 'dog 'dog 'OContext)))))

(deftest a-scoped-read-answers-a-cycle-the-way-the-closure-it-walks-does
  ;; `wff` refuses a cyclic `genl` edge, and belief assembles one anyway: defeat an edge,
  ;; assert its reverse — the check reads the *active* adjacency, which no longer holds
  ;; the defeated one — then revive the first.  So the scoped read owes the same defence
  ;; the unscoped one already has.  The potential ranks the **condensation**, so two
  ;; nodes in one component are level rather than ordered, and a walk pruned on a strict
  ;; descent alone answers false for an edge the reader is looking straight at — while
  ;; `genls`, walking the very same visible edges, returns it.
  (let [t (lattice)]
    (tax/add-genl t 'dog 'animal 1 'AContext)
    (tax/add-genl t 'animal 'dog 2 'AContext)
    (tax/add-genl t 'cat 'thing 3 'BContext)          ; a second asserting context, so a
    (tax/restore-depths t)                            ; reader seeing only A is scoped
    (is (= '#{AContext} (tax/visible-ctxs t :genl 'AContext)) "scoping is engaged")
    (testing "the closure walks the cycle"
      (is (= '#{dog animal} (tax/genls t 'dog 'AContext)))
      (is (= '#{dog animal} (tax/specs t 'dog 'AContext))))
    (testing "and the reachability agrees with the closure it claims to answer"
      (is (tax/genl? t 'dog 'animal 'AContext))
      (is (tax/genl? t 'animal 'dog 'AContext)))
    (testing "as does the witness, which is the third reader of the same question"
      (is (= [[1 'AContext]] (tax/reach-support t :genl 'dog 'animal 'AContext)))
      (is (= [[2 'AContext]] (tax/reach-support t :genl 'animal 'dog 'AContext))))
    (testing "a shared component is a reason to keep walking, never an answer"
      ;; mutual reachability is a fact about the *global* edges; B sees neither of them
      (is (not (tax/genl? t 'dog 'animal 'BContext)))
      (is (not (tax/genl? t 'animal 'dog 'BContext)))
      (is (nil? (tax/reach-support t :genl 'dog 'animal 'BContext))))))

(deftest a-scoped-read-follows-belief-per-context
  ;; the payoff of refresh-relation's retarget arm, read back out: the edge is
  ;; supported from A and B, so defeating one supporter moves the answer for one
  ;; reader and not the other.  ctx-counts stays belief-blind — A still holds a
  ;; (disbelieved) supporter, so reader A stays scoped rather than falling into
  ;; the global path.
  (let [t (lattice)]
    (tax/add-genl t 'dog 'animal 1 'AContext)
    (tax/add-genl t 'dog 'animal 2 'BContext)
    (is (tax/genl? t 'dog 'animal 'AContext))
    (is (tax/genl? t 'dog 'animal 'BContext))
    (tax/refresh-beliefs t (into lattice-handles #{2})) ; A's supporter defeated
    (is (not (tax/genl? t 'dog 'animal 'AContext)))
    (is (tax/genl? t 'dog 'animal 'BContext))
    (is (tax/genl? t 'dog 'animal 'WContext) "a reader seeing B still answers")
    (tax/refresh-beliefs t (into lattice-handles #{1 2}))
    (is (tax/genl? t 'dog 'animal 'AContext) "and revival brings A back")))

;; ---- the scoped flat caches -----------------------------------------------

(deftest scoped-disjointness-needs-a-visible-declaration
  (let [t (lattice)]
    (tax/add-disjoint t 'dog 'cat 1 'AContext)
    (testing "visible from the declaring context and its descendants"
      (is (tax/disjoint? t 'dog 'cat 'AContext))
      (is (tax/disjoint? t 'dog 'cat 'WContext)))
    (testing "invisible from a sibling, an ancestor, and a stranger"
      (is (not (tax/disjoint? t 'dog 'cat 'BContext)))
      (is (not (tax/disjoint? t 'dog 'cat 'UContext)))
      (is (not (tax/disjoint? t 'dog 'cat 'OContext))))
    (testing "the unscoped arity still answers globally"
      (is (tax/disjoint? t 'dog 'cat)))
    (testing "a variable context is the unscoped read"
      (is (tax/disjoint? t 'dog 'cat '?ctx)))))

(deftest scoped-disjointness-closes-under-visible-genl-only
  (let [t (lattice)]
    (tax/add-disjoint t 'dog 'cat 1 'AContext)
    (tax/add-genl t 'chihuahua 'dog 2 'BContext)
    (testing "the subtype edge is invisible from A, so A cannot convict chihuahua"
      (is (not (tax/disjoint? t 'chihuahua 'cat 'AContext))))
    (testing "a reader seeing both the declaration and the edge convicts"
      (is (tax/disjoint? t 'chihuahua 'cat 'WContext)))
    (testing "the declaration alone is not enough"
      (is (not (tax/disjoint? t 'chihuahua 'cat 'BContext))))))

(deftest scoped-disjointness-through-a-metatype-needs-all-three-visible
  (let [t (lattice)]
    (tax/mark-disjoint-metatype t 'kind_of_animal 1 'AContext)
    (tax/add-metatype-member t 'kind_of_animal 'dog 2 'AContext)
    (tax/add-metatype-member t 'kind_of_animal 'cat 3 'BContext)
    (testing "the mark and both memberships must be visible together"
      (is (tax/disjoint? t 'dog 'cat 'WContext))
      (is (not (tax/disjoint? t 'dog 'cat 'AContext)) "cat's membership is B's")
      (is (not (tax/disjoint? t 'dog 'cat 'BContext)) "the mark and dog's are A's")
      (is (not (tax/disjoint? t 'dog 'cat 'OContext))))
    (testing "unscoped still answers"
      (is (tax/disjoint? t 'dog 'cat)))))

(deftest scoped-predicate-properties-and-inverse
  (let [t (lattice)]
    (tax/mark-prop t :transitive 'partOf 1 'AContext)
    (tax/add-inverse t 'parentOf 'childOf 2 'BContext)
    (testing "a property holds where its declaration is visible"
      (is (tax/has-prop? t :transitive 'partOf 'AContext))
      (is (tax/has-prop? t :transitive 'partOf 'WContext))
      (is (not (tax/has-prop? t :transitive 'partOf 'BContext)))
      (is (tax/has-prop? t :transitive 'partOf))
      (is (tax/has-prop? t :transitive 'partOf '?ctx)))
    (testing "an inverse answers where its declaration is visible"
      (is (= 'childOf (tax/inverse-of t 'parentOf 'BContext)))
      (is (= 'parentOf (tax/inverse-of t 'childOf 'WContext)))
      (is (nil? (tax/inverse-of t 'parentOf 'AContext)))
      (is (= 'childOf (tax/inverse-of t 'parentOf))))
    (testing "a contextless declaration constrains everywhere"
      (tax/mark-prop t :symmetric 'siblingOf 3)
      (is (tax/has-prop? t :symmetric 'siblingOf 'OContext)))))

(deftest a-flat-cache-follows-belief-per-context
  (let [t (lattice)]
    (tax/add-disjoint t 'dog 'cat 1 'AContext)
    (tax/add-disjoint t 'dog 'cat 2 'BContext)
    (is (tax/disjoint? t 'dog 'cat 'AContext))
    (tax/refresh-beliefs t (into lattice-handles #{2}))
    (testing "A's supporter defeated: A stops convicting, B does not"
      (is (not (tax/disjoint? t 'dog 'cat 'AContext)))
      (is (tax/disjoint? t 'dog 'cat 'BContext)))
    (tax/refresh-beliefs t (into lattice-handles #{1 2}))
    (is (tax/disjoint? t 'dog 'cat 'AContext))))

(deftest the-scoped-memo-budget-flushes-without-changing-answers
  ;; the budget is memory insurance, never semantics: with room for one visset,
  ;; alternating readers flush each other's level and every answer stays right.
  (binding [tax/*scoped-memo-budget* 1]
    (let [t (lattice)]
      (tax/add-genl t 'dog 'animal 1 'AContext)
      (tax/add-genl t 'cat 'animal 2 'BContext)
      (dotimes [_ 3]
        (is (= '#{dog animal} (tax/genls t 'dog 'AContext)))
        (is (= '#{dog} (tax/genls t 'dog 'BContext)))
        (is (= '#{cat animal} (tax/genls t 'cat 'BContext)))
        (is (= '#{cat} (tax/genls t 'cat 'OContext)))))))

;; ---- the reachability witness ----------------------------------------------
;; `reach-support` names one supporter per edge, and whatever depends on the
;; reachability inherits that supporter's context — so which supporter is named decides
;; where a derived conclusion may live.  That choice is therefore held to the same rule
;; every representative choice here is: keyed on content, never on a handle, which is
;; allocated in assertion order (docs/nmtms.md).

(deftest the-edge-witness-is-keyed-on-context-and-never-on-handle
  ;; A and B are incomparable, so no supporter is the more general one and the asserting
  ;; context's *name* is the whole tie-break.  Both handle assignments, both arrival
  ;; orders, one answer: A's supporter, whichever number it drew and whenever it landed.
  (doseq [ha [10 20], a-first? [true false]]
    (let [hb  (if (= ha 10) 20 10)
          t   (lattice)
          add (fn [h c] (tax/add-genl t 'dog 'animal h c))]
      (if a-first?
        (do (add ha 'AContext) (add hb 'BContext))
        (do (add hb 'BContext) (add ha 'AContext)))
      (is (= [[ha 'AContext]] (tax/reach-support t :genl 'dog 'animal 'WContext))
          (str "A's supporter at handle " ha ", asserted "
               (if a-first? "first" "second"))))))

(deftest supporters-sharing-a-context-are-interchangeable
  ;; The only tie the context name leaves is between two supporters of one edge asserted
  ;; from the *same* context — same visibility, same generality, so a dependant inherits
  ;; the identical placement whichever is named and there is nothing beneath the stable
  ;; sort left to decide.  What may not move with arrival order is the context, and the
  ;; two orders agree on it.
  (letfn [(witness-ctx [h1 h2]
            (let [t (lattice)]
              (tax/add-genl t 'dog 'animal h1 'AContext)
              (tax/add-genl t 'dog 'animal h2 'AContext)
              (second (first (tax/reach-support t :genl 'dog 'animal 'WContext)))))]
    (is (= 'AContext (witness-ctx 10 20) (witness-ctx 20 10)))))

;; ---- the oracle ------------------------------------------------------------

(defn- reference-scoped
  "The reference answer: filter the *active* edge set to what `reader` can see —
  by `edge-contexts`, the same state the scoped walk consults, nil constraining
  everywhere — and hand it to the materialized `closures` build."
  [t reader]
  (let [up (tax/context-up t reader)]
    (tax/closures (filter (fn [e]
                            (some (fn [c] (or (nil? c) (contains? up c)))
                                  (tax/edge-contexts t :genl e)))
                          (tax/genl-edges t)))))

(deftest scoped-reads-agree-with-the-filtered-reference-after-random-edits
  ;; edits and scoped reads interleave, so a memo or vis-index entry surviving an
  ;; edit it should not is caught at the very next read.  Deterministic seed;
  ;; edges point up the node order, so the graph stays a DAG.
  (let [t       (lattice)
        rnd     (java.util.Random. 7)
        nodes   '[na nb nc nd ne nf ng]
        ectxs   ['UContext 'AContext 'BContext 'WContext 'OContext nil]
        readers '[UContext AContext BContext WContext DContext OContext EContext ZContext]
        live    (atom {})
        next-h  (atom 0)]
    (dotimes [_ 200]
      (let [op (.nextInt rnd 3)]
        (cond
          (or (zero? op) (empty? @live))
          (let [i (.nextInt rnd (dec (count nodes)))
                j (+ i 1 (.nextInt rnd (- (count nodes) i 1)))
                h (swap! next-h inc)
                c (nth ectxs (.nextInt rnd (count ectxs)))]
            (tax/add-genl t (nth nodes i) (nth nodes j) h c)
            (swap! live assoc h [(nth nodes i) (nth nodes j)]))

          (= 1 op)
          (let [[h [x y]] (nth (vec @live) (.nextInt rnd (count @live)))]
            (tax/del-genl! t x y h)
            (swap! live dissoc h))

          :else
          (tax/refresh-beliefs t (into lattice-handles
                                       (filter (fn [_] (.nextBoolean rnd)))
                                       (keys @live))))
        ;; every reader, every node, against the filtered reference
        (doseq [reader readers]
          (let [ref (reference-scoped t reader)]
            (doseq [n nodes]
              (is (= (get (:up ref) n #{n}) (tax/genls t n reader))
                  (str "genls of " n " from " reader))
              (is (= (get (:down ref) n #{n}) (tax/specs t n reader))
                  (str "specs of " n " from " reader)))
            ;; reachability must agree with the closure it claims to answer
            (doseq [_ (range 3)]
              (let [x (nth nodes (.nextInt rnd (count nodes)))
                    y (nth nodes (.nextInt rnd (count nodes)))]
                (is (= (contains? (get (:up ref) x #{x}) y)
                       (tax/genl? t x y reader))
                    (str "genl? " x " " y " from " reader))))))))))

(deftest scoped-reads-agree-with-the-filtered-reference-over-cyclic-relations
  ;; The oracle above points every edge up the node order, so the graph it walks is
  ;; always a DAG — and a DAG is the one shape where the depth potential ranks *nodes*.
  ;; This one lets an edge point either way, which is the shape it ranks by **component**,
  ;; and the shape a scoped read pruned on a strict descent alone gets wrong.  Three
  ;; readers of one question are held to one answer: the closure, the reachability, and
  ;; the witness the reachability rests on.
  (let [t       (lattice)
        rnd     (java.util.Random. 11)
        nodes   '[na nb nc nd ne]
        ectxs   ['AContext 'BContext nil]
        readers '[AContext BContext WContext OContext]
        live    (atom {})
        next-h  (atom 0)]
    (dotimes [_ 60]
      (let [op (.nextInt rnd 4)]
        (cond
          (or (< op 2) (empty? @live))
          (let [i (.nextInt rnd (count nodes))
                j (.nextInt rnd (count nodes))]
            (when (not= i j)                            ; either direction: cycles welcome
              (let [h (swap! next-h inc)
                    c (nth ectxs (.nextInt rnd (count ectxs)))]
                (tax/add-genl t (nth nodes i) (nth nodes j) h c)
                (swap! live assoc h [(nth nodes i) (nth nodes j)]))))

          (= 2 op)
          (let [[h [x y]] (nth (vec @live) (.nextInt rnd (count @live)))]
            (tax/del-genl! t x y h)
            (swap! live dissoc h))

          ;; the repair a settle would run: with it the potential is sound and the
          ;; prunings engage, without it the relation is loose and they are dropped —
          ;; the reads must agree either way
          :else (tax/restore-depths t)))
      (doseq [reader readers]
        (let [ref (reference-scoped t reader)
              up  #(get (:up ref) % #{%})]
          (doseq [x nodes]
            (is (= (up x) (tax/genls t x reader)) (str "genls of " x " from " reader))
            (is (= (get (:down ref) x #{x}) (tax/specs t x reader))
                (str "specs of " x " from " reader))
            (doseq [y nodes]
              (is (= (contains? (up x) y) (tax/genl? t x y reader))
                  (str "genl? " x " " y " from " reader))
              (is (= (contains? (up x) y)
                     (some? (tax/reach-support t :genl x y reader)))
                  (str "reach-support " x " " y " from " reader)))))))))

;; ---- the scoped equality partition ------------------------------------------
;; `scoped-class` is the equality analogue, and it is not a filter of the global
;; partition: dropping an edge can *split* a class, so the members and the elected
;; representative are both recomputed over what the reader can see.  Its reference is
;; therefore `equality-partition` — the same from-scratch build `taxonomy_test` checks
;; the incremental union against — handed only the visible edges and their preferences.

(deftest scoped-class-agrees-with-the-filtered-reference-after-random-edits
  (let [terms '[ta tb tc td te]
        ctxs  ['AContext 'BContext 'OContext nil]]
    (doseq [seed (range 4)]
      (let [t      (lattice)
            rnd    (java.util.Random. (+ 100 seed))
            pick   (fn [v] (nth v (.nextInt rnd (count v))))
            live   (atom {})                        ; handle -> [a b preferred ctx]
            out    (atom #{})                       ; the disbelieved supporters
            next-h (atom 0)]
        (dotimes [_ 50]
          (let [op (.nextInt rnd 4)]
            (cond
              (or (< op 2) (empty? @live))
              (let [a (pick terms), b (pick terms)]
                (when (not= a b)
                  (let [h (swap! next-h inc)
                        ;; a `rewriteOf` names one side preferred; `sameAs` names neither
                        p (pick [a b nil])
                        c (pick ctxs)]
                    (tax/add-equality t a b h p)
                    (swap! live assoc h [a b p c]))))

              (= 2 op)
              (let [[h [a b]] (nth (vec @live) (.nextInt rnd (count @live)))]
                (tax/del-equality! t a b h)
                (swap! live dissoc h))

              :else
              (let [o (into #{} (filter (fn [_] (.nextBoolean rnd))) (keys @live))]
                (reset! out o)
                (tax/refresh-beliefs t (complement o)))))

          (doseq [reader '[AContext BContext WContext OContext]]
            (let [up    (tax/context-up t reader)
                  seen? (fn [h] (let [[_ _ _ c] (@live h)]
                                  (and (not (@out h)) (or (nil? c) (contains? up c)))))
                  vis-h (into #{} (filter seen?) (keys @live))
                  ;; the same canonical undirected key `pair` builds, so the reference's
                  ;; edges and its preference claims land on one another
                  edges (into #{} (map (fn [h] (vec (sort-by str (subvec (@live h) 0 2)))))
                              vis-h)
                  prefs (into #{} (keep (fn [h] (let [[a b p] (@live h)]
                                                  (when p [p (if (= p a) b a)]))))
                              vis-h)
                  ref   (tax/equality-partition edges prefs)]
              (doseq [x terms]
                (let [[members rep] (tax/scoped-class t x seen?)]
                  (is (= (get (:members ref) (get (:class ref) x x) #{x}) members)
                      (str "members of " x " from " reader))
                  (is (= (get (:class ref) x x) rep)
                      (str "representative of " x " from " reader)))))))))))

;; ---- the disjointness witnesses ---------------------------------------------
;; `disjointness-witnesses` answers a *scoped* question from unscoped state: each yield
;; is one complete derivation's supporting contexts, and the claim is that a reader sees
;; the clash iff it sees every context in some one of them.  That claim is the exposure
;; story's floor, and it is only worth anything if it agrees with the verdict
;; `disjoint?` reaches by walking the same declarations under the same visibility.

(deftest a-witness-is-seen-by-exactly-the-readers-that-see-the-clash
  (doseq [seed (range 3)]
    (let [t       (lattice)
          rnd     (java.util.Random. (+ 200 seed))
          nodes   '[na nb nc nd ne nf]
          ectxs   ['AContext 'BContext nil]
          readers '[AContext BContext WContext OContext]
          pick    (fn [v] (nth v (.nextInt rnd (count v))))
          next-h  (atom 1000)]
      (dotimes [_ 30]
        (let [h (swap! next-h inc), c (pick ectxs)]
          (case (.nextInt rnd 5)
            (0 1) (let [i (.nextInt rnd (dec (count nodes)))         ; a genl edge, DAG
                        j (+ i 1 (.nextInt rnd (- (count nodes) i 1)))]
                    (tax/add-genl t (nth nodes i) (nth nodes j) h c))
            2     (let [a (pick nodes), b (pick nodes)]
                    (when (not= a b) (tax/add-disjoint t a b h c)))
            3     (tax/mark-disjoint-metatype t 'MetaOne h c)
            4     (tax/add-metatype-member t 'MetaOne (pick nodes) h c)))
        (doseq [r readers]
          (let [up (tax/context-up t r)]
            (doseq [a nodes, b nodes :when (not= a b)]
              (is (= (tax/disjoint? t a b r)
                     (boolean (some (fn [w] (every? #(contains? up %) w))
                                    (tax/disjointness-witnesses t a b))))
                  (str "clash " a "/" b " from " r)))))))))

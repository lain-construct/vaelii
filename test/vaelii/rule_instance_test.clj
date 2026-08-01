(ns vaelii.rule-instance-test
  "A rule's variables are the rule's own, and every *instance* of it needs its own.

Both backward chainers thread one binding map down a derivation path and hand it to
  every expansion on it, so two instances of one rule meet each other there.  The
  collision is between *canonical* names — a stored rule is spelled `?var0 ?var1 …`
  (`sentex/canonicalize-rule`), so every rule in the KB draws from one small pool of
  names and colliding is the normal case rather than the unlucky one.

  What a collision costs is an answer, not time: the unification that should have
  succeeded fails, and the branch under it is never explored.  So each test here asks a
  query whose answer is a closure the KB plainly contains, and asks it of all three
  engines — they must agree with each other and with the closure."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.inference :as inference]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- node-prove
  "`prove` on the node engine.  The depth is chosen here because the engine has no
  default: 8 covers every derivation these fixtures build."
  [kb goal context]
  (binding [v/*query-engine* :inference, inference/*max-depth* 8]
    (v/prove kb goal context)))

(defn- level-7-prove
  "Backward chaining at level 7 of the lookup stack — the recursive chainer with the
  *registry* as its leaf rather than stored facts, which is a third search and not a
  spelling of one of the other two."
  [kb goal context]
  (map :bindings (v/lookup kb 7 goal context)))

(defn- all-engines
  "`[prove level-7 node-engine]` answers for `goal`'s variable `var`, each as a set.

  Three engines and not two: the point of the sweep is that independently written
  searches agree.  `ask` is not among them and cannot be — it expands no rule, so it
  has no answer to these questions at all."
  [kb goal context var]
  (mapv #(set (map (fn [s] (get s var)) (doall (% kb goal context))))
        [v/prove level-7-prove node-prove]))

(defn- agree
  "Every engine's answer for `var`, asserted equal to `expected` — and to each other."
  [kb goal context var expected]
  (let [[p b a] (all-engines kb goal context var)]
    (is (= expected p) (str "prove disagrees on " (pr-str goal)))
    (is (= expected b) (str "level 7 disagrees on " (pr-str goal)))
    (is (= expected a) (str "the node engine disagrees on " (pr-str goal)))))

(tu/deftest-kb a-recursive-rule-meets-itself-down-one-path
  ;; (anc ?x ?z) :- (parentOf ?x ?y) (anc ?y ?z) — used twice on one path, the second
  ;; instance's ?x has to be the child where the first's was the grandchild.  Sharing
  ;; the name asks unify to make them equal, which fails, and the query answers only at
  ;; distance one.
  (tu/with-terms [parentOf anc ChainContext]
    (let [n (fn [i] (symbol (str "ChainN" i)))]
      (doseq [i (range 4)]
        (v/assert kb (list parentOf (n i) (n (inc i))) ChainContext))
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) ChainContext
                     {:direction :backward})
      (v/assert-rule kb [(list parentOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z)
                     ChainContext {:direction :backward})
      (testing "the whole ancestor chain, not just the parent"
        (agree kb (list anc (n 0) '?z) ChainContext '?z
               (set (map n (range 1 5)))))
      (testing "and read from the other end"
        (agree kb (list anc '?x (n 4)) ChainContext '?x
               (set (map n (range 0 4))))))))

(tu/deftest-kb a-left-recursive-rule-meets-itself-too
  (tu/with-terms [parentOf lanc LeftContext]
    (let [n (fn [i] (symbol (str "LeftN" i)))]
      (doseq [i (range 4)]
        (v/assert kb (list parentOf (n i) (n (inc i))) LeftContext))
      (v/assert-rule kb [(list parentOf '?x '?z)] (list lanc '?x '?z) LeftContext
                     {:direction :backward})
      (v/assert-rule kb [(list lanc '?x '?y) (list parentOf '?y '?z)] (list lanc '?x '?z)
                     LeftContext {:direction :backward})
      (agree kb (list lanc (n 0) '?z) LeftContext '?z (set (map n (range 1 5)))))))

(tu/deftest-kb an-inner-rules-variable-does-not-bind-an-outer-rules-sibling
  ;; The outer rule's second conjunct is still unsolved when the first is expanded, so
  ;; its variables are unbound and unmentioned in the bindings — and an inner rule with
  ;; one more variable than the goal asked about (an existential in its antecedent)
  ;; occupies the very same canonical slot.  Merging its answer whole binds the outer
  ;; conjunct's ?var2 to the existential's value, and the conjunct then matches nothing.
  (tu/with-terms [linkA linkB reach side ReachContext]
    (tu/with-terms [Start Middle Target Existential]
      (v/assert-rule kb [(list linkA '?a '?b) (list linkB '?b '?c)] (list reach '?a '?c)
                     ReachContext {:direction :backward})
      (v/assert-rule kb [(list side '?p '?q '?r)] (list linkA '?p '?q) ReachContext
                     {:direction :backward})
      (v/assert kb (list side Start Middle Existential) ReachContext)
      (v/assert kb (list linkB Middle Target) ReachContext)
      (agree kb (list reach Start '?c) ReachContext '?c #{Target}))))

(tu/deftest-kb a-query-may-use-the-names-stored-rules-are-spelled-with
  ;; Nothing stops a caller writing ?var0 / ?var1, and a rule's consequent is stored in
  ;; exactly those.  Crossed over, the two are asked to unify with each other, and the
  ;; occurs check — correctly — refuses the cycle, so the rule does not fire at all.
  (tu/with-terms [edgeX hopX HopContext]
    (tu/with-terms [HopFrom HopTo]
      (v/assert kb (list edgeX HopFrom HopTo) HopContext)
      (v/assert-rule kb [(list edgeX '?m '?n)] (list hopX '?m '?n) HopContext
                     {:direction :backward})
      (testing "straight through"
        (agree kb (list hopX HopFrom '?var1) HopContext '?var1 #{HopTo}))
      (testing "crossed over — the goal's ?var1 sits where the rule's ?var0 does"
        (agree kb (list hopX '?var1 '?var0) HopContext '?var1 #{HopFrom})
        (agree kb (list hopX '?var1 '?var0) HopContext '?var0 #{HopTo})))))

(tu/deftest-kb an-exception-still-blocks-a-renamed-instance
  ;; A guard reads the rule's *own* variable names out of the completed bindings, so a
  ;; renamed instance has to bind them back before asking.  A guard that stopped firing
  ;; under renaming would be an exception that silently lapsed at depth.
  (tu/with-terms [parentOf anc estranged GuardContext]
    (tu/with-terms [GuardA GuardB GuardC]
      (v/assert kb (list parentOf GuardA GuardB) GuardContext)
      (v/assert kb (list parentOf GuardB GuardC) GuardContext)
      (v/assert kb (list estranged GuardB) GuardContext)
      (v/assert kb (list 'exceptWhen (list estranged '?x)
                         (list 'set/defaultRule
                               (list 'implies (list parentOf '?x '?z) (list anc '?x '?z))))
                GuardContext)
      (v/assert-rule kb [(list parentOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z)
                     GuardContext {:direction :backward})
      (testing "the base rule is blocked for the estranged parent at every depth"
        ;; GuardA reaches GuardB by the base rule; the recursive rule would take it on
        ;; to GuardC through (anc GuardB ?z), and *that* firing of the base rule is the
        ;; excepted one.
        (agree kb (list anc GuardA '?z) GuardContext '?z #{GuardB})
        (agree kb (list anc GuardB '?z) GuardContext '?z #{})))))

(tu/deftest-kb renaming-is-deterministic
  ;; The renamed variables reach the caller — `prove` returns raw binding maps — so a
  ;; gensym would make the same query answer differently on every run, in an engine
  ;; whose contract is that it does not.
  (tu/with-terms [parentOf anc DetContext]
    (let [n (fn [i] (symbol (str "DetN" i)))]
      (doseq [i (range 3)]
        (v/assert kb (list parentOf (n i) (n (inc i))) DetContext))
      (v/assert-rule kb [(list parentOf '?x '?z)] (list anc '?x '?z) DetContext
                     {:direction :backward})
      (v/assert-rule kb [(list parentOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z)
                     DetContext {:direction :backward})
      ;; the renamed variables are visible only in the DFS's *raw* binding maps; the
      ;; node engine projects onto the query's variables, so it has none to be
      ;; deterministic about
      (let [goal  (list anc (n 0) '?z)
            once  (binding [v/*query-engine* :dfs] (set (v/prove kb goal DetContext)))
            twice (binding [v/*query-engine* :dfs] (set (v/prove kb goal DetContext)))]
        (is (= once twice) "the same query returned different binding maps"))
      ;; The renamed names are not observable through an engine any more — a solution is
      ;; projected onto the query's own variables — so determinism is asserted where it
      ;; is decided.  A gensym here would give an engine whose contract is order
      ;; independence a different answer on every run of one query.
      (testing "and the renaming behind it is deterministic where it happens"
        (let [rule  (first (provers/candidate-rules kb (list anc (n 0) '?z) DetContext))
              taken '#{?var0 ?var1}
              a     (res/freshen-rule rule taken)
              b     (res/freshen-rule rule taken)]
          (is (= (:consequent a) (:consequent b)))
          (is (= (:antecedents a) (:antecedents b)))
          (is (some #(re-find #"'" (name %)) (res/form-variables (:consequent a)))
              "nothing here needs renaming, so this is not measuring what it claims"))))))

;; ---- what a solution is a map over ---------------------------------------

(tu/deftest-kb a-solution-is-a-map-over-the-question-not-over-the-proof
  ;; A derivation path accumulates one flat binding map, and every instance it expands
  ;; contributes its own names to it.  Those are scratch — how the search got there, not
  ;; what it was asked — so a solution is cut down to the query's own variables at the
  ;; moment it is finished.  Without that the three engines return three different maps
  ;; for one question, and only `ask` returns the one the asker can read.
  (tu/with-terms [edgeOf anc ProjContext]
    (tu/with-terms [PjA PjB PjC]
      (v/assert kb (list edgeOf PjA PjB) ProjContext)
      (v/assert kb (list edgeOf PjB PjC) ProjContext)
      (v/assert-rule kb [(list edgeOf '?x '?z)] (list anc '?x '?z) ProjContext
                     {:direction :backward})
      (v/assert-rule kb [(list edgeOf '?x '?y) (list anc '?y '?z)] (list anc '?x '?z)
                     ProjContext {:direction :backward})
      (testing "every engine keys its answers by the query's variables and nothing else"
        (doseq [[label f] [["prove" v/prove] ["level 7" level-7-prove]
                           ["node engine" node-prove]]]
          (let [sols (doall (f kb (list anc PjA '?z) ProjContext))]
            (is (seq sols) label)
            (is (every? #(= #{'?z} (set (keys %))) sols)
                (str label " leaked a variable the asker never wrote: " (pr-str sols))))))
      (testing "and the three of them return the same maps, not merely the same answers"
        (is (= (set (v/prove kb (list anc PjA '?z) ProjContext))
               (set (node-prove kb (list anc PjA '?z) ProjContext))
               (set (level-7-prove kb (list anc PjA '?z) ProjContext))
               #{{'?z PjB} {'?z PjC}})))
      (testing "a ground query asks about no variables, so it answers with an empty map"
        (is (= [{}] (v/prove kb (list anc PjA PjC) ProjContext)))
        (is (= [{}] (vec (node-prove kb (list anc PjA PjC) ProjContext)))))
      (testing "a query that writes the canonical names is asking about them"
        ;; `?var0` is a spelling, not a reservation: a variable belongs to whoever
        ;; wrote it, and a query using the rules' own names must still be answered.
        (is (= #{{'?var1 PjA '?var0 PjB} {'?var1 PjB '?var0 PjC} {'?var1 PjA '?var0 PjC}}
               (set (v/prove kb (list anc '?var1 '?var0) ProjContext)))))
      (testing "a bounded run projects too, and resuming it keeps the projection"
        (let [r (v/prove-within kb (list anc PjA '?z) ProjContext {:max-results 1})]
          (is (= :capped (:status r)))
          (is (= #{{'?z PjB} {'?z PjC}}
                 (into (set (:results r)) (:results (v/resume r {}))))))))))

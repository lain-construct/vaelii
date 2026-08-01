(ns vaelii.strength-test
  "The defeat-class lattice, and the least fixpoint that computes it.

  `vaelii.impl.strength` is forty lines of total order, and `jtms/region-classes`
  solves a *recursive* equation over it: a justification confers no more than the
  weakest of its antecedents' classes, so a node's class depends on its
  antecedents'.  The docstring there says a single pass \"would be subtly wrong and
  would look fine\" — these tests are what makes that checkable.

  Like `jtms_blocked_test`, these are **pure**: no store, no fixture.  The
  graph is built by hand so a claim about a *region* is checkable rather than
  inferred from an end-to-end belief."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.strength :as strength]))

;; ---- tiny graph builders (same shape as jtms_blocked_test) --------------

(defn- premise
  ([tms d] (premise tms d :default))
  ([tms d s] (jtms/add-premise tms d s) d))

(defn- justify
  ([tms jid antes conseq] (justify tms jid antes conseq :monotonic))
  ([tms jid antes conseq strength]
   (jtms/ensure-node tms conseq 1)
   (jtms/add-justification tms (jtms/->just jid 'rule antes conseq {} strength))
   jid))

;; ---- the lattice itself --------------------------------------------------

(deftest the-lattice-is-a-total-order-of-exactly-two-classes
  (testing "monotonic > default, and `assertable` is exactly those two"
    (is (= #{:monotonic :default} strength/assertable))
    (is (strength/assertable? :monotonic))
    (is (strength/assertable? :default))
    (is (not (strength/assertable? :strict))
        "the third class was deleted — do not reintroduce it"))
  (testing "min picks the weaker, max the stronger, in both argument orders"
    (is (= :default   (strength/min :monotonic :default)))
    (is (= :default   (strength/min :default :monotonic)))
    (is (= :monotonic (strength/max :monotonic :default)))
    (is (= :monotonic (strength/max :default :monotonic))))
  (testing "both are idempotent"
    (doseq [c [:monotonic :default]]
      (is (= c (strength/min c c)))
      (is (= c (strength/max c c)))))
  (testing "the predicates split the lattice"
    (is (strength/defeasible? :default))
    (is (not (strength/defeasible? :monotonic)))
    (is (strength/known-true? :monotonic))
    (is (not (strength/known-true? :default)))))

(deftest an-unknown-class-ranks-below-default
  ;; `rank-of` returns 0 for anything it does not know, which makes an unknown class
  ;; *weaker* than :default under min and *loses* to it under max.  Every caller in
  ;; the engine guards against handing nil in (`conferred-class` seeds with
  ;; `(or (:strength j) :monotonic)` and reads antecedent classes with a `:default`
  ;; default), so this pins the fallback rather than a live code path — but it is the
  ;; behaviour those guards are guarding, and a change here would move belief.
  (is (= 0 (strength/rank-of nil)))
  (is (= 0 (strength/rank-of :strict)) "a deleted class is simply unknown")
  (is (nil? (strength/min :monotonic nil)) "unknown is weaker, so min yields it")
  (is (= :monotonic (strength/max :monotonic nil)))
  (testing "class-of-rank is min's inverse on the two real classes, and total"
    (is (= :default   (strength/class-of-rank 1)))
    (is (= :monotonic (strength/class-of-rank 2)))
    (is (= :default   (strength/class-of-rank 99)) "out of range falls back to the weakest")))

;; ---- the class equation is a FIXPOINT, not a pass -----------------------

(deftest a-monotonic-chain-stays-monotonic-to-its-end
  ;; 1 ⇒ 2 ⇒ 3 ⇒ 4, every link a bare (:monotonic) rule over a :monotonic premise.
  ;; Each conclusion is monotonically entailed, so all four are :monotonic.
  ;;
  ;; This is THE test for `region-classes` being a least fixpoint.  Building the chain
  ;; incrementally cannot show it: each `add-justification` relabels a region of one
  ;; node whose antecedent is *boundary*, read from stored `:classes` and already
  ;; correct — so a single-pass implementation gets the right answer too.  The
  ;; discriminating move is a relabel whose region holds the whole chain at once.
  ;; Then every in-region node starts at :default (the bottom), and one Jacobi pass
  ;; propagates :monotonic exactly one hop: node 4 would read :default and stay there.
  (let [tms (jtms/create-tms)]
    (premise tms 1 :monotonic)
    (justify tms 101 [1] 2)
    (justify tms 102 [2] 3)
    (justify tms 103 [3] 4)
    (testing "built incrementally — every hop is monotonically entailed"
      (is (= [:monotonic :monotonic :monotonic :monotonic]
             (mapv #(jtms/defeat-class tms %) [1 2 3 4]))))

    (testing "and after a whole-graph relabel, whose region is the entire chain"
      (jtms/relabel tms)
      (is (= :monotonic (jtms/defeat-class tms 4))
          "node 4 is three hops from the premise: a single pass would leave it :default")
      (is (= [:monotonic :monotonic :monotonic :monotonic]
             (mapv #(jtms/defeat-class tms %) [1 2 3 4]))))

    (testing "and after defeat + clear-defeats, whose region is also the whole chain"
      (jtms/defeat tms [1])
      (is (not-any? #(jtms/in? tms %) [1 2 3 4]))
      (jtms/clear-defeats! tms)
      (is (every? #(jtms/in? tms %) [1 2 3 4]))
      (is (= :monotonic (jtms/defeat-class tms 4))))))

(deftest a-default-anywhere-in-a-chain-caps-everything-after-it
  ;; The dual: one :default premise at the head, and the whole chain is :default —
  ;; a conclusion is never stronger than what it rests on.  Together with the test
  ;; above this pins propagation in both directions over more than one hop.
  (let [tms (jtms/create-tms)]
    (premise tms 1 :default)
    (justify tms 101 [1] 2)
    (justify tms 102 [2] 3)
    (jtms/relabel tms)
    (is (= [:default :default :default]
           (mapv #(jtms/defeat-class tms %) [1 2 3])))))

;; ---- min(own strength, weakest antecedent) -----------------------------

(deftest a-justification-confers-the-min-of-its-own-strength-and-its-antecedents
  (testing "the ANTECEDENT binds: a bare rule over a :default premise concludes :default"
    (let [tms (jtms/create-tms)]
      (premise tms 1 :default)
      (justify tms 101 [1] 2 :monotonic)
      (is (= :default (jtms/defeat-class tms 2)))))

  (testing "the RULE binds: a defeasible rule over a :monotonic premise concludes :default"
    ;; The half of `min` that no other test reaches — every defeasible rule elsewhere
    ;; in the suite fires over :default antecedents, so the rule's own :default is
    ;; never the binding constraint.  Seeding `conferred-class` at :monotonic instead
    ;; of `(or (:strength j) :monotonic)` would pass everything but this.
    (let [tms (jtms/create-tms)]
      (premise tms 1 :monotonic)
      (justify tms 101 [1] 2 :default)
      (is (= :default (jtms/defeat-class tms 2))
          "a defeasible rule introduces defeasibility even over known-true facts")))

  (testing "neither binds: a bare rule over :monotonic premises concludes :monotonic"
    (let [tms (jtms/create-tms)]
      (premise tms 1 :monotonic)
      (justify tms 101 [1] 2 :monotonic)
      (is (= :monotonic (jtms/defeat-class tms 2))))))

(deftest the-weakest-of-several-antecedents-decides
  ;; The reduce runs over *every* antecedent, so a single :default among :monotonic
  ;; ones caps the conclusion.  Reducing over only the first, or using max instead of
  ;; min, survives every other test in the suite.
  (let [tms (jtms/create-tms)]
    (premise tms 1 :monotonic)
    (premise tms 2 :default)
    (premise tms 3 :monotonic)
    (justify tms 101 [1 2 3] 4 :monotonic)
    (is (= :default (jtms/defeat-class tms 4))
        "the :default antecedent sits in the middle — the reduce must see all three")
    (testing "with the weak antecedent removed the conclusion is monotonic again"
      (justify tms 102 [1 3] 5 :monotonic)
      (is (= :monotonic (jtms/defeat-class tms 5))))))

(deftest the-informant-is-excluded-from-the-cap
  ;; A rule is an antecedent of its own justification (so retracting it withdraws what
  ;; it licensed), but that is a validity role, not a ground.  Capping on it would put
  ;; every derived datum at the rule's own assumption strength — :default — and no
  ;; conclusion could ever be :monotonic.
  (let [tms (jtms/create-tms)]
    (premise tms 1 :monotonic)
    (premise tms 99 :default)                     ; the rule sentex itself
    (jtms/ensure-node tms 2 1)
    (jtms/add-justification tms (jtms/->just 101 99 [1 99] 2 {} :monotonic))
    (is (= :monotonic (jtms/defeat-class tms 2))
        "the :default informant is an antecedent but must not cap the conclusion")))

;; ---- locality: a region relabel agrees with the whole graph -------------

(deftest a-region-relabel-agrees-with-a-whole-graph-relabel
  ;; The reconciliation the whole design rests on (docs/nmtms.md): a least fixpoint
  ;; over the affected region with the boundary held fixed is unique and equals the
  ;; global one.  Every operation below relabels only a region; `jtms/relabel` then
  ;; recomputes from scratch over every node.  The two must agree exactly — on
  ;; belief, on groundability, and on class.
  ;;
  ;; No blocking here on purpose: `relabel` clears the blocked set (it is derived from
  ;; exception queries that are never stored), so a blocked graph legitimately differs.
  (let [tms (jtms/create-tms)]
    (premise tms 1 :monotonic)
    (premise tms 2 :default)
    (premise tms 3 :default)
    (justify tms 101 [1] 10)
    (justify tms 102 [2] 11 :default)
    (justify tms 103 [10 11] 12)
    (justify tms 104 [3] 12)                      ; a second, independent witness for 12
    (justify tms 105 [12] 13)
    (jtms/defeat tms [11])
    (jtms/retract! tms 3)
    (let [snapshot (select-keys @tms [:in :groundable :classes])]
      (jtms/relabel tms)
      (let [rebuilt (select-keys @tms [:in :groundable :classes])]
        (is (= (:in snapshot) (:in rebuilt))
            "belief computed region-locally matches belief computed globally")
        (is (= (:groundable snapshot) (:groundable rebuilt)))
        (is (= (:classes snapshot) (:classes rebuilt))
            "and so do the defeat-classes — the class fixpoint is region-independent")))))

;; ---- well-foundedness ----------------------------------------------------

(deftest an-ungrounded-support-cycle-never-believes-itself
  ;; The classic JTMS failure: 11 and 12 justify each other, so once both are IN each
  ;; "supports" the other and a naive relabel keeps them forever.  `region-fixpoint`
  ;; starts from *nothing believed inside the region* and only ever adds, so a cycle
  ;; with no ground outside it never enters.
  (let [tms (jtms/create-tms)]
    (premise tms 1)
    (justify tms 101 [1] 11)                      ; the ground
    (justify tms 102 [11] 12)                     ; 11 ⇒ 12
    (justify tms 103 [12] 11)                     ; 12 ⇒ 11  — the cycle
    (is (every? #(jtms/in? tms %) [11 12]) "grounded through the premise, both hold")

    (let [{:keys [removed-sentexes]} (jtms/retract! tms 1)]
      (testing "pulling the ground collapses the cycle rather than letting it self-support"
        (is (not-any? #(jtms/in? tms %) [11 12]))
        (is (not-any? #(contains? (:groundable @tms) %) [11 12])
            "neither is structurally derivable any more"))
      (testing "and the sweep collects both — they are orphans, not defeated datums"
        (is (= #{1 11 12} (set removed-sentexes)))))))

(deftest a-cycle-with-a-second-ground-survives-losing-the-first
  ;; The complement: the same cycle, but reachable from a premise that stays.  Nothing
  ;; may be swept, or `region-fixpoint` is over-eager rather than well-founded.
  (let [tms (jtms/create-tms)]
    (premise tms 1)
    (premise tms 2)
    (justify tms 101 [1] 11)
    (justify tms 102 [11] 12)
    (justify tms 103 [12] 11)
    (justify tms 104 [2] 12)                      ; a second ground, into the cycle
    (jtms/retract! tms 1)
    (is (every? #(jtms/in? tms %) [11 12])
        "12 is grounded by premise 2, and 11 by the cycle edge from 12")))

;; ---- duplicate-support suppression --------------------------------------

(deftest has-justification-keys-on-informant-and-the-antecedent-set
  ;; The guard `core` uses to avoid recording the same justification twice.  It keys on
  ;; the informant plus the antecedents *as a set*, so antecedent order does not
  ;; matter but a different informant does.
  (let [tms (jtms/create-tms)]
    (premise tms 1)
    (premise tms 2)
    (justify tms 101 [1 2] 3)
    (is (jtms/has-justification? tms 'rule [1 2] 3))
    (is (jtms/has-justification? tms 'rule [2 1] 3) "antecedent order is not identity")
    (is (not (jtms/has-justification? tms 'other [1 2] 3)) "a different rule is a different support")
    (is (not (jtms/has-justification? tms 'rule [1] 3))   "a different antecedent set is too")
    (is (not (jtms/has-justification? tms 'rule [1 2] 4)) "and so is a different conclusion")))

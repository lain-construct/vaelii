;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.jtms-locality-test
  "Locality for the operations `jtms_blocked_test` does not cover, and `sweep!`'s
  semantics.

  docs/nmtms.md publishes a measured, flat-in-graph-size claim for
  `add-justification`, `defeat` and `clear-defeats!` — \"defeat went from 16.9ms to
  8µs at 4000 nodes, and is now flat in graph size\".  The instrument that makes that
  checkable already exists (`regions-touched`, in `jtms_blocked_test`), but it is
  applied to `set-blocked` alone.  So a regression in any of the other three — a
  region widened back to `(set (keys (:nodes state)))`, say — costs a 2000× slowdown
  that no assertion catches and only a benchmark nobody runs would notice.

  Measuring the *region* rather than a wall clock is what makes this a test rather
  than a flake: the claim is about how much work is scoped, not how fast the machine
  is.

  Pure — no store, no fixture.  Helpers are duplicated from
  `jtms_blocked_test` rather than shared, so the two files stay independent."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.jtms :as jtms]))

;; ---- builders (deliberately duplicated — see the ns docstring) ----------

(defn- premise
  ([tms d] (premise tms d :default))
  ([tms d s] (jtms/add-premise tms d s) d))

(defn- justify
  ([tms jid antes conseq] (justify tms jid antes conseq :monotonic))
  ([tms jid antes conseq strength]
   (jtms/ensure-node tms conseq 1)
   (jtms/add-justification tms (jtms/->just jid 'rule antes conseq {} strength))
   jid))

(defn- regions-touched
  "The sizes of every region `relabel-region*` was asked to recompute while `f` ran."
  [f]
  (let [sizes (atom [])
        orig  @#'jtms/relabel-region*]
    (with-redefs [jtms/relabel-region* (fn [state region]
                                         (swap! sizes conj (count region))
                                         (orig state region))]
      (f))
    @sizes))

(defn- fan-of
  "`n` independent premise ⇒ conclusion pairs: premise 2i, conclusion 2i+1,
  justification 1000+i.  Nothing connects the pairs, so a correctly-scoped
  operation on one of them must not grow with `n`."
  [n]
  (let [tms (jtms/create-tms)]
    (dotimes [i n]
      (premise tms (* 2 i))
      (justify tms (+ 1000 i) [(* 2 i)] (inc (* 2 i))))
    tms))

(defn- chain-of
  "A depth-`n` linear derivation: premise 0, then justification 2000+i concludes i+1
  from i, so node n rests on a chain of n justifications.  The region a root change
  relabels is the whole chain — the shape that exercises depth."
  ([n] (chain-of n :default))
  ([n strength]
   (let [tms (jtms/create-tms)]
     (premise tms 0 strength)
     (dotimes [i n]
       (justify tms (+ 2000 i) [i] (inc i) strength))
     tms)))

(def ^:private sizes [50 500 2000])

;; ---- locality of the three operations docs/nmtms.md measures ------------

(deftest defeat-touches-only-the-affected-region
  (testing "defeating one datum relabels its forward closure, at any graph size"
    (doseq [n sizes]
      (let [tms (fan-of n)]
        (is (= [1] (regions-touched #(jtms/defeat tms [1])))
            (str "region grew with the graph at n=" n)))))
  (testing "the region is the forward closure, so a chain is reached but nothing else"
    (let [tms (fan-of 500)]
      (justify tms 9001 [1] 100001)
      (justify tms 9002 [100001] 100002)
      (is (= [3] (regions-touched #(jtms/defeat tms [1])))
          "the defeated datum plus its two descendants — not the other 499 pairs"))))

(deftest clearing-defeats-touches-only-what-was-defeated
  (testing "revival is scoped to the previously-defeated nodes and their closure"
    (doseq [n sizes]
      (let [tms (fan-of n)]
        (jtms/defeat tms [1])
        (is (= [1] (regions-touched #(jtms/clear-defeats! tms)))
            (str "region grew with the graph at n=" n)))))
  (testing "a settle that defeated nothing relabels no node"
    ;; `settle` calls `clear-defeats!` unconditionally on every assert, and most
    ;; settles defeat nothing — so this is the hottest path through the module.  The
    ;; region comes out empty and `relabel-region*` is entered once on it, which is
    ;; O(1) the whole way down: no candidate justifications, an empty fixpoint loop,
    ;; and `set/difference` against an empty set reduces over nothing and returns its
    ;; argument.  What must never come back is a *non-empty* region here.
    (let [tms (fan-of 500)]
      (is (every? zero? (regions-touched #(jtms/clear-defeats! tms)))
          "with an empty defeated set there is nothing to revive"))))

(deftest adding-a-justification-touches-only-its-consequence
  (testing "a new justification relabels its conclusion, not the graph"
    (doseq [n sizes]
      (let [tms (fan-of n)]
        (is (= [1] (regions-touched #(justify tms 77777 [0] 999999)))
            (str "region grew with the graph at n=" n))))))

(deftest a-redundant-justification-relabels-nothing-and-is-still-in-the-window
  ;; The two halves of the fast path, and each is a bug without the other.
  ;;
  ;; **Relabels nothing** is what collapses a recursive forward load from O(derived²):
  ;; an already-IN node feeds its consequences identically on one witness or two, so a
  ;; second derivation must not walk its forward closure again.
  ;;
  ;; **Still in the window** is what a reader of `touched` needs, and belief cannot say
  ;; it: `settle/record-clashes!` republishes a standing clash's supporting
  ;; justifications every settle and carries the report forward for a pair the window
  ;; does not hold, so a silent arrival is a `contradictions` entry naming fewer reasons
  ;; than the KB holds.  `touched-in` takes it too — the datum was believed before, and a
  ;; window that said otherwise would read as "newly believed" to `preview` and the feed.
  (doseq [n sizes]
    (let [tms (fan-of n)]
      (jtms/reset-touched! tms)
      (is (every? zero? (regions-touched #(justify tms 77777 [0] 1)))
          (str "a second witness for an already-believed conclusion relabelled at n=" n))
      (is (contains? (jtms/touched tms) 1)
          "the consequence is not in the window, so a stale report is served for it")
      (is (contains? (jtms/touched-in tms) 1)
          "and it reads as newly believed, which it is not"))))

(deftest adding-a-premise-touches-only-its-own-region
  (doseq [n sizes]
    (let [tms (fan-of n)]
      (is (= [1] (regions-touched #(premise tms 888888)))
          (str "region grew with the graph at n=" n)))))

(deftest retraction-touches-only-the-retracted-datums-closure
  ;; `retract!` relabels before it sweeps; both halves must stay scoped.
  (doseq [n sizes]
    (let [tms (fan-of n)]
      (let [touched (regions-touched #(jtms/retract! tms 0))]
        (is (every? #(<= % 2) touched)
            (str "retraction relabelled a region of " (pr-str touched) " at n=" n))))))

;; ---- depth: the region-local fixpoints are worklists, not round-robin ----
;;
;; The region fixpoints iterate to stability, so a
;; round-robin sweep re-scans the whole region each round and costs O(region depth ×
;; region) on a deep chain.  The worklist re-touches a node only when one of its inputs
;; moves, so the same unique least fixpoint costs O(region edges).  Correctness first,
;; then the work bound — counting evaluations, not wall-clock, keeps it a test.

(deftest deep-chain-belief-propagates-and-withdraws-through-depth
  (let [n 300, tms (chain-of n)]
    (testing "belief reaches the end of a deep chain"
      (is (every? #(jtms/in? tms %) (range (inc n)))))
    (testing "defeating the root withdraws the entire chain"
      (jtms/defeat tms [0])
      (is (not-any? #(jtms/in? tms %) (range (inc n)))))
    (testing "clearing the defeat revives all of it"
      (jtms/clear-defeats! tms)
      (is (every? #(jtms/in? tms %) (range (inc n)))))))

(deftest region-classes-relabels-a-deep-chain-in-linear-work
  ;; A :monotonic chain makes the class front actually advance through depth (a
  ;; round-robin sweep needs one round per node to propagate it, O(k²) node-class
  ;; evaluations).  Re-asserting the root premise forces ONE relabel of the whole
  ;; depth-k region; the worklist recomputes each node O(1) times.
  (let [n     400
        tms   (chain-of n :monotonic)
        calls (atom 0)
        orig  @#'jtms/node-class]
    (with-redefs [jtms/node-class (fn [& a] (swap! calls inc) (apply orig a))]
      (jtms/add-premise tms 0 :monotonic))   ; resettles 0's closure = the whole chain
    (testing "the deep relabel is correct — the class propagates to every node"
      (is (every? #(= :monotonic (jtms/defeat-class tms %)) (range (inc n)))))
    (testing "and it cost O(k), not O(k²), node-class evaluations"
      (is (< @calls (* 4 n))
          (str "node-class ran " @calls " times at depth " n
               "; a round-robin sweep would run ~" (* n n))))))

;; ---- sweep! semantics ---------------------------------------------------
;;
;; `sweep!` is `retract!`'s collector without the retraction, and `exceptWhen` makes
;; it a routine path rather than a retraction-only one.  Every existing test reaches
;; it through `retract!` or through a full `settle`, so its own contract is unpinned.

(deftest sweep-collects-the-whole-closure-of-its-seeds
  ;; The seeds are where the walk *starts*, not what it collects: a blocked
  ;; justification orphans its conclusion and everything resting on that.
  (let [tms (jtms/create-tms)]
    (premise tms 1)
    (justify tms 101 [1] 2)
    (justify tms 102 [2] 3)
    (justify tms 103 [3] 4)
    (jtms/set-blocked tms #{101})
    (is (not-any? #(jtms/in? tms %) [2 3 4]))
    (let [{:keys [removed-sentexes removed-justifications]} (jtms/sweep! tms [2])]
      (testing "seeding at 2 collects 3 and 4 as well — the consequence closure"
        (is (= #{2 3 4} (set removed-sentexes))))
      (testing "and the justifications that touched them go too"
        (is (= #{101 102 103} (set removed-justifications))))
      (testing "the premise is not swept — it is still asserted"
        (is (jtms/in? tms 1))
        (is (jtms/premise? tms 1))))))

(deftest sweep-keeps-a-datum-that-still-has-a-witness
  ;; Groundability, not belief: a second derivation means the datum is still
  ;; structurally derivable and must survive the collector.
  (let [tms (jtms/create-tms)]
    (premise tms 1)
    (premise tms 2)
    (justify tms 101 [1] 3)
    (justify tms 102 [2] 3)
    (jtms/set-blocked tms #{101})
    (let [{:keys [removed-sentexes]} (jtms/sweep! tms [3])]
      (is (empty? removed-sentexes) "3 is still derivable through 102")
      (is (jtms/in? tms 3)))))

(deftest sweep-prunes-the-blocked-set-of-justifications-it-removed
  ;; A blocked id outliving its justification is a leak that only shows up later,
  ;; when a new justification is allocated the same id and arrives pre-blocked.
  (let [tms (jtms/create-tms)]
    (premise tms 1)
    (justify tms 101 [1] 2)
    (jtms/set-blocked tms #{101})
    (is (= #{101} (jtms/blocked tms)))
    (jtms/sweep! tms [2])
    (is (empty? (jtms/blocked tms))
        "the swept justification's block went with it")))

(deftest sweep-does-not-report-a-premise-marker-as-a-removed-justification
  ;; A premise's own marker justification is bookkeeping, not a justification the caller
  ;; should be told to delete from its justification store.
  (let [tms (jtms/create-tms)]
    (premise tms 1)
    (justify tms 101 [1] 2)
    (jtms/set-blocked tms #{101})
    (let [{:keys [removed-justifications]} (jtms/sweep! tms [2])]
      (is (= [101] (vec removed-justifications)))
      (is (not-any? #(= :premise (:informant (jtms/justification tms %)))
                    removed-justifications)))))

(deftest sweeping-a-live-datum-removes-nothing
  (let [tms (jtms/create-tms)]
    (premise tms 1)
    (justify tms 101 [1] 2)
    (let [{:keys [removed-sentexes removed-justifications]} (jtms/sweep! tms [2])]
      (is (empty? removed-sentexes) "2 is groundable, so it stays")
      (is (empty? removed-justifications)))))

;; ---- ensure* keeps the SHALLOWEST depth --------------------------------

(deftest a-datum-keeps-the-shallowest-depth-it-was-ever-given
  ;; Depth bounds forward chaining (`:max-depth`), and a datum re-derived by a longer
  ;; route must not inherit the longer route's depth — otherwise re-deriving an
  ;; existing conclusion could push it past the truncation bound and drop it.
  (let [tms (jtms/create-tms)]
    (jtms/ensure-node tms 5 7)
    (is (= 7 (jtms/depth tms 5)))
    (jtms/ensure-node tms 5 3)
    (is (= 3 (jtms/depth tms 5)) "a shallower derivation lowers the recorded depth")
    (jtms/ensure-node tms 5 9)
    (is (= 3 (jtms/depth tms 5)) "a deeper one does not raise it back")))

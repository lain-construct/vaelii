;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.chaining-contracts-test
  "Two guards on the forward-chaining path that nothing exercised.

  `:max-derivations` is the backstop against a runaway chain that is *not* bounded
  by depth — a rule that derives ever more facts at the same depth walks straight
  past `:max-depth`.  Only the depth bound had a test, so the second `:truncated?`
  disjunct was unreachable from the suite.

  The `ist` placement guard is the other: a rule concluding `(ist Ctx S)` places `S`
  into the named context, and `Ctx` may be a variable the antecedents bind.  Nothing
  guarantees it binds to a *context*.  The guard yields no placements when it does
  not, and a `keep` swallows the nil — so removing it would place a conclusion into
  a bogus context that `context-up` never reaches: stored, believed, and invisible
  to every query."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- fwd [antes conseq]
  (list 'set/forwardRule (vr/rule-sentence antes conseq)))

;; ---- :max-derivations ---------------------------------------------------

(tu/deftest-kb default-chain-opts-publishes-both-bounds
  ;; A public def with no test reference.  If the opts merge ever dropped a key, the
  ;; chain loop would compare against nil and NPE, or against a default that never
  ;; fires — this is the only thing that would notice the shape changing.
  (is (= #{:max-depth :max-derivations} (set (keys v/default-chain-opts))))
  (is (pos-int? (:max-depth v/default-chain-opts)))
  (is (pos-int? (:max-derivations v/default-chain-opts))))

(tu/deftest-kb an-unbounded-run-is-not-flagged-truncated
  (tu/with-terms [thing marked A B C D E F]
    (v/assert kb (fwd [(list thing '?x)] (list marked '?x)) 'NaturalWorldContext)
    (doseq [i [A B C D E F]]
      (v/assert kb (list thing i) 'NaturalWorldContext {:chain? false}))
    (let [{:keys [derived truncated?]} (v/forward-chain kb {})]
      (is (>= derived 6) "one conclusion per fact")
      (is (not truncated?)))))

(tu/deftest-kb max-derivations-bounds-a-run-that-depth-alone-would-not
  ;; A transitive closure over a line graph: every `path` fact beyond the direct
  ;; edges is derived, and the full closure is far larger than the bound.  Depth
  ;; alone would not stop it at 2 derivations.
  ;;
  ;; The bound is checked *between* agenda datums, not inside one firing, so a single
  ;; datum's fan-out can overshoot it — `:max-derivations` is a backstop against a
  ;; runaway run, not a precise quota.  Asserting well below the unbounded total is
  ;; what pins it without over-claiming.
  (tu/with-terms [edge path A B C D E GraphContext]
    (v/assert kb (list 'genlContext GraphContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (fwd [(list edge '?x '?y)] (list path '?x '?y)) GraphContext)
    (v/assert kb (fwd [(list edge '?x '?y) (list path '?y '?z)]
                      (list path '?x '?z)) GraphContext)
    (doseq [[a b] [[A B] [B C] [C D] [D E]]]
      (v/assert kb (list edge a b) GraphContext {:chain? false}))
    (let [{:keys [derived truncated?]} (v/forward-chain kb {:max-derivations 2})]
      (is truncated? "the run hit the derivation backstop")
      (is (< derived 10)
          "the full closure over a 4-edge line is 10 paths; the bound stopped it short"))))

(tu/deftest-kb max-depth-still-bounds-a-deepening-chain
  ;; The other disjunct, for contrast: depth grows, so the depth bound fires.
  (tu/with-terms [edge path A B C D GraphContext]
    (v/assert kb (list 'genlContext GraphContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (fwd [(list edge '?x '?y)] (list path '?x '?y)) GraphContext)
    (v/assert kb (fwd [(list edge '?x '?y) (list path '?y '?z)]
                      (list path '?x '?z)) GraphContext)
    (doseq [[a b] [[A B] [B C] [C D]]]
      (v/assert kb (list edge a b) GraphContext {:chain? false}))
    (let [{:keys [truncated?]} (v/forward-chain kb {:max-depth 1})]
      (is truncated? "a depth-1 bound cannot reach the two-hop path"))))

;; ---- :on-progress -------------------------------------------------------
;;
;; The fixpoint is the one phase of a bulk load that can run for minutes, so it reports
;; where it is and takes a throw as an abort.  Reporting is paced by wall-clock, which a
;; test cannot wait out honestly — a run big enough to take seconds is a slow test, and one
;; small enough to be quick reports once.  So the interval itself is a knob
;; (`:progress-every-ms 0`, report at every opportunity) and the runs stay small: a line
;; graph's transitive closure is quadratic in its edges, so 40 of them is hundreds of
;; agenda datums for four asserts of setup.

(defn- line-graph!
  "A `path`-closure rule set over a line of `n` edges, asserted without chaining.  Returns
  `[edge path context]`."
  [kb n]
  (let [edge (tu/tmp-pred "edge"), path (tu/tmp-pred "path"), ctx (tu/tmp-ctx "Graph")
        nodes (vec (repeatedly (inc n) #(tu/tmp-ind "N")))]
    (v/assert kb (list 'genlContext ctx 'UniverseContext) 'UniverseContext)
    (v/assert kb (fwd [(list edge '?x '?y)] (list path '?x '?y)) ctx {:chain? false})
    (v/assert kb (fwd [(list edge '?x '?y) (list path '?y '?z)] (list path '?x '?z))
              ctx {:chain? false})
    (doseq [[a b] (partition 2 1 nodes)]
      (v/assert kb (list edge a b) ctx {:chain? false}))
    [edge path ctx]))

(tu/deftest-kb a-long-run-reports-where-it-has-got-to
  (line-graph! kb 40)
  (let [seen (atom [])
        {:keys [derived]} (v/forward-chain kb {:progress-every-ms 0
                                               :on-progress #(swap! seen conj %)})]
    (is (> (count @seen) 1)
        "a run of hundreds of datums reports more than once — a bar that never moves is
         the thing this exists to stop")
    (is (= (map :derived @seen) (sort (map :derived @seen)))
        "the derived count only ever grows")
    (is (every? #(and (nat-int? (:derived %)) (nat-int? (:pending %))) @seen))
    (is (= derived (:derived (last @seen)))
        "the last report agrees with what the run returns")
    (is (zero? (:pending (last @seen)))
        "a fixpoint ends with an empty agenda")))

(tu/deftest-kb a-throwing-progress-callback-aborts-the-run
  ;; How a loader cancels: there is no other point at which stopping a fixpoint is safe.
  ;; What had been derived stays — conclusions are placed as they are made — so the KB is
  ;; a prefix of the run, which is what `unload!` then takes down.
  (let [[_ path _] (line-graph! kb 40)
        closure    (/ (* 40 41) 2)]                  ; every ordered pair along the line
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"stop here"
                          (v/forward-chain kb {:progress-every-ms 0
                                               :on-progress (fn [_] (throw (ex-info "stop here" {})))})))
    (is (< (v/count-with-functor kb path) closure)
        "the abort landed before the closure was complete")
    (v/forward-chain kb {})
    (is (= closure (v/count-with-functor kb path))
        "and a run from what it had placed reaches the same fixpoint")))

;; ---- the ist placement guard -------------------------------------------

(tu/deftest-kb an-ist-consequent-places-into-a-bound-context-variable
  ;; The covered half, restated here so the guard test below has its complement.
  (tu/with-terms [holdsIn interesting Widget AlphaContext]
    (v/assert kb (list 'genlContext AlphaContext 'UniverseContext) 'UniverseContext)
    (v/assert kb (fwd [(list holdsIn '?c '?x)] (list 'ist '?c (list interesting '?x)))
              'UniverseContext)
    (v/assert kb (list holdsIn AlphaContext Widget) 'UniverseContext)
    (is (seq (v/sentexes-matching kb (list interesting Widget) AlphaContext))
        "the conclusion landed in the context the variable bound to")))

(tu/deftest-kb an-ist-consequent-binding-a-non-context-places-nothing
  ;; `?c` binds to an individual, not a context.  The conclusion must be dropped —
  ;; not placed into a made-up "context" that nothing can see.
  (tu/with-terms [holdsIn interesting Widget NotACtx]
    (v/assert kb (fwd [(list holdsIn '?c '?x)] (list 'ist '?c (list interesting '?x)))
              'UniverseContext)
    (let [contexts-before (set (v/contexts kb))]
      (v/assert kb (list holdsIn NotACtx Widget) 'UniverseContext)
      (testing "nothing was placed"
        ;; `contexts-of` asks where this *sentence* is asserted; `find-sentexes` would
        ;; also match the rule, which mentions the predicate in its consequent.
        (is (empty? (v/contexts-of kb (list interesting Widget)))
            "no conclusion should exist in any context"))
      (testing "and no bogus context was invented"
        (is (= contexts-before (set (v/contexts kb))))
        (is (not (contains? (set (v/contexts kb)) NotACtx)))))))

;; ---- the opts roster ------------------------------------------------------

(tu/deftest-kb a-forward-chain-option-nothing-reads-is-refused
  ;; Every key `forward-chain` takes is a bound or the window into one, so the
  ;; silent-default failure is a run with no ceiling: `{:max-derivation n}` reads as no
  ;; key at all and the fixpoint runs unbounded — the exact run the option was written
  ;; to prevent.  Wire-reachable, too: the daemon's `:forward-chain` op passes its args
  ;; straight through.
  (testing "the singular typo is refused, naming the plural it meant"
    (let [e (is (thrown? clojure.lang.ExceptionInfo
                         (v/forward-chain kb {:max-derivation 5})))]
      (is (= :unknown-option (:type (ex-data e))))
      (is (= [:max-derivation] (:unknown (ex-data e))))
      (is (re-find #":max-derivations" (ex-message e))
          "the message lists what forward-chain does read")))
  (testing "a non-map opts is refused rather than read as no bounds"
    ;; The keyword is the point — the refusal is what this asserts — so the
    ;; type mismatch clj-kondo sees is the test's subject, not a defect.
    #_{:clj-kondo/ignore [:type-mismatch]}
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"must be a map"
                          (v/forward-chain kb :max-derivations))))
  (testing "the rostered keys still run"
    (let [r (v/forward-chain kb {:max-depth 2 :max-derivations 10
                                 :progress-every-ms 1000 :on-progress (fn [_])})]
      (is (contains? r :derived)))))

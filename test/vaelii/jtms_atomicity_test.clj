;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.jtms-atomicity-test
  "The TMS mutation contract: retracting an
  unknown datum no-ops instead of materializing a phantom node and fabricating a
  removal count, retraction is idempotent, and every mutation applies atomically —
  a concurrent `swap!` composes with `retract!`/`sweep!` rather than being lost to
  a deref-then-`reset!` window."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.jtms :as jtms]
            [vaelii.test-util :as tu]))

;; ---- unknown datums (pure, no KB) ---------------------------------------

(deftest retract-unknown-datum-no-ops
  (let [tms (jtms/create-tms)]
    (jtms/add-premise tms 1 :monotonic)
    (let [before @tms
          result (jtms/retract! tms 999999)]
      (is (= {:removed-sentexes [] :removed-justifications []} result)
          "an unknown datum must not claim a removal")
      (is (= before @tms)
          "an unknown datum must not materialize a node"))))

(deftest retract-is-idempotent
  (let [tms (jtms/create-tms)]
    (jtms/add-premise tms 1 :default)
    (is (= [1] (:removed-sentexes (jtms/retract! tms 1))))
    (let [after  @tms
          again  (jtms/retract! tms 1)]
      (is (= {:removed-sentexes [] :removed-justifications []} again))
      (is (= after @tms) "a second retraction must change nothing"))))

;; ---- atomicity under concurrent writers ---------------------------------
;;
;; The nodes in each test are deliberately unlinked, so every operation's region
;; is a singleton and the writers interleave as densely as the scheduler allows.
;; Under the old deref-then-reset! shape these tests lose updates; under
;; compare-and-set they cannot.

(deftest concurrent-retractions-all-land
  (let [tms (jtms/create-tms)
        n   400]
    (doseq [d (range n)] (jtms/add-premise tms d :default))
    (let [evens (future (doseq [d (range 0 n 2)] (jtms/retract! tms d)))
          odds  (future (doseq [d (range 1 n 2)] (jtms/retract! tms d)))]
      @evens @odds)
    (is (empty? (:nodes @tms))
        "every concurrent retraction must land — a lost update leaves a node behind")))

(deftest retraction-composes-with-swap-based-mutation
  (let [tms  (jtms/create-tms)
        n    200
        park (range n (+ n 50))]                      ; disjoint from the retracted range
    (doseq [d (range (+ n 50))] (jtms/add-premise tms d :default))
    (let [retracting (future (doseq [d (range n)] (jtms/retract! tms d)))
          defeating  (future (dotimes [_ 25]
                               (jtms/defeat tms park)
                               (jtms/clear-defeats! tms)))]
      @retracting @defeating)
    (testing "every retraction survived the concurrent swap!s"
      (is (not-any? #(get-in @tms [:nodes %]) (range n))))
    (testing "and the swap!-based writer's final state survived the retractions"
      (is (every? #(jtms/in? tms %) park)))))

;; ---- the public API contract --------------------------------------------

(deftest kb-retract-of-unknown-handle-counts-zero
  (tu/with-neutral-kb [kb tu/fresh]
    (is (= {:removed-sentexes 0 :removed-justifications 0}
           (v/retract! kb 999999)))
    (is (not-any? #{999999} (jtms/datums (:tms kb)))
        "the phantom node must not survive into the TMS")))

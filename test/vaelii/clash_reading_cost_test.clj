;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.clash-reading-cost-test
  "What a reading of the standing clashes costs, as a count: a clash's membership lookup
  builds no supertype closure.  An exact integer rather than a duration, for
  `assert_cost_test`'s reason — a call count is a property of the algorithm where a
  millisecond is a property of the box."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]))

(defn- types! [kb & ts]
  (doseq [t ts] (v/assert kb (list 'genl t 'thing) 'CxUniverse)))

;; ---- the membership lookup builds no closure ----------------------

(defn- lookup-closure-reads
  "`[lookups closure-reads]` while `f` runs: `checks/membership-handles-led` calls, and the
  `tax/genls` / `tax/genls-global` calls made inside one."
  [f]
  (let [lookups (atom 0)
        reads   (atom 0)
        inside  (atom false)
        led     @#'checks/membership-handles-led
        counted (fn [orig] (fn [& args] (when @inside (swap! reads inc)) (apply orig args)))]
    (with-redefs-fn {#'checks/membership-handles-led
                     (fn [& args]
                       (swap! lookups inc)
                       (reset! inside true)
                       (try (apply led args) (finally (reset! inside false))))
                     #'tax/genls        (counted tax/genls)
                     #'tax/genls-global (counted tax/genls-global)}
      (fn [] (f)))
    [@lookups @reads]))

(deftest a-clash-s-membership-lookup-reads-no-supertype-closure
  ;; `checks/membership-handles` names the `(t x)` sentex a clash is with by testing every
  ;; type `x` holds against `t`, including types no clash is about.  A closure read there
  ;; builds the supertype closure of each, which on a large taxonomy is most of a settle;
  ;; `crc_deep` sits under a chain so its closure is one a read would build.
  (tu/with-neutral-kb [kb #(tu/fresh)]
    (tu/with-terms [crc_a crc_b crc_deep crc_mid crc_top CrcX]
      (types! kb crc_a crc_b crc_top)
      (v/assert kb (list 'genl crc_mid crc_top) 'CxUniverse)
      (v/assert kb (list 'genl crc_deep crc_mid) 'CxUniverse)
      (v/assert kb (list 'disjoint crc_a crc_b) 'CxUniverse {:strength :monotonic})
      (v/assert kb (list crc_deep CrcX) 'CxUniverse {})
      (v/assert kb (list crc_a CrcX) 'CxUniverse {})
      (doseq [lead [:auto :agnostic]]
        (testing (str "leading " lead)
          (binding [res/*lead-side* lead]
            (let [h                (atom nil)
                  [lookups reads]  (lookup-closure-reads
                                    #(reset! h (v/assert kb (list crc_b CrcX) 'CxUniverse {})))]
              (is (pos? lookups) "the clash looked its members up, or the count measures nothing")
              (is (zero? reads))
              (is (= 1 (count (v/contradictions kb))))
              (v/retract! kb @h))))))))

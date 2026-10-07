;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.input-output-timing-test
  "When an input and an output exist, against their event.

  CxChange's four timing rules conclude point relations over `(StartFn X)` and `(EndFn X)`:
  an output starts within its event, a destroyed input ends within it, an input starts by
  its end, and a preserved input ends after it.  The point network reads those
  conclusions, so with `:point` registered a contradicting stated order is a
  `:qualitative-inconsistency`, and with `:includes-instant` registered `argue` answers
  whether a thing exists at a moment.  Each test states its facts in its own context
  below CxChange, so one test's network cannot reach another's.

  An event is half-open, as a calendar term is: `(EndFn E)` is the first moment after E."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded (fn [kb] (-> kb tu/load-starter! (v/add-reasoner :point :includes-instant)))))
(use-fixtures :each (tu/neutral))

(defn- story!
  "A fresh context below CxChange, holding `facts`."
  [kb facts]
  (let [ctx (tu/tmp-ctx "Story")]
    (v/assert kb (list 'genlCx ctx 'CxChange) 'CxChange)
    (run! #(v/assert kb % ctx) facts)
    ctx))

(defn- consistent? [kb ctx] (:consistent? (v/qualitative-network kb :point ctx)))

(defn- exists-at [kb ctx thing instant]
  (:verdict (v/argue kb (list 'includesInstant thing instant) ctx {})))

(def ^:private noon '(InstantFn 2026 6 1 12 0 0))
(def ^:private one-pm '(InstantFn 2026 6 1 13 0 0))
(def ^:private noon-next-year '(InstantFn 2027 6 1 12 0 0))

(tu/deftest-kb a-preserved-input-exists-when-its-event-ends
  ;; Make a salad: the lettuce exists the moment the making ends, and an hour later the
  ;; KB does not know.
  (tu/with-terms [Salading1 Lettuce1]
    (let [ctx (story! kb [(list 'event Salading1)
                          (list 'preservedInput Salading1 Lettuce1)
                          (list 'instantEqual (list 'EndFn Salading1) noon)])]
      (is (consistent? kb ctx))
      (is (= :true (exists-at kb ctx Lettuce1 noon)))
      (is (= :unknown (exists-at kb ctx Lettuce1 one-pm))))))

(tu/deftest-kb a-destroyed-input-does-not-exist-after-its-event
  ;; Smash a pot: the pot does not exist the moment the smashing ends, nor a year later.
  (tu/with-terms [Smashing1 Pot1]
    (let [ctx (story! kb [(list 'event Smashing1)
                          (list 'destroyedInput Smashing1 Pot1)
                          (list 'instantEqual (list 'EndFn Smashing1) noon)])]
      (is (consistent? kb ctx))
      (is (= :false (exists-at kb ctx Pot1 noon)))
      (is (= :false (exists-at kb ctx Pot1 noon-next-year))))))

(tu/deftest-kb an-output-starts-within-its-event
  (tu/with-terms [Carving1 Statue1 Stamping1 Widget1]
    (testing "an output that started before its event is an inconsistency"
      (let [ctx (story! kb [(list 'event Carving1)
                            (list 'instantBefore (list 'StartFn Statue1) (list 'StartFn Carving1))
                            (list 'output Carving1 Statue1)])]
        (is (false? (consistent? kb ctx)))))
    (testing "and one that starts exactly as its event ends is not"
      (let [ctx (story! kb [(list 'event Stamping1)
                            (list 'instantEqual (list 'StartFn Widget1) (list 'EndFn Stamping1))
                            (list 'output Stamping1 Widget1)])]
        (is (true? (consistent? kb ctx)))))))

(tu/deftest-kb a-destroyed-input-ends-within-its-event
  (tu/with-terms [Smelting1 Ore1]
    (let [ctx (story! kb [(list 'event Smelting1)
                          (list 'instantAfter (list 'EndFn Ore1) (list 'EndFn Smelting1))
                          (list 'destroyedInput Smelting1 Ore1)])]
      (is (false? (consistent? kb ctx))
          "ore that outlasted its smelting was not destroyed in it"))))

(tu/deftest-kb an-input-starts-by-the-time-its-event-ends
  (tu/with-terms [Tossing1 Lettuce1 Sawing1 Plank1]
    (testing "lettuce there before the salad and still there after is consistent"
      (let [ctx (story! kb [(list 'event Tossing1)
                            (list 'instantBefore (list 'StartFn Lettuce1) (list 'StartFn Tossing1))
                            (list 'instantAfter (list 'EndFn Lettuce1) (list 'EndFn Tossing1))
                            (list 'input Tossing1 Lettuce1)])]
        (is (true? (consistent? kb ctx)))))
    (testing "but an input that started after its event ended is an inconsistency"
      (let [ctx (story! kb [(list 'event Sawing1)
                            (list 'instantAfter (list 'StartFn Plank1) (list 'EndFn Sawing1))
                            (list 'input Sawing1 Plank1)])]
        (is (false? (consistent? kb ctx)))))))

(tu/deftest-kb a-preserved-input-that-ended-with-its-event-is-an-inconsistency
  (tu/with-terms [Salading1 Lettuce1]
    (let [ctx (story! kb [(list 'event Salading1)
                          (list 'instantEqual (list 'EndFn Lettuce1) (list 'EndFn Salading1))
                          (list 'preservedInput Salading1 Lettuce1)])]
      (is (false? (consistent? kb ctx))))))

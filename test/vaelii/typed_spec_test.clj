;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.typed-spec-test
  "typedSpec: a genl spec whose declared argument types are tighter than its genl's.
  `(typedSpec G S)` concludes `(genl S G)` and lifts nothing, and the `kb-integrity`
  `:under-specific` pass reports each stated `G` sentence whose arguments meet every
  argument constraint of `S`, which should have been stated as an `S` sentence
  (docs/integrity.md)."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.naming :as nm]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (tu/load-core!))))

(def ^:private U 'CxUniverse)

(defn- assert-all! [kb sentences]
  (doseq [s sentences] (v/assert kb s U)))

(defn- declare-pair!
  "Declare `linked` over thing × thing, `wired` over `gadget` × `socket`, and
  `(typedSpec linked wired)`."
  [kb linked wired gadget socket]
  (assert-all! kb [(list 'unary_predicate gadget) (list 'genl gadget 'thing)
                   (list 'unary_predicate socket) (list 'genl socket 'thing)
                   (list 'binary_predicate linked)
                   (list 'arg linked 1 'thing) (list 'arg linked 2 'thing)
                   (list 'binary_predicate wired)
                   (list 'arg wired 1 gadget) (list 'arg wired 2 socket)
                   (list 'typedSpec linked wired)]))

(defn- under-specific
  "The `:under-specific` findings of a sweep run with that category alone."
  ([kb] (under-specific kb {}))
  ([kb opts]
   (:under-specific (v/kb-integrity kb #{} U (assoc opts :categories #{:under-specific})))))

(defn- shown
  "Each finding as `[stated-sentence spec suggested-sentence]`."
  [findings]
  (mapv (fn [f] [(:sentence (:stated f)) (:spec f) (:suggest f)]) findings))

(tu/deftest-kb a-typed-spec-concludes-its-genl-and-lifts-nothing
  (tu/with-terms [linkedWith wiredTo gadget_kind socket_kind Zibbo Plonk]
    (declare-pair! kb linkedWith wiredTo gadget_kind socket_kind)
    (is (true? (v/genl? kb wiredTo linkedWith U)) "(genl wiredTo linkedWith) is believed")
    (let [edge (first (v/sentexes-matching kb (list 'genl wiredTo linkedWith) U))]
      (is (some? edge))
      (is (and edge (not (v/premise? kb (:id edge))))
          "the edge is concluded from the typedSpec, not stated"))
    (assert-all! kb [(list gadget_kind Zibbo) (list socket_kind Plonk)
                     (list linkedWith Zibbo Plonk)])
    (is (not (v/ask? kb (list wiredTo Zibbo Plonk) U))
        "no rule lifts a genl sentence to its typed spec")
    (is (empty? (v/sentexes-matching kb (list wiredTo '?x '?y) U)))))

(tu/deftest-kb a-stated-genl-sentence-meeting-every-spec-constraint-is-reported
  (tu/with-terms [linkedWith wiredTo gadget_kind socket_kind Zibbo Plonk]
    (declare-pair! kb linkedWith wiredTo gadget_kind socket_kind)
    (assert-all! kb [(list gadget_kind Zibbo) (list socket_kind Plonk)])
    (let [h      (v/assert kb (list linkedWith Zibbo Plonk) U)
          before (tu/sentex-ids kb)
          report (v/kb-integrity kb #{} U {:categories #{:under-specific}})]
      (is (= :gap (:status report)))
      (is (= [[(list linkedWith Zibbo Plonk) wiredTo (list wiredTo Zibbo Plonk)]]
             (shown (:under-specific report)))
          "one finding naming the stated sentence and the spec it should have used")
      (is (= {:handle h :context U}
             (select-keys (:stated (first (:under-specific report))) [:handle :context])))
      (is (= before (tu/sentex-ids kb)) "the audit stores nothing"))))

(tu/deftest-kb a-stated-genl-sentence-missing-a-spec-constraint-is-not-reported
  (tu/with-terms [linkedWith wiredTo gadget_kind socket_kind Zibbo Quarry]
    (declare-pair! kb linkedWith wiredTo gadget_kind socket_kind)
    (assert-all! kb [(list gadget_kind Zibbo) (list linkedWith Zibbo Quarry)])
    (is (empty? (under-specific kb))
        "Quarry is not proven a socket_kind, so wiredTo would not have fit")))

(tu/deftest-kb a-derived-genl-sentence-is-not-reported
  (tu/with-terms [linkedWith wiredTo feedsInto gadget_kind socket_kind Zibbo Plonk]
    (declare-pair! kb linkedWith wiredTo gadget_kind socket_kind)
    (assert-all! kb [(list 'binary_predicate feedsInto)
                     (list 'arg feedsInto 1 'thing) (list 'arg feedsInto 2 'thing)
                     (list 'set/forwardRule (list 'implies (list feedsInto '?x '?y)
                                                  (list linkedWith '?x '?y)))
                     (list gadget_kind Zibbo) (list socket_kind Plonk)
                     (list feedsInto Zibbo Plonk)])
    (is (v/ask? kb (list linkedWith Zibbo Plonk) U) "the rule derives the genl sentence")
    (is (empty? (under-specific kb)) "a sentence no one stated is not under-specific")))

(tu/deftest-kb a-constraint-the-spec-inherits-is-read
  (tu/with-terms [linkedWith pluggedTo wiredTo gadget_kind socket_kind Zibbo Plonk Quarry]
    ;; wiredTo declares position 1 only, and inherits socket_kind at 2 from pluggedTo.
    (assert-all! kb [(list 'unary_predicate gadget_kind) (list 'genl gadget_kind 'thing)
                     (list 'unary_predicate socket_kind) (list 'genl socket_kind 'thing)
                     (list 'binary_predicate linkedWith)
                     (list 'arg linkedWith 1 'thing) (list 'arg linkedWith 2 'thing)
                     (list 'binary_predicate pluggedTo)
                     (list 'arg pluggedTo 2 socket_kind)
                     (list 'genl pluggedTo linkedWith)
                     (list 'binary_predicate wiredTo)
                     (list 'arg wiredTo 1 gadget_kind)
                     (list 'genl wiredTo pluggedTo)
                     (list 'typedSpec linkedWith wiredTo)
                     (list gadget_kind Zibbo) (list socket_kind Plonk)
                     (list linkedWith Zibbo Quarry) (list linkedWith Zibbo Plonk)])
    (is (= [[(list linkedWith Zibbo Plonk) wiredTo (list wiredTo Zibbo Plonk)]]
           (shown (under-specific kb)))
        "Quarry fails the inherited socket_kind constraint; Plonk meets it")))

(tu/deftest-kb under-specific-findings-respect-context-visibility
  (tu/with-terms [CxHidden linkedWith wiredTo gadget_kind socket_kind Zibbo Plonk]
    (v/assert kb (list 'genlCx CxHidden U) U)
    (declare-pair! kb linkedWith wiredTo gadget_kind socket_kind)
    (assert-all! kb [(list gadget_kind Zibbo) (list socket_kind Plonk)])
    (v/assert kb (list linkedWith Zibbo Plonk) CxHidden)
    (is (empty? (under-specific kb)) "a sentence below the audit context is not seen")
    (is (= 1 (count (:under-specific (v/kb-integrity kb #{} CxHidden
                                                     {:categories #{:under-specific}})))))))

(tu/deftest-kb under-specific-findings-truncate-under-every-bound
  (tu/with-terms [linkedWith wiredTo gadget_kind socket_kind Zibbo Plonk Quarry]
    (declare-pair! kb linkedWith wiredTo gadget_kind socket_kind)
    (assert-all! kb [(list gadget_kind Zibbo) (list socket_kind Plonk) (list socket_kind Quarry)
                     (list linkedWith Zibbo Plonk) (list linkedWith Zibbo Quarry)])
    (let [in-order (shown (under-specific kb))]
      (is (= 2 (count in-order)))
      (is (= in-order (sort-by first nm/compare-form in-order)) "in content order")
      (testing "a result cap below the finding count keeps the completed prefix"
        (let [report (v/kb-integrity kb #{} U {:categories #{:under-specific} :max-results 1})]
          (is (= [:truncated :max-results] ((juxt :status :reason) report)))
          (is (= (subvec in-order 0 1) (shown (:under-specific report))))))
      (testing "work exhaustion is truncated, never audited"
        (let [run    #(v/kb-integrity kb #{} U {:categories #{:under-specific} :max-work %})
              needed (first (filter #(= :gap (:status (run %))) (range 0 5000)))]
          (is (some? needed))
          (is (every? #(= [:truncated :max-work] ((juxt :status :reason) (run %)))
                      (range 0 (or needed 0)))))))))

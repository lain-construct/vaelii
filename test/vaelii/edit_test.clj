;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.edit-test
  "`edit` — a batched add-then-remove that settles once.  The point is efficiency and
  a stable belief state: adds land before removes, so a conclusion the removed premise
  solely-supported but an added one re-derives keeps a witness through the
  dependency-directed sweep — it is never swept and rebuilt, and never flickers OUT and
  back.  The final state equals running the asserts and retracts singly.

  And it is **all-or-nothing**: an engine refusal `check-edit` cannot predict — one that
  only bites because an earlier entry in the same batch landed first — is raised on the
  entry that trips it, and the batch is then taken back at the handles it wrote."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(deftest edit-adds-before-removing-so-a-rederivable-conclusion-survives
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [a b c X CxThe]
      ;; two rules concluding the same thing, from different premises
      (v/assert-rule kb [(list a '?x)] (list c '?x) CxThe)
      (v/assert-rule kb [(list b '?x)] (list c '?x) CxThe)
      (let [fa (v/assert kb (list a X) CxThe)
            ch (v/handle-of kb (list c X) CxThe)]
        (is (v/in? kb ch) "(c X) is derived from (a X)")
        (let [result (v/edit! kb {:add [[(list b X) CxThe]] :remove [fa]})]
          (testing "the return reports the add and the teardown"
            (is (= 1 (count (:added result))))
            (is (pos? (:removed-sentexes (:removed result)))))
          (testing "the removed premise is gone and the added one is believed"
            (is (nil? (v/handle-of kb (list a X) CxThe)))
            (is (v/in? kb (v/handle-of kb (list b X) CxThe))))
          (testing "(c X) survived on the new support — same handle, still IN"
            (is (v/in? kb ch))
            (is (contains?
                 (->> (v/supporting-justifications kb ch)
                      (mapcat :antecedents) set)
                 (v/handle-of kb (list b X) CxThe))
                "its live support now names the added premise")))))))

(deftest edit-matches-separate-assert-and-retract
  ;; Run the same scenario two ways on two *sequential* fresh KBs (nesting two
  ;; `tu/fresh` would collide — both take the scratch db pair), then compare belief.
  (tu/with-terms [a b c X CxThe]
    (letfn [(scenario [kb via-edit?]
              (v/assert-rule kb [(list a '?x)] (list c '?x) CxThe)
              (v/assert-rule kb [(list b '?x)] (list c '?x) CxThe)
              (let [fa (v/assert kb (list a X) CxThe)]
                (if via-edit?
                  (v/edit! kb {:add [[(list b X) CxThe]] :remove [fa]})
                  (do (v/assert kb (list b X) CxThe)   ; add...
                      (v/retract! kb fa))))               ; ...then remove
              (into {} (for [s [(list a X) (list b X) (list c X)]]
                         [s (let [h (v/handle-of kb s CxThe)] (boolean (and h (v/in? kb h))))])))]
      (let [via-edit (tu/with-neutral-kb [kb tu/fresh] (scenario kb true))
            via-sep  (tu/with-neutral-kb [kb tu/fresh] (scenario kb false))]
        (is (= via-edit via-sep)
            "edit reaches the same belief as add-then-retract done singly")
        (is (get via-edit (list c X)) "(c X) is believed either way")))))

(deftest edit-degenerate-only-adds-or-only-removes
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [p q X CxThe]
      (testing "only adds behaves like assert-many"
        (let [r (v/edit! kb {:add [[(list p X) CxThe] [(list q X) CxThe]]})]
          (is (= 2 (count (:added r))))
          (is (= {:removed-sentexes 0 :removed-justifications 0} (:removed r)))
          (is (v/in? kb (v/handle-of kb (list p X) CxThe)))
          (is (v/in? kb (v/handle-of kb (list q X) CxThe)))))
      (testing "only removes behaves like retract"
        (let [ph (v/handle-of kb (list p X) CxThe)
              r  (v/edit! kb {:remove [ph]})]
          (is (empty? (:added r)))
          (is (pos? (:removed-sentexes (:removed r))))
          (is (nil? (v/handle-of kb (list p X) CxThe)))
          (is (v/in? kb (v/handle-of kb (list q X) CxThe)) "the untouched premise stays"))))))

;; ---- the door refuses what the dry run reports ---------------------------

(deftest a-malformed-add-entry-is-refused-whole-not-applied-in-part
  ;; One fn (`add-entry-shape-problem`) is read by both doors, so what `check-edit`
  ;; reports as `:shape` is what `edit` throws — a 4-element entry is never applied
  ;; with the junk silently dropped.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Muffet CxShape]
      (testing "a 4-element entry is :shape at both doors, and nothing lands"
        (let [batch  {:add [[(list dog Muffet) CxShape {} :junk]]}
              before (v/sentex-count kb)]
          (is (= [:shape] (mapv :type (v/check-edit kb batch))))
          (let [e (is (thrown? clojure.lang.ExceptionInfo (v/edit! kb batch)))]
            (is (= :shape (:type (ex-data e)))))
          (is (= before (v/sentex-count kb)))
          (is (nil? (v/handle-of kb (list dog Muffet) CxShape))
              "the entry was refused whole, not applied minus the junk")))
      (testing "a non-sequential entry is :shape at both doors, not a bare throw"
        (doseq [bad [42 {:sentence 1}]]
          (let [batch {:add [bad]}]
            (is (= [:shape] (mapv :type (v/check-edit kb batch))))
            (let [e (is (thrown? clojure.lang.ExceptionInfo (v/edit! kb batch)))]
              (is (= :shape (:type (ex-data e)))))))))))

(deftest a-batch-half-that-is-not-a-sequence-is-shape-at-every-door
  ;; `{:add 5}` reaches every door's iteration, so unrefused it raises a bare
  ;; "Don't know how to create ISeq" out of `check-edit`, `edit` and `preview` alike —
  ;; over the daemon, a 500 with no `:type` to discriminate on.
  (tu/with-neutral-kb [kb tu/fresh]
    (doseq [batch [{:add 5} {:remove 5} {:add {:a 1}} {:remove #{7}}]]
      (testing (pr-str batch)
        (is (= [:shape] (mapv :type (v/check-edit kb batch))))
        (doseq [[nm door] [["edit" #(v/edit! kb batch)]
                           ["preview" #(v/preview kb batch)]]]
          (let [e (is (thrown? clojure.lang.ExceptionInfo (door))
                      (str nm " refuses " (pr-str batch)))]
            (is (= :shape (:type (ex-data e))) (str nm " says :shape"))))))))

(deftest an-unknown-remove-handle-refuses-the-batch-before-anything-lands
  ;; `check-edit` flags the handle as `:unknown-handle`; a door that then quietly
  ;; folded it into zero counts would apply the adds first and leave a half-applied
  ;; batch behind a refusal the dry run had already named.  `retract!` standalone is
  ;; the deliberate contrast: retracting one absent handle is an ordinary zero-count
  ;; answer, not a batch.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Muffet CxHalf]
      (let [ghost 9999999
            batch {:add [[(list dog Muffet) CxHalf]] :remove [ghost]}]
        (is (nil? (v/sentex kb ghost)) "the handle names nothing stored")
        (testing "check-edit predicts the refusal"
          (is (some #(= :unknown-handle (:type %)) (v/check-edit kb batch))))
        (testing "edit refuses the whole batch with the same :type"
          (let [e (is (thrown? clojure.lang.ExceptionInfo (v/edit! kb batch)))]
            (is (= :unknown-handle (:type (ex-data e))))
            (is (= ghost (:handle (ex-data e))))))
        (testing "and the add half did not land — no half-applied batch"
          (is (nil? (v/handle-of kb (list dog Muffet) CxHalf))))
        (testing "retract! standalone keeps its zero-count answer"
          (is (= {:removed-sentexes 0 :removed-justifications 0}
                 (v/retract! kb ghost))))
        (testing "and a nil :remove entry stays nothing-to-remove"
          (is (= 0 (:removed-sentexes (:removed (v/edit! kb {:remove [nil]}))))))))))

;;; ── all-or-nothing ──────────────────────────────────────────────────────

(deftest a-refusal-check-edit-cannot-see-takes-the-whole-batch-back
  ;; The dry run checks each entry against the KB **as it stands**, so a batch whose
  ;; third entry clashes with its *first* is admissible to `check-edit` and refused by
  ;; the engine two entries in.  That is the case a rollback exists for.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog cat Muffet Whiskers Rex CxThe]
      (v/assert kb (list 'genlCx CxThe 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
      (let [sentences [(list dog Muffet) (list cat Whiskers)
                       (list cat Muffet) (list dog Rex)]
            batch     {:add (mapv #(vector % CxThe) sentences)}
            before    {:count      (v/sentex-count kb)
                       :sentexes   (tu/sentex-ids kb)
                       :premises   (tu/premise-ids kb)
                       :justifs    (tu/justification-ids kb)
                       :contras    (v/contradictions kb)}]
        (testing "the dry run predicts nothing: every entry is fine on its own"
          (is (= [] (v/check-edit kb batch))))
        (let [e (is (thrown? clojure.lang.ExceptionInfo (v/edit! kb batch)))
              d (ex-data e)]
          (testing "the engine's own refusal comes back, saying where and that it was undone"
            (is (= :disjoint (:type d)) "the original ex-data is kept")
            (is (true? (:rolled-back d)))
            (is (= :add (:in d)))
            (is (= 2 (:index d)))
            (is (= (nth (:add batch) 2) (:entry d)))
            (is (some? (ex-cause e)) "with the original hung off it as the cause")))
        (testing "and the KB is exactly what it was — count, roster, belief, dilemmas"
          (is (= (:count before) (v/sentex-count kb)))
          (is (= (:sentexes before) (tu/sentex-ids kb)))
          (is (= (:premises before) (tu/premise-ids kb)))
          (is (= (:justifs before) (tu/justification-ids kb)))
          (is (= (:contras before) (v/contradictions kb)))
          (doseq [sentence sentences]
            (is (nil? (v/handle-of kb sentence CxThe))
                (str "nothing is stored for " (pr-str sentence)))))
        (testing "the same batch without the entry that tripped lands whole"
          (let [ok    (into [] (keep-indexed #(when (not= 2 %1) %2)) (:add batch))
                added (:added (v/edit! kb {:add ok}))]
            (is (= 3 (count added)))
            (doseq [[sentence _] ok]
              (is (v/in? kb (v/handle-of kb sentence CxThe))
                  (str (pr-str sentence) " is believed")))))))))

(deftest a-batch-that-refuses-leaves-a-premise-it-named-for-removal-believed
  ;; Removes run after adds, so a batch refused on an add has not reached its removals —
  ;; and the rollback owes the premise, and everything derived from it, untouched.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog cat barks Muffet Whiskers CxThe]
      (v/assert kb (list 'genlCx CxThe 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
      (v/assert-rule kb [(list dog '?x)] (list barks '?x) CxThe)
      (let [h  (v/assert kb (list dog Muffet) CxThe)
            bh (v/handle-of kb (list barks Muffet) CxThe)]
        (is (v/in? kb bh) "the conclusion the removal would sweep is derived")
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/edit! kb {:add [[(list cat Whiskers) CxThe]
                                        [(list cat Muffet) CxThe]]
                                  :remove [h]})))
        (testing "the removal was never made: the premise stands at its handle"
          (is (= h (v/handle-of kb (list dog Muffet) CxThe)))
          (is (v/in? kb h))
          (is (true? (v/premise? kb h))))
        (testing "and so does what it supported, at its own handle"
          (is (= bh (v/handle-of kb (list barks Muffet) CxThe)))
          (is (v/in? kb bh)))
        (testing "with neither add left behind"
          (is (nil? (v/handle-of kb (list cat Whiskers) CxThe)))
          (is (nil? (v/handle-of kb (list cat Muffet) CxThe))))))))

(deftest a-strength-a-refused-batch-raised-goes-back-down
  ;; The audit's third case: a handle the batch did not create and did not merely
  ;; re-assert, but **re-classed**.  `mark-premise` resolves by content and keeps the
  ;; stronger class, which is right for an assertion and wrong for an undo.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog cat Muffet Whiskers CxThe]
      (v/assert kb (list 'genlCx CxThe 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
      (let [h (v/assert kb (list dog Muffet) CxThe)]
        (is (= :default (v/defeat-class kb h)))
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/edit! kb {:add [[(list dog Muffet) CxThe {:strength :monotonic}]
                                        [(list cat Whiskers) CxThe]
                                        [(list cat Muffet) CxThe]]})))
        (testing "the class the batch raised is back where the KB had it"
          (is (= :default (v/defeat-class kb h))))))))

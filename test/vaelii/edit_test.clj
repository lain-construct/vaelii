(ns vaelii.edit-test
  "`edit` — a batched add-then-remove that settles once.  The point is efficiency and
  a stable belief state: adds land before removes, so a conclusion the removed premise
  solely-supported but an added one re-derives keeps a witness through the
  dependency-directed sweep — it is never swept and rebuilt, and never flickers OUT and
  back.  The final state equals running the asserts and retracts singly."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(deftest edit-adds-before-removing-so-a-rederivable-conclusion-survives
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [a b c X TheContext]
      ;; two rules concluding the same thing, from different premises
      (v/assert-rule kb [(list a '?x)] (list c '?x) TheContext)
      (v/assert-rule kb [(list b '?x)] (list c '?x) TheContext)
      (let [fa (v/assert kb (list a X) TheContext)
            ch (v/handle-of kb (list c X) TheContext)]
        (is (v/in? kb ch) "(c X) is derived from (a X)")
        (let [result (v/edit kb {:add [[(list b X) TheContext]] :remove [fa]})]
          (testing "the return reports the add and the teardown"
            (is (= 1 (count (:added result))))
            (is (pos? (:removed-sentexes (:removed result)))))
          (testing "the removed premise is gone and the added one is believed"
            (is (nil? (v/handle-of kb (list a X) TheContext)))
            (is (v/in? kb (v/handle-of kb (list b X) TheContext))))
          (testing "(c X) survived on the new support — same handle, still IN"
            (is (v/in? kb ch))
            (is (contains?
                 (->> (v/supporting-justifications kb ch)
                      (mapcat :antecedents) set)
                 (v/handle-of kb (list b X) TheContext))
                "its live support now names the added premise")))))))

(deftest edit-matches-separate-assert-and-retract
  ;; Run the same scenario two ways on two *sequential* fresh KBs (nesting two
  ;; `tu/fresh` would collide — both take the scratch db pair), then compare belief.
  (tu/with-terms [a b c X TheContext]
    (letfn [(scenario [kb via-edit?]
              (v/assert-rule kb [(list a '?x)] (list c '?x) TheContext)
              (v/assert-rule kb [(list b '?x)] (list c '?x) TheContext)
              (let [fa (v/assert kb (list a X) TheContext)]
                (if via-edit?
                  (v/edit kb {:add [[(list b X) TheContext]] :remove [fa]})
                  (do (v/assert kb (list b X) TheContext)   ; add...
                      (v/retract! kb fa))))               ; ...then remove
              (into {} (for [s [(list a X) (list b X) (list c X)]]
                         [s (let [h (v/handle-of kb s TheContext)] (boolean (and h (v/in? kb h))))])))]
      (let [via-edit (tu/with-neutral-kb [kb tu/fresh] (scenario kb true))
            via-sep  (tu/with-neutral-kb [kb tu/fresh] (scenario kb false))]
        (is (= via-edit via-sep)
            "edit reaches the same belief as add-then-retract done singly")
        (is (get via-edit (list c X)) "(c X) is believed either way")))))

(deftest edit-degenerate-only-adds-or-only-removes
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [p q X TheContext]
      (testing "only adds behaves like assert-many"
        (let [r (v/edit kb {:add [[(list p X) TheContext] [(list q X) TheContext]]})]
          (is (= 2 (count (:added r))))
          (is (= {:removed-sentexes 0 :removed-justifications 0} (:removed r)))
          (is (v/in? kb (v/handle-of kb (list p X) TheContext)))
          (is (v/in? kb (v/handle-of kb (list q X) TheContext)))))
      (testing "only removes behaves like retract"
        (let [ph (v/handle-of kb (list p X) TheContext)
              r  (v/edit kb {:remove [ph]})]
          (is (empty? (:added r)))
          (is (pos? (:removed-sentexes (:removed r))))
          (is (nil? (v/handle-of kb (list p X) TheContext)))
          (is (v/in? kb (v/handle-of kb (list q X) TheContext)) "the untouched premise stays"))))))

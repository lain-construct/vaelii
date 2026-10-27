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
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(deftest edit-adds-before-removing-so-a-rederivable-conclusion-survives
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [a b c X CxThe]
      ;; two rules concluding the same thing, from different premises
      (v/assert-rule kb [(list a '?x)] (list c '?x) CxThe {:direction :forward})
      (v/assert-rule kb [(list b '?x)] (list c '?x) CxThe {:direction :forward})
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
              (v/assert-rule kb [(list a '?x)] (list c '?x) CxThe {:direction :forward})
              (v/assert-rule kb [(list b '?x)] (list c '?x) CxThe {:direction :forward})
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

;; ---- the entry point refuses what the dry run reports ---------------------------

(deftest a-malformed-add-entry-is-refused-whole-not-applied-in-part
  ;; One fn (`add-entry-shape-problem`) is read by both entry points, so what `check-edit`
  ;; reports as `:shape` is what `edit` throws — a 4-element entry is never applied
  ;; with the junk silently dropped.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog Muffet CxShape]
      (testing "a 4-element entry is :shape at both entry points, and nothing lands"
        (let [batch  {:add [[(list dog Muffet) CxShape {} :junk]]}
              before (v/sentex-count kb)]
          (is (= [:shape] (mapv :type (v/check-edit kb batch))))
          (let [e (is (thrown? clojure.lang.ExceptionInfo (v/edit! kb batch)))]
            (is (= :shape (:type (ex-data e)))))
          (is (= before (v/sentex-count kb)))
          (is (nil? (v/handle-of kb (list dog Muffet) CxShape))
              "the entry was refused whole, not applied minus the junk")))
      (testing "a non-sequential entry is :shape at both entry points, not a bare throw"
        (doseq [bad [42 {:sentence 1}]]
          (let [batch {:add [bad]}]
            (is (= [:shape] (mapv :type (v/check-edit kb batch))))
            (let [e (is (thrown? clojure.lang.ExceptionInfo (v/edit! kb batch)))]
              (is (= :shape (:type (ex-data e)))))))))))

(deftest a-batch-half-that-is-not-a-sequence-is-shape-at-every-entry-point
  ;; `{:add 5}` reaches every entry point's iteration, so unrefused it raises a bare
  ;; "Don't know how to create ISeq" out of `check-edit`, `edit` and `preview` alike —
  ;; over the daemon, a 500 with no `:type` to discriminate on.
  (tu/with-neutral-kb [kb tu/fresh]
    (doseq [batch [{:add 5} {:remove 5} {:add {:a 1}} {:remove #{7}}]]
      (testing (pr-str batch)
        (is (= [:shape] (mapv :type (v/check-edit kb batch))))
        (doseq [[nm entry-point] [["edit" #(v/edit! kb batch)]
                                  ["preview" #(v/preview kb batch)]]]
          (let [e (is (thrown? clojure.lang.ExceptionInfo (entry-point))
                      (str nm " refuses " (pr-str batch)))]
            (is (= :shape (:type (ex-data e))) (str nm " says :shape"))))))))

(deftest an-unknown-remove-handle-refuses-the-batch-before-anything-lands
  ;; `check-edit` flags the handle as `:unknown-handle`; an entry point that then quietly
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
  ;; third entry closes a `genl` cycle with its *second* is admissible to `check-edit`
  ;; and refused by the engine two entries in.  That is the case a rollback exists for.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog cat Muffet Rex CxThe]
      (v/assert kb (list 'genlCx CxThe 'CxUniverse) 'CxUniverse)
      (let [sentences [(list dog Muffet) (list 'genl dog cat)
                       (list 'genl cat dog) (list dog Rex)]
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
            (is (= :not-well-formed (:type d)) "the original ex-data is kept")
            (is (true? (:rolled-back d)))
            (is (= :add (:in d)))
            (is (= 2 (:index d)))
            (is (= (nth (:add batch) 2) (:entry d)))
            (is (some? (ex-cause e)) "with the original hung off it as the cause")))
        (testing "and the KB is exactly what it was — count, handle set, belief, dilemmas"
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
    (tu/with-terms [dog cat barks Muffet CxThe]
      (v/assert kb (list 'genlCx CxThe 'CxUniverse) 'CxUniverse)
      (v/assert-rule kb [(list dog '?x)] (list barks '?x) CxThe {:direction :forward})
      (let [h  (v/assert kb (list dog Muffet) CxThe)
            bh (v/handle-of kb (list barks Muffet) CxThe)]
        (is (v/in? kb bh) "the conclusion the removal would sweep is derived")
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/edit! kb {:add [[(list 'genl dog cat) CxThe]
                                        [(list 'genl cat dog) CxThe]]
                                  :remove [h]})))
        (testing "the removal was never made: the premise stands at its handle"
          (is (= h (v/handle-of kb (list dog Muffet) CxThe)))
          (is (v/in? kb h))
          (is (true? (v/premise? kb h))))
        (testing "and so does what it supported, at its own handle"
          (is (= bh (v/handle-of kb (list barks Muffet) CxThe)))
          (is (v/in? kb bh)))
        (testing "with neither add left behind"
          (is (nil? (v/handle-of kb (list 'genl dog cat) CxThe)))
          (is (nil? (v/handle-of kb (list 'genl cat dog) CxThe))))))))

(deftest a-strength-a-refused-batch-raised-goes-back-down
  ;; The audit's third case: a handle the batch did not create and did not merely
  ;; re-assert, but **re-classed**.  `mark-premise` resolves by content and keeps the
  ;; stronger class, which is right for an assertion and wrong for an undo.
  (tu/with-neutral-kb [kb tu/fresh]
    (tu/with-terms [dog cat Muffet CxThe]
      (v/assert kb (list 'genlCx CxThe 'CxUniverse) 'CxUniverse)
      (let [h (v/assert kb (list dog Muffet) CxThe)]
        (is (= :default (v/defeat-class kb h)))
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/edit! kb {:add [[(list dog Muffet) CxThe {:strength :monotonic}]
                                        [(list 'genl dog cat) CxThe]
                                        [(list 'genl cat dog) CxThe]]})))
        (testing "the class the batch raised is back where the KB had it"
          (is (= :default (v/defeat-class kb h))))))))

;; ---- edit-records! and settle-record-edits! --------------------------------------

(defn- believed
  "Every believed record of `kb` as `[sentence context]`, handles resolved."
  [kb]
  (into #{}
        (comp (filter #(v/in? kb %))
              (map #(let [s (p/get-sentex (:records kb) %)]
                      (tu/handle-free kb [(sx/sentence-of s) (:context s)]))))
        (tu/sentex-ids kb)))

(defn- edit-both-ways
  "The believed records after `scenario` through `edit!` (each direction change a
  retraction and a re-assertion) and through `edit-records!` on a reopened KB without
  belief followed by `settle-record-edits!` with `settle-opts`, on two sequential fresh
  KBs.  `scenario` is `{:build (fn [kb]) :remove [[s ctx]] :direction [[[s ctx] bare d]]}`;
  its `:keeps` and `:entailing?`, read by the caller, are records `edit!` must leave
  believed and whether the row runs under the entailing argument-type reading."
  [{:keys [build remove direction]} settle-opts]
  (let [handles (fn [kb] (mapv (fn [[s c]] (v/handle-of kb s c)) remove))]
    [(tu/with-cleared-kb [kb tu/fresh]
       (build kb)
       (v/edit! kb {:remove (handles kb)})
       (doseq [[[s c] bare d] direction]
         (v/retract! kb (v/handle-of kb s c))
         (v/assert kb bare c {:direction d}))
       (believed kb))
     (tu/with-cleared-kb [kb tu/fresh]
       (build kb)
       (let [hs  (handles kb)
             ds  (into {} (map (fn [[[s c] _ d]] [(v/handle-of kb s c) d])) direction)
             kb2 (tu/test-kb)
             r   (v/edit-records! kb2 {:remove hs :direction ds})]
         (v/settle-record-edits! kb2 (assoc settle-opts :seeds (:seeds r)))
         (believed kb2)))]))

(deftest edit-records-then-settle-believes-what-edit-believes
  (tu/with-terms [p q r s t u w bird flies travels blocked parentOf animal dog needs wanted relativeOf childOf kinOf knows person A B Tweety Fido Rex Fred Mary CxThe CxWorld CxDogs CxRa CxRb CxRm]
    (let [rule (fn [ante conseq] (list 'implies ante conseq))
          ;; a firing names one route for each reachability it rests on, so removing the
          ;; edge it named deletes the justification while the second route still
          ;; licenses the firing; `route-first?` puts the second route before the firing
          cx-route (fn [route-first?]
                     (fn [kb]
                       (let [route #(do (v/assert kb (list 'genlCx CxRm CxRa) 'CxUniverse)
                                        (v/assert kb (list 'genlCx CxRb CxRm) 'CxUniverse))]
                         (v/assert kb (list 'genlCx CxRa 'CxUniverse) 'CxUniverse)
                         (v/assert kb (list 'genlCx CxRb CxRa) 'CxUniverse)
                         (when route-first? (route))
                         (v/assert-rule kb [(list p '?x)] (list q '?x) CxRa {:direction :forward})
                         (v/assert kb (list p A) CxRb)
                         (when-not route-first? (route)))))
          genl-route (fn [route-first?]
                       (fn [kb]
                         (let [route #(do (v/assert kb (list 'genl childOf kinOf) 'CxUniverse)
                                          (v/assert kb (list 'genl kinOf relativeOf) 'CxUniverse))]
                           (v/assert kb (list 'genlCx CxThe 'CxUniverse) 'CxUniverse)
                           (v/assert-rule kb [(list relativeOf '?x '?y)] (list knows '?x '?y) CxThe
                                          {:direction :forward})
                           (v/assert kb (list 'genl childOf relativeOf) 'CxUniverse)
                           (when route-first? (route))
                           (v/assert kb (list childOf Fido Rex) CxThe)
                           (when-not route-first? (route)))))
          ;; `(animal Fred)` is minted off `(parentOf Fred Mary)` and withheld while
          ;; `(dog Fred)` says it more specifically (docs/argtypes.md)
          withheld (fn [kb]
                     (doseq [c [CxWorld CxDogs]]
                       (v/assert kb (list 'genlCx c 'CxUniverse) 'CxUniverse))
                     (v/assert kb (list 'genlCx CxWorld CxDogs) 'CxUniverse)
                     (v/assert kb (list 'genl animal 'thing) 'CxUniverse)
                     (v/assert kb (list 'genl dog animal) 'CxUniverse)
                     (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
                     (v/assert kb (list dog Fred) CxDogs)
                     (v/assert kb (list parentOf Fred Mary) CxWorld))
          rows
          {"a removed premise takes its forward chain with it"
           {:build (fn [kb]
                     (v/assert-rule kb [(list p '?x)] (list q '?x) CxThe {:direction :forward})
                     (v/assert-rule kb [(list q '?x)] (list r '?x) CxThe {:direction :forward})
                     (v/assert kb (list p A) CxThe)
                     (v/assert kb (list p B) CxThe))
            :remove [[(list p A) CxThe]]}

           "a removed defeater lets a default and what it fires come back"
           {:build (fn [kb]
                     (v/assert kb (list 'set/defaultRule (rule (list bird '?x) (list flies '?x))) CxThe)
                     (v/assert-rule kb [(list flies '?x)] (list travels '?x) CxThe {:direction :forward})
                     (v/assert kb (list bird Tweety) CxThe)
                     (v/assert kb (list 'not (list flies Tweety)) CxThe {:strength :monotonic}))
            :remove [[(list 'not (list flies Tweety)) CxThe]]}

           "a removed fact a negation-as-failure antecedent read releases the firing"
           {:build (fn [kb]
                     (v/assert-rule kb [(list p '?x) (list 'unknown (list blocked '?x))] (list u '?x)
                                    CxThe {:direction :forward})
                     (v/assert kb (list p A) CxThe)
                     (v/assert kb (list blocked A) CxThe))
            :remove [[(list blocked A) CxThe]]}

           "a removed declaration releases a held fact, and the firing it holds back"
           {:build (fn [kb]
                     (v/assert kb (list 'genl dog 'thing) 'CxUniverse)
                     (v/assert kb (list 'unary_predicate needs) 'CxUniverse)
                     (v/assert-rule kb [(list needs '?x)] (list wanted '?x) CxThe {:direction :forward})
                     (v/assert kb (list needs 5) CxThe)
                     (v/assert kb (list 'arg needs 1 dog) 'CxUniverse))
            :remove [[(list 'arg needs 1 dog) 'CxUniverse]]}

           "a fact defeated on arrival is chained once the removal revives it"
           {:build (fn [kb]
                     (v/assert-rule kb [(list q '?x)] (list w '?x) CxThe {:direction :forward})
                     (v/assert kb (list 'not (list q A)) CxThe {:strength :monotonic})
                     (v/assert kb (list q A) CxThe))
            :remove [[(list 'not (list q A)) CxThe]]}

           "a removed membership releases the general mint it withheld"
           {:build withheld :remove [[(list dog Fred) CxDogs]]}

           "a removed genl edge releases the general mint the membership withheld"
           {:build withheld :remove [[(list 'genl dog animal) 'CxUniverse]]}

           "a removed genl route leaves the mint another route derives"
           {:build (fn [kb]
                     (v/assert kb (list 'arg relativeOf 1 person) 'CxUniverse)
                     (v/assert kb (list 'genl childOf relativeOf) 'CxUniverse)
                     (v/assert kb (list 'genl childOf kinOf) 'CxUniverse)
                     (v/assert kb (list 'genl kinOf relativeOf) 'CxUniverse)
                     (v/assert kb (list childOf Fido Rex) 'CxUniverse))
            :remove [[(list 'genl childOf relativeOf) 'CxUniverse]]
            :keeps  [[(list person Fido) 'CxUniverse]] :entailing? true}

           "a removed genlCx edge leaves the firing a later second route licenses"
           {:build (cx-route false) :remove [[(list 'genlCx CxRb CxRa) 'CxUniverse]]
            :keeps [[(list q A) CxRb]]}

           "a removed genlCx edge leaves the firing an earlier second route licenses"
           {:build (cx-route true) :remove [[(list 'genlCx CxRb CxRa) 'CxUniverse]]
            :keeps [[(list q A) CxRb]]}

           "a removed genl edge leaves the firing a later second route licenses"
           {:build (genl-route false) :remove [[(list 'genl childOf relativeOf) 'CxUniverse]]
            :keeps [[(list knows Fido Rex) CxThe]]}

           "a removed genl edge leaves the firing an earlier second route licenses"
           {:build (genl-route true) :remove [[(list 'genl childOf relativeOf) 'CxUniverse]]
            :keeps [[(list knows Fido Rex) CxThe]]}

           "a removed premise that a firing also concludes stays, derived"
           {:build (fn [kb]
                     (v/assert-rule kb [(list p '?x)] (list q '?x) CxThe {:direction :forward})
                     (v/assert kb (list p A) CxThe)
                     (v/assert kb (list q A) CxThe))
            :remove [[(list q A) CxThe]]}

           "a removed argument declaration takes its type mint with it"
           {:build (fn [kb]
                     (v/assert kb (list 'arg parentOf 1 animal) CxThe)
                     (v/assert kb (list parentOf Fido Rex) CxThe))
            :remove [[(list 'arg parentOf 1 animal) CxThe]]}

           "a rule taken off forward takes its firings with it"
           {:build (fn [kb]
                     (v/assert-rule kb [(list p '?x)] (list s '?x) CxThe {:direction :forward})
                     (v/assert kb (list p A) CxThe))
            :direction [[[(rule (list p '?x) (list s '?x)) CxThe] (rule (list p '?x) (list s '?x)) :backward]]}

           "a rule put on forward fires over the stored facts"
           {:build (fn [kb]
                     (v/assert-rule kb [(list p '?x)] (list t '?x) CxThe {:direction :backward})
                     (v/assert kb (list p A) CxThe))
            :direction [[[(rule (list p '?x) (list t '?x)) CxThe] (rule (list p '?x) (list t '?x)) :forward]]}}]
      (doseq [[label row] rows]
        (testing label
          ;; an `:entailing?` row keeps an argument-type mint, which only the entailing
          ;; reading makes
          (let [[via-edit via-records] (if (:entailing? row)
                                         (tu/with-entailing (edit-both-ways row {}))
                                         (edit-both-ways row {}))]
            (doseq [k (:keeps row)]
              (is (contains? via-edit k) (str "the row exercises " (pr-str k))))
            (is (= via-edit via-records)
                (pr-str {:only-edit (remove via-records via-edit)
                         :only-records (remove via-edit via-records)}))))))))

(deftest edit-records-refuses-before-writing
  (tu/with-terms [p q A CxThe]
    (let [ex-type (fn [f] (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))]
      (tu/with-cleared-kb [kb tu/fresh]
        (let [fa (v/assert kb (list p A) CxThe)
              fq (v/assert kb (list q A) CxThe)
              ex (v/assert kb (list 'except (list 'sentexHandle fq)) CxThe)]
          (testing "a KB with belief"
            (is (= :belief-built (ex-type #(v/edit-records! kb {:remove [fa]})))))
          (let [kb2 (tu/test-kb)]
            (testing "an except removal, and the batch's other removal stays unwritten"
              (is (= :record-edit-unsupported (ex-type #(v/edit-records! kb2 {:remove [fa ex]}))))
              (is (some? (p/get-sentex (:records kb2) fa))))
            (testing "a direction on a fact, a bad direction, an absent handle"
              (is (= :unknown-option (ex-type #(v/edit-records! kb2 {:direction {fa :forward}}))))
              (is (= :unknown-option (ex-type #(v/edit-records! kb2 {:direction {fa :sideways}}))))
              (is (= :unknown-handle (ex-type #(v/edit-records! kb2 {:direction {99999 :forward}})))))
            (testing "the same batch run again completes it and counts what is gone"
              (is (= 1 (:removed (v/edit-records! kb2 {:remove [fa]}))))
              (is (= {:removed 0 :absent 1}
                     (select-keys (v/edit-records! kb2 {:remove [fa]}) [:removed :absent]))))
            (testing "a nil removal, as `handle-of` answers on an index not built, counts as absent"
              (is (= {:removed 0 :absent 1}
                     (select-keys (v/edit-records! kb2 {:remove [nil]}) [:removed :absent]))))))))))

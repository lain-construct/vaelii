(ns vaelii.deferred-settle-test
  "`with-deferred-settle` / `assert-many`: assert a batch with belief settled once
  at the end instead of per assert.

  The contract is *same belief, fewer settles*.  Belief is order-independent and
  recomputed from current state, so deferring the reconciliation cannot change the
  answer — only when it is paid.  The sharp case is `exceptWhen`, whose sweep runs
  **in** settle: under deferral a conclusion the exception will block stays believed
  until the closing settle, then goes.  That is observable mid-batch, which is what
  proves the settle was genuinely deferred rather than merely redundant."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- except-rule [exception antes conseq]
  (list 'exceptWhen exception (list 'set/defaultRule (vr/rule-sentence antes conseq))))

;; ---- same belief as per-assert -------------------------------------------
;; The excepted binding (Opus) has its conclusion placed while `(bird Opus)` is
;; asserted — before `(penguin Opus)` arrives — so under deferral it is swept only
;; at the closing settle.  The answers must match the per-assert version in
;; `except_test`: Tweety flies, Opus does not, nothing was arbitrated.

(tu/deftest-kb deferred-settle-reaches-the-same-belief-as-per-assert
  (tu/with-terms [bird penguin flies Tweety Opus BirdContext]
    (v/with-deferred-settle kb
      (v/assert kb (except-rule (list penguin '?b) [(list bird '?b)] (list flies '?b))
                BirdContext)
      (v/assert kb (list bird Tweety) BirdContext)
      (v/assert kb (list bird Opus) BirdContext)
      (v/assert kb (list penguin Opus) BirdContext))
    (testing "the unexcepted binding concludes"
      (is (seq (v/sentexes-matching kb (list flies Tweety) BirdContext))))
    (testing "the excepted binding was swept by the closing settle"
      (is (empty? (v/sentexes-matching kb (list flies Opus) BirdContext))))
    (testing "blocking is not rebutting, and nothing was arbitrated"
      (is (empty? (v/sentexes-matching kb (list 'not (list flies Opus)) BirdContext)))
      (is (empty? (v/conflicts kb))))))

;; ---- the settle is genuinely deferred ------------------------------------
;; If the sweep ran per assert, `(flies Opus)` would vanish the instant
;; `(penguin Opus)` is stored.  Under deferral it must still be believed *inside*
;; the batch and gone only after it closes — the observable difference.

(tu/deftest-kb deferral-postpones-the-exception-sweep-to-the-batch-end
  (tu/with-terms [bird penguin flies Opus BirdContext]
    (v/assert kb (except-rule (list penguin '?b) [(list bird '?b)] (list flies '?b))
              BirdContext)
    (v/assert kb (list bird Opus) BirdContext)
    (is (seq (v/sentexes-matching kb (list flies Opus) BirdContext))
        "flies Opus is placed while only bird is known")
    (v/with-deferred-settle kb
      (v/assert kb (list penguin Opus) BirdContext)
      (testing "mid-batch: settle deferred, so the queued sweep has not run"
        (is (seq (v/sentexes-matching kb (list flies Opus) BirdContext)))))
    (testing "the closing settle ran the sweep"
      (is (empty? (v/sentexes-matching kb (list flies Opus) BirdContext))))))

;; ---- assert-many: derive + return handles --------------------------------

(tu/deftest-kb assert-many-chains-per-fact-and-settles-once
  (tu/with-terms [parentOf grandparentOf Tom Bob Ann FamContext]
    (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                   (list grandparentOf '?x '?z) FamContext)
    (let [hs (v/assert-many kb [(list parentOf Tom Bob) (list parentOf Bob Ann)]
                            FamContext)]
      (testing "one handle back per input sentence, in order"
        (is (= 2 (count hs)))
        (is (every? nat-int? hs)))
      (testing "chaining ran per fact, so the grandparent is derived after the settle"
        (is (seq (v/sentexes-matching kb (list grandparentOf Tom Ann) FamContext))))
      (testing "the returned handles are the asserted facts"
        (is (= (set hs)
               (set [(v/handle-of kb (list parentOf Tom Bob) FamContext)
                     (v/handle-of kb (list parentOf Bob Ann) FamContext)])))))))

;; ---- nesting composes: only the outermost settles ------------------------

(tu/deftest-kb nested-deferred-settle-composes
  (tu/with-terms [bird penguin flies Opus BirdContext]
    (v/assert kb (except-rule (list penguin '?b) [(list bird '?b)] (list flies '?b))
              BirdContext)
    (v/assert kb (list bird Opus) BirdContext)
    (v/with-deferred-settle kb
      (v/with-deferred-settle kb
        (v/assert kb (list penguin Opus) BirdContext))
      (testing "an inner block does not settle; the outer one still owns it"
        (is (seq (v/sentexes-matching kb (list flies Opus) BirdContext)))))
    (testing "the outermost settle swept it"
      (is (empty? (v/sentexes-matching kb (list flies Opus) BirdContext))))))

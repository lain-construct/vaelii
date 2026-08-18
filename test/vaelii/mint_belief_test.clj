;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.mint-belief-test
  "A rule a **generator** stamps out is *derived* content: it is justified by the
  firing that minted it, never marked a premise, so the ordinary relabel un-believes
  it the moment what licensed it goes (`chain/mint-rule`, docs/generators.md).  These
  pin that invariant against **defeat** — the case retraction tests do not reach.

  `generator_test`'s `retracting-the-fill-retracts-the-rule` and
  `rejoin_belief_test` cover the *retraction* of a fill (which SWEEPS the mint's node
  outright) and the two *re-join* firing paths.  Neither pins what happens when the
  mark that licensed the mint is **defeated** rather than retracted: a defeated
  default's mint stays stored, indexed and node-bearing while OUT, so its *belief* is
  the only thing that keeps it from firing.  The claim under test is that its belief
  does move — the mint's sole justification names the mark handle as an antecedent, so
  forcing the mark OUT makes the justification invalid and the relabel takes the mint
  OUT with it.

  The **oracle is the trigger path**, exactly as `rejoin_belief_test` states it:
  `res/rule-believed?` is what `fire-rules-for` asks before a trigger match fires, and
  a defeated mint that reads un-believed there draws nothing.

  A NOTE on measuring a mint, because it is the trap this file exists to close.  The
  marker rule — the `set/defaultRule (implies (trig ?p) (mark ?p))` that hands the
  generator its fill — is itself a stored rule with an antecedent whose consequent is a
  *fact*, so `vr/generator-sentex?` is false of it and it is an **asserted premise**,
  correctly IN for the whole scenario (nothing in the engine defeats a rule, only its
  conclusion — docs/nmtms.md).  A `(->> rules (remove generator?) first)` helper picks
  *it* up, not the derived mint, and then reports a believed rule after the defeat and
  reads as a soundness hole.  `the-marker-default-is-not-the-mint` pins the two apart:
  the marker is a premise, the mint is derived, and only the mint's belief moves."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded starter/load-into))
(use-fixtures :each (tu/neutral))

(defn- the-mint
  "The one *derived* stamped rule in `ctx` concluding `pred` — a rule with an
  antecedent, not a generator, and **not a premise**.  Found by what it concludes and
  by its being derived, so it can never be confused with the marker default the
  generator fires on (which is an asserted premise concluding a fact)."
  [kb ctx pred]
  (->> (v/sentexes-in-context kb ctx)
       (filter :antecedent)
       (remove vr/generator-sentex?)
       (remove #(v/premise? kb (:id %)))
       (filter #(= pred (some-> (:consequent %) first)))
       first))

(defn- build-mint!
  "Assert a generator, a marker default and one fill so a rule is minted; return the
  derived mint's sentex map.  `(trig pbigger)` fires the marker to conclude
  `(mark pbigger)`, on which the generator fires to stamp out
  `(implies (pbigger ?x ?y) (seen ?x))`."
  [kb mark seen trig pbigger ctx]
  (v/assert kb (list 'implies (list mark '?rel)
                     (list 'implies (list '?rel '?x '?y) (list seen '?x)))
            ctx)
  (v/assert kb (list 'set/defaultRule
                     (list 'implies (list 'and (list trig '?p)) (list mark '?p)))
            ctx)
  (v/assert kb (list trig pbigger) ctx)
  (the-mint kb ctx seen))

;; ---- the invariant: a defeated mint is un-believed -----------------------

(tu/deftest-kb a-defeated-mint-is-un-believed
  (tu/with-terms [pmark pseen trig pbigger CxMB]
    (let [mint (build-mint! kb pmark pseen trig pbigger CxMB)
          mh   (:id mint)]
      (is (some? mint) "a rule was stamped")
      (testing "before the defeat the mint is a derived, believed rule"
        (is (not (v/premise? kb mh)) "the mint is derived, not a premise")
        (is (seq (v/supporting-justifications kb mh))
            "and it rests on the generator's firing")
        (is (v/in? kb mh))
        (is (res/rule-believed? kb mh)))
      (testing "defeating the mark that licensed it takes the mint OUT"
        (v/assert kb (list 'not (list pmark pbigger)) CxMB {:strength :monotonic})
        (is (empty? (v/sentexes-matching kb (list pmark pbigger) CxMB))
            "the mark is defeated")
        (is (not (v/in? kb mh))
            "the mint's sole justification names the mark, now OUT — so the mint is OUT")
        (is (not (res/rule-believed? kb mh))
            "and the belief gate the chainers read agrees")))))

;; ---- soundness: an un-licensed mint fires nothing ------------------------

(tu/deftest-kb a-defeated-mint-does-not-fire-on-the-trigger-path
  ;; the oracle path: a fact matching the mint's antecedent arrives *after* the defeat,
  ;; so `fire-rules-for` reaches the mint through the antecedent index (which posts on
  ;; storage) and must refuse it on `res/rule-believed?`.  A refused rule draws no
  ;; conclusion at all — not even one that would only label OUT — so the conclusion is
  ;; neither believed nor stored.
  (tu/with-terms [pmark pseen trig pbigger dog cat CxMB]
    (let [mint (build-mint! kb pmark pseen trig pbigger CxMB)]
      (is (some? mint) "a rule was stamped")
      (v/assert kb (list 'not (list pmark pbigger)) CxMB {:strength :monotonic})
      (is (not (res/rule-believed? kb (:id mint))) "the mint is un-believed")
      (testing "a tuple the mint would range over arrives, and draws nothing"
        (v/assert kb (list pbigger dog cat) CxMB)
        (v/forward-chain kb)
        (is (empty? (v/sentexes-matching kb (list pseen dog) CxMB))
            "the disbelieved mint concluded nothing believed")
        (is (nil? (v/handle-of kb (list pseen dog) CxMB))
            "and the trigger path refused it outright — no OUT-labelled sentex either")))))

;; ---- the measurement trap this file closes -------------------------------

(tu/deftest-kb the-marker-default-is-not-the-mint
  ;; The marker `defaultRule (implies (trig ?p) (mark ?p))` is a stored rule concluding
  ;; a fact — not a generator — so a `(remove generator?) first` helper returns *it*,
  ;; and it is an asserted PREMISE, correctly believed for the whole scenario.  Mistaking
  ;; it for the mint is what makes a defeated mint *look* like it stays believed.  Pin the
  ;; two apart: the marker stays IN as a premise, only the derived mint's belief moves.
  (tu/with-terms [pmark pseen trig pbigger CxMB]
    (let [mint (build-mint! kb pmark pseen trig pbigger CxMB)
          ;; the naive helper: first non-generator rule with an antecedent
          naive (->> (v/sentexes-in-context kb CxMB)
                     (filter :antecedent)
                     (remove vr/generator-sentex?)
                     (filter #(v/premise? kb (:id %)))
                     first)]
      (is (some? mint) "the derived mint exists")
      (is (some? naive) "so does a premise rule the naive helper would grab")
      (is (not= (:id mint) (:id naive))
          "they are different handles — the naive pick is not the mint")
      (is (v/premise? kb (:id naive)) "the naive pick is an asserted premise")
      (is (not (v/premise? kb (:id mint))) "the mint is derived")
      (testing "after the defeat the premise marker stays IN; only the mint moves"
        (v/assert kb (list 'not (list pmark pbigger)) CxMB {:strength :monotonic})
        (is (res/rule-believed? kb (:id naive))
            "the marker rule is a premise — nothing defeats a rule, only its conclusion")
        (is (not (res/rule-believed? kb (:id mint)))
            "the mint is un-believed the moment its licensing mark is defeated")))))

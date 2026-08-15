;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.placement-context-witness-test
  "**A firing rests on the `genlCx` edges its placement saw its ingredients over**,
  and says so.

  A conclusion is placed in the maximal contexts that see the rule, the antecedent facts
  and the taxonomy the match climbed — and every one of those sightings is a reachability
  up the context cone, supported by an ordinary sentex somebody asserted and can take
  back.  A justification that named only the rule and the facts left the conclusion
  standing, and believed, in a context that could no longer see either of them: the same
  KB built without the edge derives nothing, so belief would be a function of arrival
  order.

  So the firing's justification names a **witness** for each sighting: one `genlCx`
  path from the placement up to each ingredient context, one supporter per edge.  A
  section per consequence below — `why` shows the edges, retracting either side's edge
  withdraws what it licensed, defeating one puts the conclusion OUT, a reachability that
  outlives the named witness re-derives, and an escape-hatch `(ist Ctx S)` placement
  names nothing, because it rests on nothing.

  The `genl` twin of all of it is `subsumption_support_test`, and the two are one claim
  about two relations."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.starter :as starter]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded starter/load-into))
(use-fixtures :each (tu/neutral))

(defn- antecedent-sentences
  "The sentences of everything the (single) justification of `handle` rests on — what
  `why` walks into, the rule included."
  [kb handle]
  (->> (v/supporting-justifications kb handle)
       (mapcat :antecedents)
       (map #(:sentence (v/sentex kb %)))
       set))

(defn- edge-sentexes
  "The `genlCx` sentexes among a conclusion's antecedents."
  [kb handle]
  (->> (v/supporting-justifications kb handle)
       (mapcat :antecedents)
       (map #(v/sentex kb %))
       (filter #(= 'genlCx (first (:sentence %))))))

(defn- under!
  "Wire `sub` under each of `supers`, and every super under CxUniverse."
  [kb sub & supers]
  (doseq [s supers]
    (v/assert kb (list 'genlCx s 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx sub s) 'CxUniverse)))

;; ---- what the justification names ---------------------------------------

(tu/deftest-kb a-firing-placed-below-its-rule-names-the-edge-it-saw-the-rule-over
  (tu/with-terms [bird flies Tweety CxLow CxHigh]
    (under! kb CxLow CxHigh)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh)
    (v/assert kb (list bird Tweety) CxLow)
    (let [derived (:id (first (v/sentexes-matching kb (list flies Tweety) CxLow)))]
      (is (some? derived) "the rule was inherited into the context holding the fact")
      (testing "the edge is an antecedent, beside the fact and the rule"
        (is (contains? (antecedent-sentences kb derived) (list 'genlCx CxLow CxHigh))))
      (testing "so `why` shows it, rather than a proof that skips how the rule was seen"
        (let [because (->> (v/why kb derived) :support first :because (map :sentence) set)]
          (is (contains? because (list 'genlCx CxLow CxHigh))))))))

(tu/deftest-kb a-same-context-firing-names-no-edge
  ;; the control: a placement that reaches its ingredients reflexively rests on no
  ;; context edge at all, so this section proves something other than "the antecedent
  ;; list grew"
  (tu/with-terms [bird flies Tweety CxOne]
    (v/assert kb (list 'genlCx CxOne 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxOne)
    (v/assert kb (list bird Tweety) CxOne)
    (let [derived (:id (first (v/sentexes-matching kb (list flies Tweety) CxOne)))
          antes   (:antecedents (first (v/supporting-justifications kb derived)))
          named   (into #{} (map #(:sentence (v/sentex kb %))) antes)]
      ;; *which* sentexes, not how many: this file's whole subject is which ingredients a
      ;; placement rests on, and a count of two is equally true of the wrong two.  The
      ;; rule is matched on its shape rather than as written, a stored rule being
      ;; canonically renumbered (`?x` reads back `?var0`).
      (is (= 2 (count named)))
      (is (contains? named (list bird Tweety)) "the fact itself")
      (is (some #(and (seq? %) (= 'implies (first %)) (= bird (ffirst (rest %)))) named)
          "and the rule that fired, not some other justification's")
      (is (not-any? #(and (seq? %) (= 'genlCx (first %))) named)
          "and no context edge, the placement reaching its ingredients reflexively"))))

(tu/deftest-kb every-edge-on-the-path-is-named
  ;; visibility is transitive, so a rule two steps up is seen over two edges and either
  ;; one of them is enough to withdraw the conclusion
  (tu/with-terms [bird flies Tweety CxLow CxMid CxHigh]
    (v/assert kb (list 'genlCx CxHigh 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxMid CxHigh) 'CxUniverse)
    (v/assert kb (list 'genlCx CxLow CxMid) 'CxUniverse)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh)
    (v/assert kb (list bird Tweety) CxLow)
    (let [derived (:id (first (v/sentexes-matching kb (list flies Tweety) CxLow)))
          antes   (antecedent-sentences kb derived)]
      (is (some? derived))
      (is (contains? antes (list 'genlCx CxLow CxMid)))
      (is (contains? antes (list 'genlCx CxMid CxHigh))))))

(tu/deftest-kb the-rule-side-and-the-fact-side-are-both-named
  ;; the placement descends below two incomparable contexts, so it sees the rule over one
  ;; edge and the fact over another — and rests on both
  (tu/with-terms [bird flies Tweety CxPlace CxRule CxFact]
    (under! kb CxPlace CxRule CxFact)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxRule)
    (v/assert kb (list bird Tweety) CxFact)
    (let [placed (first (v/sentexes-matching kb (list flies Tweety) '?ctx))
          antes  (antecedent-sentences kb (:id placed))]
      (is (= CxPlace (:context placed)) "the one context below both")
      (is (contains? antes (list 'genlCx CxPlace CxRule)))
      (is (contains? antes (list 'genlCx CxPlace CxFact))))))

(tu/deftest-kb the-named-edge-is-one-the-placement-can-see
  (tu/with-terms [bird flies Tweety CxLow CxHigh]
    (under! kb CxLow CxHigh)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh)
    (v/assert kb (list bird Tweety) CxLow)
    (let [derived (:id (first (v/sentexes-matching kb (list flies Tweety) CxLow)))
          edges   (edge-sentexes kb derived)]
      (is (seq edges))
      (is (every? #(v/sees? kb CxLow (:context %)) edges)
          "every edge the conclusion rests on is one its own context sees"))))

;; ---- retracting either side's edge withdraws what it licensed -------------

(tu/deftest-kb retracting-the-rule-side-edge-withdraws-the-conclusion
  (tu/with-terms [bird flies Tweety CxPlace CxRule CxFact]
    (under! kb CxPlace CxRule CxFact)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxRule)
    (v/assert kb (list bird Tweety) CxFact)
    (is (seq (v/sentexes-matching kb (list flies Tweety) '?ctx)))
    (v/retract! kb (v/handle-of kb (list 'genlCx CxPlace CxRule) 'CxUniverse))
    (testing "with the edge gone the placement cannot see the rule, so neither does the conclusion stand"
      (is (empty? (v/sentexes-matching kb (list flies Tweety) '?ctx))))
    (testing "and the ingredients that were not retracted are all still believed"
      (is (seq (v/sentexes-matching kb (list bird Tweety) CxFact))))))

(tu/deftest-kb retracting-the-fact-side-edge-withdraws-the-conclusion
  (tu/with-terms [bird flies Tweety CxPlace CxRule CxFact]
    (under! kb CxPlace CxRule CxFact)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxRule)
    (v/assert kb (list bird Tweety) CxFact)
    (is (seq (v/sentexes-matching kb (list flies Tweety) '?ctx)))
    (v/retract! kb (v/handle-of kb (list 'genlCx CxPlace CxFact) 'CxUniverse))
    (is (empty? (v/sentexes-matching kb (list flies Tweety) '?ctx)))))

(tu/deftest-kb retracting-one-edge-of-a-chain-withdraws-the-conclusion
  (tu/with-terms [bird flies Tweety CxLow CxMid CxHigh]
    (v/assert kb (list 'genlCx CxHigh 'CxUniverse) 'CxUniverse)
    (let [upper (v/assert kb (list 'genlCx CxMid CxHigh) 'CxUniverse)]
      (v/assert kb (list 'genlCx CxLow CxMid) 'CxUniverse)
      (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh)
      (v/assert kb (list bird Tweety) CxLow)
      (is (seq (v/sentexes-matching kb (list flies Tweety) CxLow)))
      (v/retract! kb upper)
      (is (empty? (v/sentexes-matching kb (list flies Tweety) '?ctx))
          "the sighting needed both edges, so losing the upper one is enough"))))

(tu/deftest-kb a-retracted-edge-takes-the-whole-cascade-with-it
  ;; the conclusion is an ordinary datum, so what rests on *it* goes too — the
  ;; dependency-directed sweep needs no special case for a context edge
  (tu/with-terms [bird flies moves Tweety CxLow CxHigh]
    (under! kb CxLow CxHigh)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh)
    (v/assert kb (list 'implies (list flies '?x) (list moves '?x)) CxHigh)
    (v/assert kb (list bird Tweety) CxLow)
    (is (seq (v/sentexes-matching kb (list moves Tweety) CxLow)))
    (v/retract! kb (v/handle-of kb (list 'genlCx CxLow CxHigh) 'CxUniverse))
    (is (empty? (v/sentexes-matching kb (list moves Tweety) '?ctx)))))

(tu/deftest-kb a-retraction-lands-where-a-kb-that-never-had-the-edge-lands
  ;; the invariant the whole file is about: belief is a function of the knowledge, not of
  ;; the order it arrived and left in.  Two arms of the same shape, one that lost the edge
  ;; and one that never had it, and they have to agree.
  (letfn [(without-edge [] (tu/with-terms [bird flies Tweety CxLow CxHigh]
                             (v/assert kb (list 'genlCx CxHigh 'CxUniverse) 'CxUniverse)
                             (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh)
                             (v/assert kb (list bird Tweety) CxLow)
                             (mapv :context (v/sentexes-matching kb (list flies Tweety) '?ctx))))
          (edge-then-gone [] (tu/with-terms [bird flies Tweety CxLow CxHigh]
                               (under! kb CxLow CxHigh)
                               (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh)
                               (v/assert kb (list bird Tweety) CxLow)
                               (v/retract! kb (v/handle-of kb (list 'genlCx CxLow CxHigh) 'CxUniverse))
                               (mapv :context (v/sentexes-matching kb (list flies Tweety) '?ctx))))]
    (is (= [] (without-edge)) "no edge, no sighting, no conclusion")
    (is (= (without-edge) (edge-then-gone))
        "and losing the edge leaves exactly what never having it would have")))

(tu/deftest-kb the-witness-does-not-depend-on-assertion-order
  ;; the edge arriving last has to reach what is already stored (`visibility-seeds`) and
  ;; be named by what it licenses, or the same four sentences mean one thing in one order
  ;; and another in the other — which is the invariant the witnesses exist to keep.
  ;; `ask` rather than a store read, because that is the door a caller uses.
  (letfn [(arm [edge-first?]
            (tu/with-terms [bird flies Tweety CxLow CxHigh]
              (v/assert kb (list 'genlCx CxHigh 'CxUniverse) 'CxUniverse)
              (when edge-first? (v/assert kb (list 'genlCx CxLow CxHigh) 'CxUniverse))
              (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh)
              (v/assert kb (list bird Tweety) CxLow)
              (when-not edge-first? (v/assert kb (list 'genlCx CxLow CxHigh) 'CxUniverse))
              (let [derived (:id (first (v/sentexes-matching kb (list flies Tweety) CxLow)))]
                {:asked   (v/ask? kb (list flies Tweety) CxLow)
                 :witness (contains? (antecedent-sentences kb derived)
                                     (list 'genlCx CxLow CxHigh))
                 ;; and the withdrawal reads the same from either build order
                 :after   (do (v/retract! kb (v/handle-of kb (list 'genlCx CxLow CxHigh)
                                                          'CxUniverse))
                              (v/ask? kb (list flies Tweety) CxLow))})))]
    (is (= {:asked true :witness true :after false} (arm true)))
    (is (= (arm true) (arm false)))))

;; ---- the edge is an antecedent, so belief and strength both run through it ----

(tu/deftest-kb a-defeated-edge-puts-the-conclusion-out-and-a-revived-one-brings-it-back
  ;; defeat, not removal: the justification is structurally intact, so the sweep leaves
  ;; the conclusion alone and the JTMS simply labels it OUT.  Revival is a relabel — the
  ;; *same* handle — which is what distinguishes this from the retraction cases above.
  (tu/with-terms [bird flies Tweety CxLow CxHigh]
    (under! kb CxLow CxHigh)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh)
    (v/assert kb (list bird Tweety) CxLow {:strength :monotonic})
    (let [derived (:id (first (v/sentexes-matching kb (list flies Tweety) CxLow)))
          nope    (v/assert kb (list 'not (list 'genlCx CxLow CxHigh)) 'CxUniverse
                            {:strength :monotonic})]
      (is (not (v/in? kb derived)) "the edge is not believed, so neither is what was seen over it")
      (is (some? (v/sentex kb derived)) "stored all along — nothing was swept")
      (is (= :unsupported (:reason (v/why-not kb derived))))
      (v/retract! kb nope)
      (is (v/in? kb derived) "and the edge coming back brings the conclusion back")
      (is (= derived (:id (first (v/sentexes-matching kb (list flies Tweety) CxLow))))
          "at the same handle: a relabel, not a re-derivation"))))

(tu/deftest-kb defeating-either-side-s-edge-puts-the-conclusion-out
  ;; the three-way witness under defeat rather than retraction: the placement sees the
  ;; rule over one edge and the fact over another, and `(not (genlCx …))` on either is
  ;; enough — the same asymmetry a retraction shows, since both run through the one
  ;; antecedent list
  (tu/with-terms [bird flies Tweety CxPlace CxRule CxFact]
    (under! kb CxPlace CxRule CxFact)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxRule)
    (v/assert kb (list bird Tweety) CxFact {:strength :monotonic})
    (let [derived (:id (first (v/sentexes-matching kb (list flies Tweety) CxPlace)))]
      (is (some? derived))
      (doseq [[side edge] [["rule-side" (list 'genlCx CxPlace CxRule)]
                           ["fact-side" (list 'genlCx CxPlace CxFact)]]]
        (testing side
          (let [nope (v/assert kb (list 'not edge) 'CxUniverse {:strength :monotonic})]
            (is (not (v/in? kb derived)) "the sighting is not believed, so neither is the conclusion")
            (v/retract! kb nope)
            (is (v/in? kb derived) "and it comes back at the same handle when the edge does")))))))

(tu/deftest-kb the-edge-caps-the-conclusion-s-defeat-class
  ;; a conclusion is never stronger than what it rests on, and the edge its placement
  ;; was seen over is now one of those things: known-true fact + bare rule + *defeasible*
  ;; context edge is a defeasible conclusion, however monotonic the fact.
  (tu/with-terms [bird flies Tweety CxLow CxHigh]
    (under! kb CxLow CxHigh)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh {:strength :monotonic})
    (v/assert kb (list bird Tweety) CxLow {:strength :monotonic})
    (testing "seen over a :default edge"
      (is (= :default (v/defeat-class
                        kb (:id (first (v/sentexes-matching kb (list flies Tweety) CxLow)))))))
    (testing "the control: no sighting, and the conclusion is as strong as its grounds"
      (tu/with-terms [Robin]
        (v/assert kb (list bird Robin) CxHigh {:strength :monotonic})
        (is (= :monotonic (v/defeat-class
                            kb (:id (first (v/sentexes-matching kb (list flies Robin) CxHigh))))))))))

;; ---- a reachability that outlives its named witness -----------------------

(tu/deftest-kb an-edge-has-one-supporter-however-many-contexts-state-it
  ;; the `genl` twin has a case for the same edge asserted from two contexts, and this
  ;; relation has no equivalent of it: `genlCx` is a
  ;; `forcedDecontextualizedPredicate`, so the topology has one canonical home and
  ;; stating the edge twice is one sentex.  There is therefore nothing for a witness to
  ;; choose between — the only way a sighting outlives its named edge is a second path.
  (tu/with-terms [bird flies Tweety CxLow CxHigh]
    (v/assert kb (list 'genlCx CxHigh 'CxUniverse) 'CxUniverse)
    (let [e1 (v/assert kb (list 'genlCx CxLow CxHigh) 'CxCore)
          e2 (v/assert kb (list 'genlCx CxLow CxHigh) 'CxUniverse)]
      (is (= e1 e2) "one sentex, in CxUniverse, whichever context stated it")
      (is (= 'CxUniverse (:context (v/sentex kb e1))))
      (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh)
      (v/assert kb (list bird Tweety) CxLow)
      (is (seq (v/sentexes-matching kb (list flies Tweety) CxLow)))
      (v/retract! kb e1)
      (is (empty? (v/sentexes-matching kb (list flies Tweety) '?ctx))
          "so retracting it takes the conclusion — there is no second supporter to keep it"))))

(tu/deftest-kb a-second-path-around-the-edge-keeps-the-conclusion
  ;; multiple inheritance between contexts: Low reaches High two ways.  Either middle
  ;; edge can go.
  (tu/with-terms [bird flies Tweety CxLow CxOne CxTwo CxHigh]
    (v/assert kb (list 'genlCx CxHigh 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxLow CxOne) 'CxUniverse)
    (v/assert kb (list 'genlCx CxLow CxTwo) 'CxUniverse)
    (let [via-one (v/assert kb (list 'genlCx CxOne CxHigh) 'CxUniverse)
          via-two (v/assert kb (list 'genlCx CxTwo CxHigh) 'CxUniverse)]
      (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh)
      (v/assert kb (list bird Tweety) CxLow)
      (let [before (:id (first (v/sentexes-matching kb (list flies Tweety) CxLow)))]
        (is (some? before))
        (v/retract! kb via-one)
        (let [after (:id (first (v/sentexes-matching kb (list flies Tweety) CxLow)))]
          (is (some? after)
              "Low still sees High by the other route, so the rule still reaches the fact")
          (is (not= before after)
              "as a re-derivation, not a survival: the sweep took the old record")))
      (v/retract! kb via-two)
      (is (empty? (v/sentexes-matching kb (list flies Tweety) '?ctx))
          "with both routes gone the conclusion has nothing left to rest on"))))

(tu/deftest-kb a-second-path-keeps-the-conclusion-where-the-rule-sits-off-the-edge
  ;; the **meet** shape, and the one the spine above cannot reach.  There the departing
  ;; edge lay on the line between the rule and the fact, so the rule was in its up-cone
  ;; and the seeding gate found it.  Here the placement sees the rule down one branch and
  ;; the fact down another, and the edge that goes is on neither: nothing that matters
  ;; sits in either of its cones.  A gate reading only those two cones therefore seeds
  ;; nothing, and the revival a surviving route still licenses never happens — which is
  ;; the arrival-order dependence this whole file exists to remove, since the same KB
  ;; built without the direct edge derives the conclusion perfectly well.
  (tu/with-terms [bird flies Tweety CxPlace CxRule CxVia CxFact]
    (v/assert kb (list 'genlCx CxRule 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxFact 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxPlace CxRule) 'CxUniverse)
    (v/assert kb (list 'genlCx CxPlace CxVia) 'CxUniverse)
    (v/assert kb (list 'genlCx CxVia CxFact) 'CxUniverse)
    (let [direct (v/assert kb (list 'genlCx CxPlace CxFact) 'CxUniverse)]
      (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxRule)
      (v/assert kb (list bird Tweety) CxFact)
      (let [before (:id (first (v/sentexes-matching kb (list flies Tweety) CxPlace)))]
        (is (some? before)
            "CxPlace sees the rule one way and the fact the other, so it holds the conclusion")
        (is (contains? (set (map :id (edge-sentexes kb before))) direct)
            "and it named the direct edge as the witness for seeing CxFact")
        (v/retract! kb direct)
        (let [after (:id (first (v/sentexes-matching kb (list flies Tweety) CxPlace)))]
          (is (some? after)
              "CxPlace still reaches CxFact through CxVia, so the conclusion is still licensed")
          (is (not= before after)
              "as a re-derivation: the sweep took the record the named edge held up"))))))

(tu/deftest-kb the-revival-a-removal-owes-is-not-gated-on-the-departing-edges-own-cones
  ;; the control for the case above, stated as the rule rather than the shape: a KB that
  ;; never held the direct edge derives the same conclusion, so a KB that held it and
  ;; lost it must end in the same place.  Anything else makes belief a function of
  ;; whether an edge nobody needs was ever asserted.
  (tu/with-terms [bird flies Tweety CxPlace CxRule CxVia CxFact]
    (v/assert kb (list 'genlCx CxRule 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxFact 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxPlace CxRule) 'CxUniverse)
    (v/assert kb (list 'genlCx CxPlace CxVia) 'CxUniverse)
    (v/assert kb (list 'genlCx CxVia CxFact) 'CxUniverse)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxRule)
    (v/assert kb (list bird Tweety) CxFact)
    (is (seq (v/sentexes-matching kb (list flies Tweety) CxPlace))
        "the direct edge was never needed to derive it")))

(tu/deftest-kb the-re-chain-a-removal-owes-files-no-dropped-conclusion
  ;; the revival pass re-asks every firing the sweep took, to find which of them a
  ;; surviving route still licenses — so the ones it cannot place are the retraction
  ;; restated, and reporting one apiece would displace the ledger's real entries
  (tu/with-terms [bird flies Tweety CxLow CxHigh]
    (under! kb CxLow CxHigh)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh)
    (v/assert kb (list bird Tweety) CxLow)
    (is (seq (v/sentexes-matching kb (list flies Tweety) CxLow)))
    (let [before (count (filter #(= :no-placement (:violation %)) (v/violations kb)))]
      (v/retract! kb (v/handle-of kb (list 'genlCx CxLow CxHigh) 'CxUniverse))
      (is (empty? (v/sentexes-matching kb (list flies Tweety) '?ctx)))
      (is (= before (count (filter #(= :no-placement (:violation %)) (v/violations kb))))
          "the conclusion is gone and the ledger is as it was"))))

(tu/deftest-kb the-edge-survives-a-rebuild-in-the-antecedent-list
  ;; a justification is a durable record, so the edges it names are durable state —
  ;; `recover` rebuilds the JTMS from those records and must hand back the same
  ;; dependency, or a restart would quietly restore the standing-on-nothing conclusion
  (tu/with-terms [bird flies Tweety CxLow CxHigh]
    (under! kb CxLow CxHigh)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh)
    (v/assert kb (list bird Tweety) CxLow)
    (let [derived (:id (first (v/sentexes-matching kb (list flies Tweety) CxLow)))
          before  (antecedent-sentences kb derived)]
      (is (contains? before (list 'genlCx CxLow CxHigh)))
      (v/recover kb)
      (is (= before (antecedent-sentences kb derived)))
      (is (v/in? kb derived) "and it is still believed")
      (v/retract! kb (v/handle-of kb (list 'genlCx CxLow CxHigh) 'CxUniverse))
      (is (empty? (v/sentexes-matching kb (list flies Tweety) '?ctx))
          "so the rebuilt dependency still withdraws"))))

(tu/deftest-kb a-preview-of-removing-the-edge-reports-what-it-would-take
  (tu/with-terms [bird flies Tweety CxLow CxHigh]
    (under! kb CxLow CxHigh)
    (v/assert kb (list 'implies (list bird '?x) (list flies '?x)) CxHigh)
    (v/assert kb (list bird Tweety) CxLow)
    (let [edge    (v/handle-of kb (list 'genlCx CxLow CxHigh) 'CxUniverse)
          removed (set (map :sentence (:believed-removed (v/preview kb {:remove [edge]} {}))))]
      (is (contains? removed (list flies Tweety))
          "the conclusion the edge licensed is named as a casualty"))
    (is (seq (v/sentexes-matching kb (list flies Tweety) CxLow))
        "and the preview put the KB back")))

;; ---- what is *not* an ingredient, and so is not named --------------------

(tu/deftest-kb an-ist-consequent-names-no-context-edge-for-a-rule-it-need-not-see
  ;; the escape hatch places where the author said, whether or not the target can see the
  ;; rule or the facts — so the placement rests on no sighting of either, and naming one
  ;; would be a dependency the engine does not have.  A conclusion that goes when an
  ;; unrelated edge is retracted is the same order-dependence pointing the other way.
  (tu/with-terms [bird flies Tweety CxSaid CxHeld]
    (v/assert kb (list 'genlCx CxSaid 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxHeld 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'implies (list bird '?x) (list 'ist CxHeld (list flies '?x))) CxSaid)
    (v/assert kb (list bird Tweety) CxSaid)
    (let [placed (first (v/sentexes-matching kb (list flies Tweety) CxHeld))]
      (is (some? placed) "the named target took it, though it sees neither the rule nor the fact")
      (is (empty? (edge-sentexes kb (:id placed)))
          "and rests on no context edge, because its placement was not derived from one")
      (v/retract! kb (v/handle-of kb (list 'genlCx CxHeld 'CxUniverse) 'CxUniverse))
      (is (seq (v/sentexes-matching kb (list flies Tweety) CxHeld))
          "so wiring the target elsewhere neither licensed the conclusion nor withdraws it"))))

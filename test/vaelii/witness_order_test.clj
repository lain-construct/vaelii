;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.witness-order-test
  "One firing per satisfying combination, not one per side that could start it
  (`chain/*agenda-arrivals*`).

  A two-antecedent rule is triggered by a datum at either position and both triggers
  enumerate the same pair, so half of a join rule's firings rebuild a conclusion the
  other half already placed.  Ordering the agenda's datums lets one of the two skip the
  work.  Everything here is the claim that skipping it costs nothing: the firing that
  survives is the same firing, so the derived sentexes and their justifications are
  identical to a run with `chain/*suppress-duplicate-firings*` bound false, which is
  the reference this file compares against.

  The cases are the ones where a firing is enumerable at one trigger and not at the
  other, since that is the whole of what could go wrong: a whole store **seeded** onto
  one agenda in no particular order, a fact **revived** from OUT after its partner
  arrived, a fact put **back** on the agenda under an edge the run derived, a
  **disbelieved** trigger no join can find, an antecedent the join reaches through the
  symmetric **mirror** where the trigger cannot follow, and a fact filling **two
  positions** of one rule."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.protocols :as p]
            [vaelii.test-util :as tu]))

(defn- fixpoint-content
  "The KB's whole derived state, handle-free and sorted: every stored sentex as
  [sentence context truth strength believed?], every justification with its
  consequence, informant and antecedents mapped from handles to [sentence context]."
  [kb]
  (let [recs (:records kb)
        tms  (:tms kb)
        sent (fn [h] (let [s (p/get-sentex recs h)] [(:sentence s) (:context s)]))]
    {:sentexes
     (sort-by pr-str
              (map (fn [id]
                     (let [s (p/get-sentex recs id)]
                       [(:sentence s) (:context s) (:truth s) (:strength s)
                        (boolean (jtms/in? tms id))]))
                   (p/sentex-ids recs)))
     :justifications
     (sort-by pr-str
              (map (fn [j]
                     [(sent (:consequence j))
                      (if (integer? (:informant j)) (sent (:informant j)) (:informant j))
                      (set (map sent (:antecedents j)))
                      (:strength j)])
                   (jtms/justifications tms)))}))

(defn- both-ways
  "Run `load!` on a fresh KB with the suppression on and again with it off, and return
  `[suppressed reference]` fixpoint contents."
  [load!]
  (mapv (fn [suppress?]
          (tu/with-cleared-kb [kb tu/fresh]
            (binding [chain/*suppress-duplicate-firings* suppress?]
              (load! kb))
            (fixpoint-content kb)))
        [true false]))

(defn- agree [[suppressed reference] what]
  (testing what
    (is (= (:sentexes reference) (:sentexes suppressed))
        "the suppressed run stored something else")
    (is (= (:justifications reference) (:justifications suppressed))
        "the suppressed run supported it differently")))

;; ---- the seeding case ---------------------------------------------------
;; `forward-chain` puts every in-datum on one agenda, so both sides of every pair are
;; processed in the same run and the arrival order is whatever `jtms/in-datums`
;; produced — the case where arrival order and handle order are least alike.

(deftest a-seeded-store-derives-what-the-reference-derives
  (tu/with-terms [linksTo leadsTo reaches nearBy spans A B C D StoryContext]
    (let [load! (fn [kb]
                  (doseq [f [(list linksTo A B) (list leadsTo B C)
                             (list linksTo A D) (list leadsTo D C)
                             (list nearBy C C)]]
                    (v/assert kb f StoryContext {:chain? false}))
                  (v/assert-rule kb [(list linksTo '?a '?m) (list leadsTo '?m '?b)]
                                 (list reaches '?a '?b) StoryContext
                                 {:direction :forward :chain? false})
                  (v/assert-rule kb [(list reaches '?a '?m) (list nearBy '?m '?b)]
                                 (list spans '?a '?b) StoryContext
                                 {:direction :forward :chain? false})
                  (v/forward-chain kb))]
      (agree (both-ways load!) "a whole store seeded onto one agenda")
      (tu/with-cleared-kb [kb tu/fresh]
        (load! kb)
        (let [h1 (kb/find-sentex-handle kb (list reaches A C) StoryContext)
              h2 (kb/find-sentex-handle kb (list spans A C) StoryContext)]
          (is (some? h1) "the two-witness conclusion is derived")
          (is (some? h2) "and carries the rule above it")
          (is (= 2 (count (jtms/supports (:tms kb) h1)))
              "one justification per distinct witness — suppression drops neither")
          (is (= 1 (count (jtms/supports (:tms kb) h2)))
              "and exactly one where there is one witness"))))))

;; ---- a fact that fills two positions of one rule ------------------------

(deftest a-self-join-and-a-four-antecedent-rule-agree-with-the-reference
  (tu/with-terms [linksTo reaches pa qa ra sa chain4 P Q R S T StoryContext]
    (agree
     (both-ways
      (fn [kb]
        ;; transitive closure over a graph with a self-loop, so one `reaches` fact
        ;; satisfies both antecedents of the recursive rule at once
        (doseq [f [(list linksTo P Q) (list linksTo Q R) (list linksTo R R)]]
          (v/assert kb f StoryContext {:chain? false}))
        (v/assert-rule kb [(list linksTo '?a '?b)] (list reaches '?a '?b)
                       StoryContext {:direction :forward :chain? false})
        (v/assert-rule kb [(list reaches '?a '?m) (list reaches '?m '?b)]
                       (list reaches '?a '?b) StoryContext
                       {:direction :forward :chain? false})
        ;; four antecedents, so the rule is covered by a test rather than by the
        ;; argument that it generalizes
        (doseq [f [(list pa P Q) (list pa P R) (list qa Q R) (list qa R S)
                   (list ra R S) (list ra S T) (list sa S T) (list sa T P)]]
          (v/assert kb f StoryContext {:chain? false}))
        (v/assert-rule kb [(list pa '?w '?x) (list qa '?x '?y)
                           (list ra '?y '?z) (list sa '?z '?v)]
                       (list chain4 '?w '?v) StoryContext
                       {:direction :forward :chain? false})
        (v/forward-chain kb)))
     "a self-join and a four-antecedent join")))

;; ---- an antecedent the join reaches through the mirror ------------------
;; `res/match-pattern` probes both argument orders for a symmetric predicate; the
;; trigger match (`res/match1`) is a plain unify and does not.  So a mirrored hit is
;; a firing the join can make and the arriving datum cannot, and suppressing it would
;; hand the pair to a trigger that never produces it.

(deftest a-symmetric-non-trigger-antecedent-is-not-suppressed
  (tu/with-terms [nextTo holds nearHold A B P StoryContext]
    (let [load! (fn [kb]
                  (v/assert kb (list 'symmetric nextTo) StoryContext
                            {:strength :monotonic :chain? false})
                  ;; stored sorted, so `(nextTo B ?y)` only finds it by the mirror
                  (v/assert kb (list nextTo A B) StoryContext
                            {:strength :monotonic :chain? false})
                  (v/assert kb (list holds P B) StoryContext
                            {:strength :monotonic :chain? false})
                  (v/assert-rule kb [(list holds '?p '?x) (list nextTo '?x '?y)]
                                 (list nearHold '?p '?y) StoryContext
                                 {:direction :forward :chain? false})
                  (v/forward-chain kb))]
      (agree (both-ways load!) "a mirrored non-trigger antecedent")
      (tu/with-cleared-kb [kb tu/fresh]
        (load! kb)
        (is (seq (v/sentexes-matching kb (list nearHold P A) StoryContext))
            "the mirrored join still fires")))))

;; ---- an aggregate is per placement, downstream of the join --------------

(deftest an-aggregate-census-is-unmoved-by-a-suppressed-attempt
  (tu/with-terms [ownerOf worth richOwner P Q A B C StoryContext]
    (let [load! (fn [kb]
                  (doseq [f [(list ownerOf P A) (list ownerOf P B) (list ownerOf P C)
                             (list ownerOf Q A)
                             (list worth A 1) (list worth B 2) (list worth C 3)]]
                    (v/assert kb f StoryContext {:strength :monotonic :chain? false}))
                  ;; the count is taken per placement, over what is *stored*, so the
                  ;; trigger that made the firing cannot change it
                  (v/assert-rule kb [(list ownerOf '?p '?a)
                                     (list 'agg/count '?n '?v (list ownerOf '?p '?v))
                                     (list 'lessThan 2 '?n)]
                                 (list richOwner '?p) StoryContext
                                 {:direction :forward :chain? false})
                  (v/forward-chain kb))]
      (agree (both-ways load!) "an aggregate antecedent")
      (tu/with-cleared-kb [kb tu/fresh]
        (load! kb)
        (is (seq (v/sentexes-matching kb (list richOwner P) StoryContext))
            "the owner of three is rich")
        (is (empty? (v/sentexes-matching kb (list richOwner Q) StoryContext))
            "and the owner of one is not")))))

;; ---- the belief flip ----------------------------------------------------

(deftest a-revived-antecedent-re-enumerates-its-older-partner
  (tu/with-terms [pa qa ra X Y Z StoryContext]
    (let [conclusion (list ra X Y)
          load! (fn [kb]
                  (v/assert-rule kb [(list pa '?x '?z) (list qa '?z '?y)]
                                 (list ra '?x '?y) StoryContext {:direction :forward})
                  ;; a *default*, so a monotonic negation can take it OUT
                  (v/assert kb (list pa X Z) StoryContext)
                  (let [defeater (v/assert kb (list 'not (list pa X Z)) StoryContext
                                           {:strength :monotonic})]
                    (is (empty? (v/sentexes-matching kb (list pa X Z) StoryContext))
                        "the first antecedent is OUT")
                    ;; the partner arrives while the first antecedent is not believed,
                    ;; so nothing joins and no justification is ever recorded
                    (v/assert kb (list qa Z Y) StoryContext {:strength :monotonic})
                    (is (empty? (v/sentexes-matching kb conclusion StoryContext))
                        "an OUT antecedent licenses no firing")
                    ;; The retraction is the whole of it: lifting the defeat revives the
                    ;; antecedent, and the settle puts it back on the agenda itself
                    ;; (`settle/revived-seeds`).  No explicit `forward-chain` here, and
                    ;; that absence is the test — the arrival ordering below has to hold
                    ;; on the run a settle starts, not only on one a caller asks for.
                    (v/retract! kb defeater)
                    (is (seq (v/sentexes-matching kb (list pa X Z) StoryContext))
                        "the defeated antecedent revived")))]
      (tu/with-cleared-kb [kb tu/fresh]
        (load! kb)
        ;; the revived fact carries the *older* handle of the pair, so the run that
        ;; re-derives from it has to order on arrival rather than on the handle, or the
        ;; partner is filtered out from under it and this is empty
        (is (seq (v/sentexes-matching kb conclusion StoryContext))
            "the settle's own re-seed derives the conclusion")
        (let [h (kb/find-sentex-handle kb conclusion StoryContext)]
          (is (= 1 (count (jtms/supports (:tms kb) h)))
              "on exactly one justification, naming both antecedents")
          (is (= #{[(list pa X Z) StoryContext] [(list qa Z Y) StoryContext]}
                 (into #{}
                       (comp (map #(jtms/justification (:tms kb) %))
                             (mapcat :antecedents)
                             (keep #(p/get-sentex (:records kb) %))
                             (remove :antecedent)      ; the rule handle is in there too
                             (map (juxt :sentence :context)))
                       (jtms/supports (:tms kb) h)))
              "and those antecedents are the two facts")))
      (agree (both-ways load!) "an assert/defeat/undefeat sequence"))))

;; ---- a datum put back on the agenda -------------------------------------

(deftest a-re-enqueued-datum-outranks-what-the-run-already-processed
  ;; A `genl` edge derived mid-run makes a stored fact matchable at a supertype it did
  ;; not have, and `special/subsumption-seeds` puts that fact back on the agenda.  Its
  ;; partner may already have been processed, at a time when nothing connected the two,
  ;; so the re-enqueued datum has to **outrank** it — which is why the order is the
  ;; run's arrival order rather than the creation order the handles carry.  Ordered by
  ;; handle this conclusion is lost, and belief would depend on assertion order, which
  ;; is the one thing it may not do (docs/nmtms.md).
  (tu/with-terms [qa outp marked super_b sub_a X Y StoryContext]
    (tu/with-cleared-kb [kb tu/fresh]
      (let [opts  {:strength :monotonic :chain? false}
            h-sub (v/assert kb (list sub_a X) StoryContext opts)
            h-qa  (v/assert kb (list qa X Y) StoryContext opts)
            h-mrk (v/assert kb (list marked sub_a) StoryContext opts)]
        (v/assert-rule kb [(list marked '?a)] (list 'genl '?a super_b)
                       StoryContext {:direction :forward :chain? false})
        (v/assert-rule kb [(list super_b '?u) (list qa '?u '?y)] (list outp '?u '?y)
                       StoryContext {:direction :forward :chain? false})
        ;; the seed order is the point: the partner is processed before any edge
        ;; connects it to anything, and the marker that derives the edge comes last
        (chain/chain-all kb [h-sub h-qa h-mrk] nil)
        (is (seq (v/sentexes-matching kb (list 'genl sub_a super_b) StoryContext))
            "the edge was derived mid-run")
        (is (seq (v/sentexes-matching kb (list outp X Y) StoryContext))
            "and the fact it newly subsumed re-joined its already-processed partner")))))

;; ---- a trigger nothing else can find ------------------------------------

(deftest a-disbelieved-trigger-suppresses-nothing
  ;; A datum triggers on `res/match1`, a plain unify; the join finds facts through
  ;; `*matcher*`, which follows belief.  So a spelling superseded by an equality merge
  ;; still fires its rules while no other trigger's join can reach it — and its
  ;; combinations, being enumerable there and nowhere else, all have to be made there.
  (tu/with-terms [bestFriendOf parentOf grandparentOf A B C StoryContext]
    (let [load! (fn [kb]
                  (v/assert kb (list 'functional bestFriendOf) StoryContext
                            {:strength :monotonic :chain? false})
                  (v/assert-rule kb [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                                 (list grandparentOf '?x '?z) StoryContext
                                 {:direction :forward :chain? false})
                  ;; two values of a functional predicate merge B into A, so the
                  ;; spelling written next is superseded the moment it is stored
                  (v/assert kb (list bestFriendOf C A) StoryContext {:strength :monotonic})
                  (v/assert kb (list bestFriendOf C B) StoryContext {:strength :monotonic})
                  (v/assert kb (list parentOf B A) StoryContext {:strength :monotonic}))]
      (agree (both-ways load!) "a superseded spelling as the trigger")
      (tu/with-cleared-kb [kb tu/fresh]
        (load! kb)
        (let [h (kb/find-sentex-handle kb (list parentOf B A) StoryContext)]
          (is (some? h) "the written spelling is stored")
          (is (not (v/in? kb h)) "and superseded by the merge, so no join finds it")
          (is (seq (v/sentexes-matching kb (list grandparentOf B A) StoryContext))
              "yet it still fires, joined against the spelling that replaced it"))))))

;; ---- retraction and re-derivation ---------------------------------------

(deftest retracting-one-witness-leaves-the-conclusion-on-the-other
  (tu/with-terms [linksTo leadsTo reaches A B C D StoryContext]
    (tu/with-cleared-kb [kb tu/fresh]
      (v/assert-rule kb [(list linksTo '?a '?m) (list leadsTo '?m '?b)]
                     (list reaches '?a '?b) StoryContext
                     {:direction :forward :chain? false})
      (doseq [f [(list linksTo A B) (list leadsTo B C)
                 (list linksTo A D) (list leadsTo D C)]]
        (v/assert kb f StoryContext {:strength :monotonic :chain? false}))
      (v/forward-chain kb)
      (let [h (kb/find-sentex-handle kb (list reaches A C) StoryContext)]
        (is (= 2 (count (jtms/supports (:tms kb) h))) "two witnesses to begin with")
        (v/retract! kb (kb/find-sentex-handle kb (list leadsTo B C) StoryContext))
        (is (seq (v/sentexes-matching kb (list reaches A C) StoryContext))
            "the conclusion stands on the witness that is left")
        (is (= 1 (count (jtms/supports (:tms kb)
                                       (kb/find-sentex-handle kb (list reaches A C)
                                                              StoryContext))))
            "on one justification")))))

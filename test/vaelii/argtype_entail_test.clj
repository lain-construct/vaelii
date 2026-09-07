;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.argtype-entail-test
  "Assertive argument types: `(arg parentOf 1 animal)` read as an entailment about
  the argument, not only as a constraint on it.

  The check's open-world floor is what this fills — an argument with no visible place
  in the genl hierarchy cannot violate anything, so it passes and the KB learns
  nothing, however many times it has been told that the slot holds an animal.  The
  entailment is drawn exactly there and nowhere else, and it is drawn as a **derived,
  justified** sentex: retract the fact or the declaration and the type goes with it.

  Off by default (`checks/*assertive-arg-types?*`), so every test here binds it."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defmacro with-entailing
  "Run the body with assertive argument types on."
  [& body]
  `(binding [checks/*assertive-arg-types?* true] ~@body))

(defmacro without-entailing
  "Run the body with them off — bound rather than assumed, since the root value is
  what `VAELII_ASSERTIVE_ARG_TYPES` sets to run the whole suite under the feature."
  [& body]
  `(binding [checks/*assertive-arg-types?* false] ~@body))

(defn- a-type
  "Declare `t` a type — an edge to `thing`, which is what makes a membership in it
  mintable at all."
  [kb t ctx]
  (v/assert kb (list 'genl t 'thing) ctx))

(defn- a-context
  "Hang `ctx` under CxUniverse, so what is declared universally is visible from
  it.  A `fresh` KB has no spindle, and a context wired to nothing sees nothing —
  which would make every argument outside the hierarchy and every test here trivially
  true."
  [kb ctx]
  (v/assert kb (list 'genlCx ctx 'CxUniverse) 'CxUniverse))

(defn- entailed
  "The handle of the **stored, believed** sentex for `sentence` in `ctx`, or nil.

  Deliberately not `ask`.  `provers/ArgTypeProver` already answers a ground
  `(Type Individual)` goal off the very declaration under test — arg read as an
  inference is not what is new here.  What is new is that the type becomes a
  **record**: a handle, a justification naming what it rests on, a place in the
  taxonomy that `isa?` and the definitional checks read, and a datum the agenda can
  fire rules on.  A prover's answer is none of those, and a test that asked one could
  not tell the two apart."
  [kb sentence ctx]
  (let [h (v/handle-of kb sentence ctx)]
    (when (and h (v/in? kb h)) h)))

(defn- believed? [kb sentence ctx] (some? (entailed kb sentence ctx)))

;; ---- the headline --------------------------------------------------------

(tu/deftest-kb a-declaration-entails-the-type-it-constrains
  (tu/with-terms [animal parentOf Fred Mary CxWorld]
    (a-context kb CxWorld)
    (a-type kb animal CxWorld)
    (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
    (testing "with the entailment off, the constraint passes and stores nothing"
      (without-entailing
       (v/assert kb (list parentOf Fred Mary) CxWorld)
       (is (not (believed? kb (list animal Fred) CxWorld)))
       (is (not (v/isa? kb Fred animal CxWorld))
           "and the taxonomy has not learned what the declaration says")
       (is (empty? (v/types-of kb Fred CxWorld)))))
    (v/retract! kb (v/handle-of kb (list parentOf Fred Mary) CxWorld))
    (with-entailing
      (v/assert kb (list parentOf Fred Mary) CxWorld)
      (testing "with it on, the type is a stored, believed datum"
        (is (believed? kb (list animal Fred) CxWorld)))
      (testing "so the taxonomy — and everything reading it — now says so"
        (is (v/isa? kb Fred animal CxWorld))
        (is (= [animal] (vec (v/types-of kb Fred CxWorld)))))
      (testing "and the second argument, which nothing constrains, is untouched"
        (is (not (believed? kb (list animal Mary) CxWorld)))))))

(tu/deftest-kb why-names-the-fact-and-the-declaration
  (tu/with-terms [animal parentOf Fred Mary CxWorld]
    (a-type kb animal CxWorld)
    (a-context kb CxWorld)
    (let [dh (v/assert kb (list 'arg parentOf 1 animal) CxWorld)]
      (with-entailing
        (let [fh (v/assert kb (list parentOf Fred Mary) CxWorld)
              th (v/handle-of kb (list animal Fred) CxWorld)
              w  (v/why kb th)
              sup (first (:support w))]
          (is (some? th) "the type is stored")
          (is (false? (:premise? w)) "and derived, not asserted")
          (is (= 'arg (:informant sup)) "the declaring predicate is the informant")
          (is (= #{fh dh} (set (map :handle (:because sup))))
              "resting on the triggering fact and the declaration, and nothing else"))))))

;; ---- both directions reach one KB ---------------------------------------

(tu/deftest-kb a-declaration-reaches-the-facts-already-stored
  (tu/with-terms [animal parentOf Fred Mary Ann Bob CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (v/assert kb (list parentOf Fred Mary) CxWorld)
      (v/assert kb (list parentOf Ann Bob) CxWorld)
      (is (not (believed? kb (list animal Fred) CxWorld))
          "nothing is entailed while nothing is declared")
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (testing "the declaration arriving last reaches every fact already stored"
        (is (believed? kb (list animal Fred) CxWorld))
        (is (believed? kb (list animal Ann) CxWorld))))))

(tu/deftest-kb the-two-arrival-orders-reach-the-same-belief
  ;; the gate: declaration-then-fact and fact-then-declaration are the same knowledge
  (doseq [order [:declaration-first :facts-first]]
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [animal parentOf Fred Mary CxWorld]
        (with-entailing
          (a-context kb CxWorld)
          (a-type kb animal CxWorld)
          (let [decl #(v/assert kb (list 'arg parentOf 1 animal) CxWorld)
                fact #(v/assert kb (list parentOf Fred Mary) CxWorld)]
            (if (= order :declaration-first) (do (decl) (fact)) (do (fact) (decl))))
          (is (believed? kb (list animal Fred) CxWorld)
              (str "entailed under " (name order)))
          (is (= 1 (count (:support (v/why kb (v/handle-of kb (list animal Fred)
                                                           CxWorld)))))
              (str "with one justification under " (name order))))))))

;; ---- the type is held by its supporters ---------------------------------

(tu/deftest-kb retracting-either-supporter-takes-the-type-back
  (doseq [drop [:the-fact :the-declaration]]
    (tu/with-neutral-kb [kb tu/fresh]
      (tu/with-terms [animal parentOf Fred Mary CxWorld]
        (with-entailing
          (a-context kb CxWorld)
          (a-type kb animal CxWorld)
          (let [dh (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
                fh (v/assert kb (list parentOf Fred Mary) CxWorld)]
            (is (believed? kb (list animal Fred) CxWorld))
            (v/retract! kb (if (= drop :the-fact) fh dh))
            (is (not (believed? kb (list animal Fred) CxWorld))
                (str "the type goes when " (name drop) " goes"))
            (is (nil? (v/handle-of kb (list animal Fred) CxWorld))
                "swept, not merely disbelieved — its only justification is invalid")))))))

(tu/deftest-kb a-type-survives-while-anything-supports-it
  (tu/with-terms [animal parentOf childOf Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (v/assert kb (list 'arg childOf 1 animal) CxWorld)
      (let [fh (v/assert kb (list parentOf Fred Mary) CxWorld)]
        (v/assert kb (list childOf Fred Mary) CxWorld)
        (is (believed? kb (list animal Fred) CxWorld))
        (testing "two independent facts entail it; dropping one leaves the other"
          (v/retract! kb fh)
          (is (believed? kb (list animal Fred) CxWorld)))))))

(tu/deftest-kb defeating-the-fact-takes-the-type-out-with-it
  (tu/with-terms [animal parentOf Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld {:strength :monotonic})
      (v/assert kb (list parentOf Fred Mary) CxWorld)
      (is (believed? kb (list animal Fred) CxWorld))
      ;; a known-true negation defeats the default fact; the type is derived from it,
      ;; so belief follows without anything arranging for it
      (v/assert kb (list 'not (list parentOf Fred Mary)) CxWorld
                {:strength :monotonic})
      (is (not (believed? kb (list animal Fred) CxWorld))
          "the minted type follows the belief of what it rests on"))))

;; ---- where it does *not* mint -------------------------------------------

(tu/deftest-kb an-inherited-declaration-constrains-but-does-not-spray
  (tu/with-terms [animal rock parentOf Fred Mary Rex CxSchema CxStory]
    (with-entailing
      (a-type kb animal 'CxUniverse)
      (a-type kb rock 'CxUniverse)
      (a-context kb CxSchema)
      (v/assert kb (list 'genlCx CxStory CxSchema) 'CxUniverse)
      (v/assert kb (list 'arg parentOf 1 animal) CxSchema)
      (v/assert kb (list parentOf Fred Mary) CxStory)
      (testing "the ancestor's declaration entails nothing in the descendant"
        (is (not (believed? kb (list animal Fred) CxStory)))
        (is (nil? (v/handle-of kb (list animal Fred) CxStory))))
      (testing "but it still constrains there — an argument of the wrong type is refused"
        (v/assert kb (list rock Rex) CxStory)
        (v/assert kb (list 'disjoint animal rock) 'CxUniverse)
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list parentOf Rex Mary) CxStory))))
      (testing "and the same declaration written locally does entail"
        (v/assert kb (list 'arg parentOf 1 animal) CxStory)
        (is (believed? kb (list animal Fred) CxStory))))))

(tu/deftest-kb a-disjoint-argument-is-convicted-rather-than-minted
  (tu/with-terms [animal rock parentOf Rex Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (a-type kb rock CxWorld)
      (v/assert kb (list 'disjoint animal rock) CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (v/assert kb (list rock Rex) CxWorld)
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"arg constraint"
                            (v/assert kb (list parentOf Rex Mary) CxWorld))
          "the existing :arg-type refusal, not a minted contradiction")
      (is (nil? (v/handle-of kb (list animal Rex) CxWorld))
          "and no type was minted on the way to the refusal"))))

(tu/deftest-kb one-sentex-however-many-declarations-entail-it
  ;; Deduplication is by content, and only by content: one record for the sentence, one
  ;; justification per (fact, declaration) pair.  Nothing is withheld because the type
  ;; was already reachable — see `checks/constraint-entailments` for why any such
  ;; narrowing would make the answer depend on arrival order.
  (tu/with-terms [animal parentOf childOf Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (v/assert kb (list 'arg childOf 1 animal) CxWorld)
      (v/assert kb (list parentOf Fred Mary) CxWorld)
      (v/assert kb (list childOf Fred Mary) CxWorld)
      (is (= 1 (count (v/sentexes-with-functor kb animal))) "one record")
      (is (= 2 (count (:support (v/why kb (entailed kb (list animal Fred) CxWorld)))))
          "two justifications — each fact holds it up on its own"))))

(tu/deftest-kb a-subsuming-membership-does-not-suppress-the-entailment
  ;; The stance, stated as a test: `(dog Muffet)` under `(genl dog animal)` already
  ;; *reaches* `animal` by subsumption, and the entailment is drawn anyway.  Withholding
  ;; it would mean the same three sentences produce different records depending on
  ;; whether the subtype membership arrived first.
  (tu/with-terms [animal dog parentOf Muffet Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (v/assert kb (list 'genl dog animal) CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (v/assert kb (list dog Muffet) CxWorld)
      (v/assert kb (list parentOf Muffet Mary) CxWorld)
      (is (believed? kb (list animal Muffet) CxWorld))
      (testing "and it is derived, so retracting the fact takes it back"
        (v/retract! kb (v/handle-of kb (list parentOf Muffet Mary) CxWorld))
        (is (nil? (v/handle-of kb (list animal Muffet) CxWorld)))
        (is (v/isa? kb Muffet animal CxWorld)
            "while subsumption, which never needed the record, still answers")))))

(tu/deftest-kb a-query-mints-nothing
  (tu/with-terms [animal parentOf Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (let [before (tu/content-count kb)]
        (v/ask kb (list parentOf Fred Mary) CxWorld)
        (v/ask kb (list animal Fred) CxWorld)
        (v/sentexes-matching kb (list parentOf '?x '?y) CxWorld)
        (is (= before (tu/content-count kb)) "asking is not telling")
        (is (nil? (v/handle-of kb (list animal Fred) CxWorld)))))))

(tu/deftest-kb an-undeclared-type-is-not-minted
  ;; the pure-native form of "structural types are reject-only": a name the hierarchy
  ;; does not hold is not a type we invent a membership in
  (tu/with-terms [parentOf Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (v/assert kb (list 'arg parentOf 1 'integer) CxWorld)
      (v/assert kb (list parentOf Fred Mary) CxWorld)
      (is (nil? (v/handle-of kb (list 'integer Fred) CxWorld))))))

;; ---- the minted type is ordinary content --------------------------------

(tu/deftest-kb a-minted-type-is-a-chaining-seed
  (tu/with-terms [animal mortal parentOf Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (a-type kb mortal CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (v/assert-rule kb [(list animal '?x)] (list mortal '?x) CxWorld)
      (testing "the rule fires off the minted type within the same assert"
        (v/assert kb (list parentOf Fred Mary) CxWorld)
        (is (believed? kb (list mortal Fred) CxWorld))))))

(tu/deftest-kb the-cascade-closes
  ;; A declaration whose own conclusion is constrained: `(rel …)` mints `(t1 x)`, `t1`'s
  ;; own declaration mints `(t2 x)`, and t2's points back at t1 — which is already
  ;; there.  It has to cascade (the retroactive direction does, so the forward one must
  ;; agree), and it has to stop: every mint is find-or-create and every justification is
  ;; content-keyed, so the cycle has nothing new to produce on the second lap.
  (tu/with-terms [t1 t2 rel Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb t1 CxWorld)
      (a-type kb t2 CxWorld)
      (v/assert kb (list 'arg rel 1 t1) CxWorld)
      (v/assert kb (list 'arg t1 1 t2) CxWorld)
      (v/assert kb (list 'arg t2 1 t1) CxWorld)
      (v/assert kb (list rel Fred Mary) CxWorld)
      (is (believed? kb (list t1 Fred) CxWorld))
      (is (believed? kb (list t2 Fred) CxWorld))
      (is (= 1 (count (v/sentexes-with-functor kb t1)))
          "one sentex per type, however many times the cycle is traversed"))))

(tu/deftest-kb the-cascade-crosses-an-argument-that-already-holds-a-type
  ;; The cascade closed only for an argument with no type at all until the symbol arm
  ;; yielded: the mint `(t1 Fred)` re-entered the check, `t1`'s own declaration read Fred
  ;; as typed-and-not-a-`t2`, and the conclusion `(t2 Fred)` would have come from was
  ;; dropped.  `dog` is neither a `t1` nor a `t2` and is disjoint from neither, so under
  ;; the entailment reading it is no obstacle to either mint.
  (tu/with-terms [t1 t2 dog rel Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb t1 CxWorld)
      (a-type kb t2 CxWorld)
      (a-type kb dog CxWorld)
      (v/assert kb (list 'arg rel 1 t1) CxWorld)
      (v/assert kb (list 'arg t1 1 t2) CxWorld)
      (v/assert kb (list dog Fred) CxWorld)
      (v/assert kb (list rel Fred Mary) CxWorld)
      (is (believed? kb (list t1 Fred) CxWorld) "the first link")
      (is (believed? kb (list t2 Fred) CxWorld) "and the second, off the first")
      (testing "each link rests on the one before it, so retracting the fact takes both"
        (v/retract! kb (v/handle-of kb (list rel Fred Mary) CxWorld))
        (is (nil? (v/handle-of kb (list t1 Fred) CxWorld)))
        (is (nil? (v/handle-of kb (list t2 Fred) CxWorld)))))))

(tu/deftest-kb a-unary-declaration-entails-what-genl-would-and-re-asserts-cleanly
  ;; `(arg p1 1 p2)` on a *unary* predicate says what `(genl p1 p2)` says, and the
  ;; conviction reading could not hold it: `(p1 Fred)` types Fred a `p1`, so the identical
  ;; assertion a second time convicted Fred for not being a `p2` — a sentence refused by
  ;; the fact it had itself created.  The entailment reading mints the `p2` instead, which
  ;; is what makes the second assert the no-op it has to be.
  (tu/with-terms [p1 p2 Fred CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb p1 CxWorld)
      (a-type kb p2 CxWorld)
      (v/assert kb (list 'arg p1 1 p2) CxWorld)
      (let [h (v/assert kb (list p1 Fred) CxWorld)]
        (is (believed? kb (list p2 Fred) CxWorld) "the type the declaration entails")
        (is (= h (v/assert kb (list p1 Fred) CxWorld))
            "and the same sentence again is the same handle, not a refusal")))))

(tu/deftest-kb a-mint-the-kb-cannot-hold-refuses-the-fact-that-entails-it
  ;; The refusal the symbol arm used to carry, moved one step along the derivation: Bert is
  ;; a `rock`, `rock` and `animal` are disjoint, and the fact is refused for the mint it
  ;; draws rather than for the type its argument lacks.  What must not happen is the third
  ;; possibility — storing the fact and dropping the mint, which leaves the KB believing a
  ;; fact whose declared consequence it rejects.
  (tu/with-terms [animal rock parentOf Bert Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb animal CxWorld)
      (a-type kb rock CxWorld)
      (v/assert kb (list 'disjoint animal rock) CxWorld)
      (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
      (v/assert kb (list rock Bert) CxWorld)
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cannot be admitted"
                            (v/assert kb (list parentOf Bert Mary) CxWorld)))
      (is (nil? (v/handle-of kb (list parentOf Bert Mary) CxWorld))
          "the fact is not stored")
      (is (nil? (v/handle-of kb (list animal Bert) CxWorld))
          "nor the mint that refused it"))))

(tu/deftest-kb a-clash-between-the-fact-and-its-own-mint-refuses
  ;; Neither side of this pair is stored when the check runs: `(p1 Fred)` is the sentence
  ;; being asserted and `(p2 Fred)` is what it entails.  `disjoint-problems` names an
  ;; opposing *handle*, so it cannot see a clash with no second record —
  ;; `checks/cascade-clash` is the arm that reads the cascade's own memberships as content.
  (tu/with-terms [p1 p2 Fred CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb p1 CxWorld)
      (a-type kb p2 CxWorld)
      (v/assert kb (list 'disjoint p1 p2) CxWorld)
      (v/assert kb (list 'arg p1 1 p2) CxWorld)
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cannot be admitted"
                            (v/assert kb (list p1 Fred) CxWorld)))
      (is (empty? (v/types-of kb Fred CxWorld)) "and Fred is left with no type at all"))))

(tu/deftest-kb a-clash-between-two-mints-of-one-cascade-refuses
  ;; Both sides come from the cascade this time, two links apart, and the triggering fact
  ;; is a binary relation that types nothing itself.  The check has to walk the whole
  ;; cascade to see it: one level down, `(t1 Fred)` is admissible.
  (tu/with-terms [t1 t2 rel Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb t1 CxWorld)
      (a-type kb t2 CxWorld)
      (v/assert kb (list 'disjoint t1 t2) CxWorld)
      (v/assert kb (list 'arg rel 1 t1) CxWorld)
      (v/assert kb (list 'arg t1 1 t2) CxWorld)
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cannot be admitted"
                            (v/assert kb (list rel Fred Mary) CxWorld)))
      (is (nil? (v/handle-of kb (list rel Fred Mary) CxWorld))))))

(tu/deftest-kb an-inherited-declaration-still-convicts
  ;; The yield is `arg-entailments`' condition term for term, and `declares-locally?` is
  ;; one of them: a declaration written in an ancestor context constrains a descendant
  ;; without minting there.  So in the descendant the constraint reading is the only
  ;; reading there is, and it convicts as it always did.
  (tu/with-terms [animal rock parentOf Bert Mary CxUp CxDown]
    (with-entailing
      (v/assert kb (list 'genlCx CxUp 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxDown CxUp) 'CxUniverse)
      (a-type kb animal CxUp)
      (a-type kb rock CxUp)
      (v/assert kb (list 'arg parentOf 1 animal) CxUp)
      (v/assert kb (list rock Bert) CxDown)
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"must be a"
                            (v/assert kb (list parentOf Bert Mary) CxDown)))
      (is (nil? (v/handle-of kb (list animal Bert) CxDown))))))

(tu/deftest-kb an-inadmissible-entailment-refuses-the-assert
  ;; `(t Rex)` is what the declaration entails, and `t` is declared binary — so the
  ;; entailment is a sentence the KB cannot hold.  The entry point refuses the fact that
  ;; entails it, because with the entailment on the declaration is a definition: admitting
  ;; `(rel Rex Mary)` is admitting `(t Rex)`.  Asked by `checks/entailment-check` before
  ;; anything is written, so the refusal leaves nothing behind — the materializer's own
  ;; test runs after the triggering sentex is stored, and dropping the mint there would
  ;; leave the KB believing a fact whose declared consequence it rejects.
  (tu/with-terms [t rel Rex Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb t CxWorld)
      (v/assert kb (list 'binary_predicate t) CxWorld)
      (v/assert kb (list 'arg rel 1 t) CxWorld)
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"arg constraint"
                            (v/assert kb (list rel Rex Mary) CxWorld))
          "refused for what it entails, not for what it says")
      (is (nil? (v/handle-of kb (list rel Rex Mary) CxWorld))
          "and the fact is not stored")
      (is (nil? (v/handle-of kb (list t Rex) CxWorld))
          "nor the entailment that refused it")))
  (testing "with the entailment off, the constraint reading admits it — Rex is untyped"
    (tu/with-terms [t rel Rex Mary CxWorld]
      (without-entailing
       (a-context kb CxWorld)
       (a-type kb t CxWorld)
       (v/assert kb (list 'binary_predicate t) CxWorld)
       (v/assert kb (list 'arg rel 1 t) CxWorld)
       (is (some? (v/assert kb (list rel Rex Mary) CxWorld)))))))

(tu/deftest-kb an-inadmissible-entailment-on-the-derivation-path-is-reported-not-thrown
  ;; The same declaration, reached by a rule firing instead of by a caller.  Here the
  ;; entailment is **recorded** and the conclusion stands: forward chaining has no caller
  ;; to refuse, and a firing that threw mid-fixpoint would leave belief half-computed.
  ;; The split is the one `constraint-checks` and `constraint-admission` already draw for
  ;; every other check — the entry point refuses, the derivation path reports.
  (tu/with-terms [t rel trigger Rex Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb t CxWorld)
      (v/assert kb (list 'binary_predicate t) CxWorld)
      (v/assert kb (list 'arg rel 1 t) CxWorld)
      (v/assert-rule kb [(list trigger '?x '?y)] (list rel '?x '?y) CxWorld)
      (v/clear-violations! kb)
      (v/assert kb (list trigger Rex Mary) CxWorld)
      (is (some? (v/handle-of kb (list rel Rex Mary) CxWorld))
          "the conclusion stands")
      (is (nil? (v/handle-of kb (list t Rex) CxWorld))
          "and the entailment it could not admit was not stored")
      (let [vs (v/violations kb)]
        (is (some #(and (= :arity (:violation %)) (= (list t Rex) (:sentence %))) vs)
            (str "reported in the ledger: " (pr-str vs)))))))

(tu/deftest-kb a-declaration-arriving-over-stored-facts-closes-the-whole-chain
  ;; The retroactive direction has to reach as far as the forward one, or which order the
  ;; three declarations arrived in decides how many links the KB ends up holding.
  ;; `entail-existing` walks the stored facts and each mint draws its own entailments, so
  ;; the chain closes from either end.
  (tu/with-terms [t1 t2 t3 rel Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb t1 CxWorld)
      (a-type kb t2 CxWorld)
      (a-type kb t3 CxWorld)
      (v/assert kb (list rel Fred Mary) CxWorld)
      (v/assert kb (list 'arg t1 1 t2) CxWorld)
      (v/assert kb (list 'arg t2 1 t3) CxWorld)
      (v/assert kb (list 'arg rel 1 t1) CxWorld)
      (is (believed? kb (list t1 Fred) CxWorld))
      (is (believed? kb (list t2 Fred) CxWorld))
      (is (believed? kb (list t3 Fred) CxWorld) "the far end, reached by the last arrival"))))

(tu/deftest-kb retracting-a-middle-declaration-takes-the-link-below-it
  ;; Each link is justified by the link above it and its own declaration, so the cascade
  ;; comes apart where the support goes and nowhere else.
  (tu/with-terms [t1 t2 rel Fred Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb t1 CxWorld)
      (a-type kb t2 CxWorld)
      (v/assert kb (list 'arg rel 1 t1) CxWorld)
      (v/assert kb (list 'arg t1 1 t2) CxWorld)
      (v/assert kb (list rel Fred Mary) CxWorld)
      (is (believed? kb (list t2 Fred) CxWorld))
      (v/retract! kb (v/handle-of kb (list 'arg t1 1 t2) CxWorld))
      (is (nil? (v/handle-of kb (list t2 Fred) CxWorld)) "the link the declaration held")
      (is (believed? kb (list t1 Fred) CxWorld) "and only that one"))))

(tu/deftest-kb the-refusal-lands-on-arrival-and-does-not-reach-back
  ;; The `arg` family has no retroactive conviction — a declaration meeting facts already
  ;; stored mints over them and reports what it cannot mint, and refuses nothing
  ;; (docs/taxonomy.md's arrival-order table, entry_point_and_report_test's rows).  The
  ;; entailment reading inherits that shape rather than changing it, so which of the two
  ;; is refused is which one arrived second.  What does **not** vary is the entailment:
  ;; the mint is absent in both orders, so no reader is answered differently.
  (letfn [(run [order]
            (tu/with-neutral-kb [kb tu/fresh]
              (tu/with-terms [p_a p_b rel Bert Mary CxWorld]
                (with-entailing
                  (a-context kb CxWorld)
                  (a-type kb p_a CxWorld)
                  (a-type kb p_b CxWorld)
                  (v/assert kb (list 'disjoint p_a p_b) CxWorld)
                  (v/assert kb (list p_b Bert) CxWorld)
                  (doseq [step order]
                    (try
                      (case step
                        :decl (v/assert kb (list 'arg rel 1 p_a) CxWorld)
                        :fact (v/assert kb (list rel Bert Mary) CxWorld))
                      (catch clojure.lang.ExceptionInfo _ nil)))
                  {:fact  (some? (v/handle-of kb (list rel Bert Mary) CxWorld))
                   :decl  (some? (v/handle-of kb (list 'arg rel 1 p_a) CxWorld))
                   :mint  (some? (v/handle-of kb (list p_a Bert) CxWorld))}))))]
    (is (= {:fact false :decl true :mint false} (run [:decl :fact]))
        "the declaration first, and the fact it would convict is refused on the way in")
    (is (= {:fact true :decl true :mint false} (run [:fact :decl]))
        "the fact first, and the declaration reports the mint it cannot make")
    (is (= (:mint (run [:decl :fact])) (:mint (run [:fact :decl])))
        "the entailment reads the same either way, which is what belief may not vary on")))

(tu/deftest-kb a-clash-the-asserting-context-cannot-see-does-not-refuse
  ;; The refusal is scoped like every other read: the mint is tested against what the
  ;; asserting context sees, so a disjointness declared in a context this one does not
  ;; reach convicts nothing here.  A context is only ever refused on grounds it can see
  ;; (docs/contexts.md), and that holds of a refusal drawn one step along the derivation
  ;; exactly as it holds of one drawn on the sentence itself.
  (tu/with-terms [p_a p_b rel Bert Mary CxLeft CxRight]
    (with-entailing
      (v/assert kb (list 'genlCx CxLeft 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxRight 'CxUniverse) 'CxUniverse)
      (a-type kb p_a 'CxUniverse)
      (a-type kb p_b 'CxUniverse)
      (v/assert kb (list 'arg rel 1 p_a) 'CxUniverse)
      (v/assert kb (list p_b Bert) 'CxUniverse)
      (v/assert kb (list 'disjoint p_a p_b) CxLeft)
      (testing "the sibling that cannot see the disjointness admits the fact and mints"
        (is (some? (v/assert kb (list rel Bert Mary) CxRight)))
        (is (believed? kb (list p_a Bert) CxRight)))
      (testing "and the one that can see it refuses"
        (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cannot be admitted"
                              (v/assert kb (list rel Bert 'TmpOther) CxLeft)))))))

;; ---- genlArg -------------------------------------------------------------

(tu/deftest-kb genlArg-entails-a-genl-edge
  (tu/with-terms [physical_object partType wheel_kind axle_kind CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb physical_object CxWorld)
      (v/assert kb (list 'genlArg partType 1 physical_object) CxWorld)
      (v/assert kb (list partType wheel_kind axle_kind) CxWorld)
      (is (v/genl? kb wheel_kind physical_object)
          "the argument named a kind of physical object, and now the taxonomy says so")
      (testing "and the edge is held by its supporters like any other entailment"
        (v/retract! kb (v/handle-of kb (list partType wheel_kind axle_kind) CxWorld))
        (is (not (v/genl? kb wheel_kind physical_object)))))))

(tu/deftest-kb an-individual-in-an-genlArg-position-is-convicted-not-given-an-edge
  (tu/with-terms [physical_object partType Wheel axle_kind CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb physical_object CxWorld)
      (v/assert kb (list 'genlArg partType 1 physical_object) CxWorld)
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"never be a subtype"
                            (v/assert kb (list partType Wheel axle_kind) CxWorld)))
      (is (not (v/genl? kb Wheel physical_object))))))

;; ---- order independence --------------------------------------------------

(defn- permutations
  [coll]
  (if (< (count coll) 2)
    (list coll)
    (for [i (range (count coll))
          p (permutations (concat (take i coll) (drop (inc i) coll)))]
      (cons (nth coll i) p))))

(defn- believed-shape
  "The belief the three sentences leave, as a value order cannot vary."
  [kb animal dog parentOf Fred Mary ctx]
  {:animal (believed? kb (list animal Fred) ctx)
   :dog    (believed? kb (list dog Fred) ctx)
   :fact   (believed? kb (list parentOf Fred Mary) ctx)})

(tu/deftest-kb every-arrival-order-reaches-the-same-belief
  ;; the declaration, the fact, and a competing type the argument already holds —
  ;; in all six orders.  `dog` is under `animal`, so the competing type is what makes
  ;; the entailment redundant, and *when* it arrives must not decide whether the KB
  ;; ends up believing a minted `(animal Fred)` on top of it.
  (let [results
        (for [order (permutations [:decl :fact :type])]
          (tu/with-neutral-kb [kb tu/fresh]
            (tu/with-terms [animal dog parentOf Fred Mary CxWorld]
              (with-entailing
                (a-context kb CxWorld)
                (a-type kb animal CxWorld)
                (v/assert kb (list 'genl dog animal) CxWorld)
                (doseq [step order]
                  (case step
                    :decl (v/assert kb (list 'arg parentOf 1 animal) CxWorld)
                    :fact (v/assert kb (list parentOf Fred Mary) CxWorld)
                    :type (v/assert kb (list dog Fred) CxWorld)))
                [order (believed-shape kb animal dog parentOf Fred Mary CxWorld)]))))]
    (is (= 1 (count (set (map second results))))
        (str "belief varied by arrival order: " (pr-str results)))
    (is (every? (comp :animal second) results)
        "and every order believes the entailed type")))

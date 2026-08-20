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

(tu/deftest-kb an-inadmissible-entailment-is-reported-not-thrown
  ;; `(t Rex)` is what the declaration entails, and `t` is declared binary — so the
  ;; entailment fails a check of its own.  It is **recorded**, and the triggering assert
  ;; still succeeds: the materialization runs after the sentex is stored (that is what
  ;; gives it a handle to be justified against) and inside a fixpoint, and throwing from
  ;; either would leave the KB half-written or belief half-computed.  The same choice
  ;; `deduce-lift` makes for the copy it cannot admit.
  (tu/with-terms [t rel Rex Mary CxWorld]
    (with-entailing
      (a-context kb CxWorld)
      (a-type kb t CxWorld)
      (v/assert kb (list 'binaryPredicate t) CxWorld)
      (v/assert kb (list 'arg rel 1 t) CxWorld)
      (v/clear-violations! kb)
      (let [h (v/assert kb (list rel Rex Mary) CxWorld)]
        (is (some? h) "the assert stands")
        (is (v/in? kb h))
        (is (nil? (v/handle-of kb (list t Rex) CxWorld))
            "and the entailment it could not admit was not stored")
        (let [vs (v/violations kb)]
          (is (some #(and (= :arity (:violation %)) (= (list t Rex) (:sentence %))) vs)
              (str "reported in the ledger: " (pr-str vs))))))))

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

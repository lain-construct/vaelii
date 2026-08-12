;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.arggenl-test
  "`argGenl` — the argument constraint one level up.  Where `argIsa` asks an argument
  to be an *instance* of a type, `argGenl` asks it to be a *subtype*, which is what a
  `typeRelationPredicate` wants: its arguments name kinds, not things.

  Plus the checks over the declarations themselves — arity, and the two ways an
  `argIsa` / `argGenl` can contradict what the KB already says about its predicate.
  Declaring *both* of them on one position is not one of those ways: they ask
  different questions about the slot and a type answers both."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- ex-type
  "The `:type` on the ex-info a thunk throws, or nil if it does not throw.

  The paths below throw five distinguishable types — `:arg-genl` for the subtype
  constraint, `:arg-type` for the instance one, `:arity` and `:arg-position` for the
  declarations, `:functional` for a second arity value — and a bare
  `(thrown? ExceptionInfo …)` passes for every one of them alike.  An `argGenl` check
  collapsing into a naming refusal is exactly the regression a file full of those would
  stay green through, so each refusal here names the one it expects."
  [f]
  (try (f) nil (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))

(defn- type-relation
  "A type-level relation over kinds of `root`, plus the kinds themselves.
  Returns `[rel sub other root]`."
  [kb]
  (let [rel (tu/tmp-pred) root (tu/tmp-type) sub (tu/tmp-type) other (tu/tmp-type)]
    (v/assert kb (list 'genl root 'thing) 'CxUniverse)
    (v/assert kb (list 'genl sub root) 'CxUniverse)
    (v/assert kb (list 'genl other 'thing) 'CxUniverse)   ; a type, but not under root
    (v/assert kb (list 'argGenl rel 1 root) 'CxUniverse)
    [rel sub other root]))

(tu/deftest-kb a-subtype-satisfies-argGenl-and-a-sibling-does-not
  (let [[rel sub other root] (type-relation kb)]
    (testing "a subtype of the constraint type is what the position wants"
      (is (v/assert kb (list rel sub (tu/tmp-type)) 'CxUniverse)))
    (testing "the constraint type itself satisfies it — genl is reflexive"
      (is (v/assert kb (list rel root (tu/tmp-type)) 'CxUniverse)))
    (testing "a type outside the constraint's down-closure does not"
      (is (= :arg-genl (ex-type #(v/assert kb (list rel other (tu/tmp-type)) 'CxUniverse)))))))

(tu/deftest-kb argGenl-wants-a-subtype-where-argIsa-wants-an-instance
  ;; the whole point of having both: the same type symbol passes one and fails the other
  (let [[rel sub] (type-relation kb)
        instRel (tu/tmp-pred) root2 (tu/tmp-type)]
    (v/assert kb (list 'genl root2 'thing) 'CxUniverse)
    (v/assert kb (list 'genl sub root2) 'CxUniverse)
    (v/assert kb (list 'argIsa instRel 1 root2) 'CxUniverse)
    ;; a type symbol comes within argIsa's reach only once it carries a membership of
    ;; its own reaching `thing` — which is what the starter's (unaryPredicate t) batch
    ;; does for every type.  Without one the open-world exemption applies and there is
    ;; nothing to convict, so the test states it rather than assuming a loaded KB.
    (let [meta (tu/tmp-type)]
      (v/assert kb (list 'genl meta 'thing) 'CxUniverse)
      (v/assert kb (list meta sub) 'CxUniverse))
    (testing "the kind satisfies argGenl"
      (is (v/assert kb (list rel sub (tu/tmp-type)) 'CxUniverse)))
    (testing "and fails argIsa, which wants one of its instances"
      (is (= :arg-type (ex-type #(v/assert kb (list instRel sub (tu/tmp-ind)) 'CxUniverse)))))
    (testing "an instance of the kind is what argIsa wanted"
      (let [x (tu/tmp-ind)]
        (v/assert kb (list sub x) 'CxUniverse)
        (is (v/assert kb (list instRel x (tu/tmp-ind)) 'CxUniverse))))))

(tu/deftest-kb an-unplaced-type-is-excused-but-an-individual-is-not
  (let [[rel] (type-relation kb)]
    (testing "open-world: a term with no place in the hierarchy yet cannot violate"
      (is (v/assert kb (list rel (tu/tmp-type) (tu/tmp-type)) 'CxUniverse)))
    (testing "an individual can never acquire genl edges, so it is convicted not excused"
      (is (= :arg-genl (ex-type #(v/assert kb (list rel (tu/tmp-ind) (tu/tmp-type)) 'CxUniverse)))))))

(tu/deftest-kb argGenl-is-well-formedness-checked-like-argIsa
  (let [rel (tu/tmp-pred)]
    (testing "the type slot is a type, not an individual"
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'argGenl rel 1 (tu/tmp-ind)) 'CxUniverse)))))
    (testing "the position is a positive integer"
      (is (= :not-well-formed (ex-type #(v/assert kb (list 'argGenl rel 0 'thing) 'CxUniverse)))))
    (testing "the message names argGenl, not argIsa"
      (is (re-find #"argGenl"
                   (:message (first (v/check kb (list 'argGenl rel 0 'thing)
                                             'CxUniverse))))))))

(tu/deftest-kb a-derived-argGenl-violation-is-recorded-not-thrown
  ;; the derivation path must not abort a fixpoint, so it drops and ledgers instead
  (let [[rel _ other] (type-relation kb)
        trigger (tu/tmp-pred)]
    (v/clear-violations! kb)
    (v/assert kb (list 'set/forwardRule
                       (list 'implies (list trigger '?x) (list rel '?x other)))
              'CxUniverse)
    (v/assert kb (list trigger other) 'CxUniverse)
    (is (some #(= :arg-genl (:violation %)) (v/violations kb))
        "the conclusion is dropped into the ledger")))

;; ---- the constraint declarations, checked against each other -------------

(tu/deftest-kb a-constraint-on-a-position-the-predicate-lacks-is-refused
  (let [rel (tu/tmp-pred)]
    (v/assert kb (list 'binaryPredicate rel) 'CxUniverse)
    (testing "a declared position is fine"
      (is (v/assert kb (list 'argIsa rel 2 'thing) 'CxUniverse)))
    (testing "one past the declared arity would never fire, so it is refused"
      (is (= :arg-position (ex-type #(v/assert kb (list 'argIsa rel 5 'thing) 'CxUniverse))))
      (is (= :arg-position (ex-type #(v/assert kb (list 'argGenl rel 5 'thing) 'CxUniverse)))))
    (testing "open-world: an undeclared predicate takes any position"
      (is (v/assert kb (list 'argIsa (tu/tmp-pred) 9 'thing) 'CxUniverse)))))

(tu/deftest-kb both-constraints-on-one-position-narrow-it-rather-than-emptying-it
  ;; The two constraints ask different questions about the same slot — one *what kind
  ;; of thing* it holds, one *where in the hierarchy* — and a type answers both.  This
  ;; is how an imported ontology routinely declares a type-valued position, so refusing
  ;; the pair on the grounds that nothing satisfies both would be refusing knowledge on
  ;; a premise that is false.
  (tu/with-terms [rel a_collection an_animal a_dog Rex]
    (v/assert kb (list 'genl a_collection 'thing) 'CxUniverse)
    (v/assert kb (list 'genl an_animal 'thing) 'CxUniverse)
    (v/assert kb (list 'genl a_dog an_animal) 'CxUniverse)
    (v/assert kb (list a_collection a_dog) 'CxUniverse)  ; a_dog *is* a collection

    (testing "both may be declared of one position"
      (is (v/assert kb (list 'argIsa rel 1 a_collection) 'CxUniverse))
      (is (v/assert kb (list 'argGenl rel 1 an_animal) 'CxUniverse)))

    (testing "and a term satisfying both is admitted — an instance of the one, a subtype of the other"
      (is (v/assert kb (list rel a_dog (tu/tmp-ind)) 'CxUniverse)))

    (testing "each is still enforced on its own"
      (tu/with-terms [a_plant]
        (v/assert kb (list 'genl a_plant 'thing) 'CxUniverse)
        (v/assert kb (list a_collection a_plant) 'CxUniverse)
        (is (= :arg-genl (ex-type #(v/assert kb (list rel a_plant (tu/tmp-ind)) 'CxUniverse)))
            "a collection, but not a kind of animal — argGenl convicts"))
      (is (= :arg-genl (ex-type #(v/assert kb (list rel Rex (tu/tmp-ind)) 'CxUniverse)))
          "an individual can never be a subtype, so it is convicted rather than excused"))))

(tu/deftest-kb the-constraint-must-agree-with-the-declared-relation-kind
  (let [instRel (tu/tmp-pred) typeRel (tu/tmp-pred)]
    (v/assert kb (list 'instanceRelationPredicate instRel) 'CxUniverse)
    (v/assert kb (list 'typeRelationPredicate typeRel) 'CxUniverse)
    (testing "an instance-level relation takes argIsa"
      (is (v/assert kb (list 'argIsa instRel 1 'thing) 'CxUniverse))
      (is (= :arg-constraint-kind (ex-type #(v/assert kb (list 'argGenl instRel 2 'thing) 'CxUniverse)))))
    (testing "a type-level relation takes argGenl"
      (is (v/assert kb (list 'argGenl typeRel 1 'thing) 'CxUniverse))
      (is (= :arg-constraint-kind (ex-type #(v/assert kb (list 'argIsa typeRel 2 'thing) 'CxUniverse)))))
    (testing "an unclassified relation takes either"
      (let [rel (tu/tmp-pred)]
        (is (v/assert kb (list 'argIsa rel 1 'thing) 'CxUniverse))
        (is (v/assert kb (list 'argGenl rel 2 'thing) 'CxUniverse))))))

(tu/deftest-kb arity-is-functional-so-a-second-value-is-refused
  ;; the declaration ships in CxCore; this KB is empty, so it states it — that
  ;; the shipped vocabulary carries it is core-context-test's assertion
  (let [rel (tu/tmp-pred)]
    (v/assert kb '(functional arity) 'CxUniverse)
    (v/assert kb (list 'arity rel 2) 'CxUniverse)
    (testing "restating the same arity is a no-op, not a clash"
      (is (v/assert kb (list 'arity rel 2) 'CxUniverse)))
    (testing "a different arity for the same predicate is a functional violation"
      (is (= :functional (ex-type #(v/assert kb (list 'arity rel 7) 'CxUniverse)))))))

(tu/deftest-kb a-sentence-must-match-its-predicates-declared-arity
  (let [rel (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind)]
    (v/assert kb (list 'binaryPredicate rel) 'CxUniverse)
    (testing "the declared arity stores"
      (is (v/assert kb (list rel a b) 'CxUniverse)))
    (testing "too many arguments, and too few, are both refused"
      (is (= :arity (ex-type #(v/assert kb (list rel a b (tu/tmp-ind)) 'CxUniverse))))
      (is (= :arity (ex-type #(v/assert kb (list rel a) 'CxUniverse)))))
    (testing "open-world: an undeclared predicate takes any arity"
      (let [undeclared (tu/tmp-pred)]
        (is (v/assert kb (list undeclared a) 'CxUniverse))
        (is (v/assert kb (list undeclared a b) 'CxUniverse))))))

(tu/deftest-kb the-arity-declaration-can-come-from-either-spelling
  ;; (arity P N) and the N-ary predicate type derive each other, so either alone binds
  (let [byArity (tu/tmp-pred) byType (tu/tmp-pred) a (tu/tmp-ind)]
    (v/assert kb (list 'arity byArity 1) 'CxUniverse)
    (v/assert kb (list 'unaryPredicate byType) 'CxUniverse)
    (is (v/assert kb (list byArity a) 'CxUniverse))
    (is (v/assert kb (list byType a) 'CxUniverse))
    (is (= :arity (ex-type #(v/assert kb (list byArity a (tu/tmp-ind)) 'CxUniverse))))
    (is (= :arity (ex-type #(v/assert kb (list byType a (tu/tmp-ind)) 'CxUniverse))))))

(tu/deftest-kb the-arity-declaration-is-cached-and-follows-its-sentex
  ;; `(arity P n)` is read on every assertion, so it is cached in the taxonomy beside
  ;; `transitive` and `inverse` rather than re-queried.  A cache is only right if it
  ;; goes when its sentex does — the same discipline every other declaration keeps.
  (let [rel (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind)]
    (let [h (v/assert kb (list 'arity rel 2) 'CxUniverse)]
      (is (= 2 (tax/declared-arity (:taxonomy kb) rel)) "cached on assert")
      (is (= :arity (ex-type #(v/assert kb (list rel a) 'CxUniverse))))
      (testing "and retracting the declaration takes the constraint with it"
        (v/retract! kb h)
        (is (nil? (tax/declared-arity (:taxonomy kb) rel)))
        (is (v/assert kb (list rel a) 'CxUniverse))
        (is (v/assert kb (list rel a b) 'CxUniverse)
            "the arity the declaration named is admitted too — with nothing declared
             the check is released, not inverted")))
    (testing "and a rebuild from the records agrees with the live cache"
      (let [h2 (v/assert kb (list 'arity (tu/tmp-pred) 3) 'CxUniverse)
            sx (v/sentex kb h2)
            p2 (second (:sentence sx))]
        (v/recover kb)
        (is (= 3 (tax/declared-arity (:taxonomy kb) p2))
            "recover replays the declaration into the cache")))))

(tu/deftest-kb a-rebuild-clears-the-arity-cache-before-replaying-it
  ;; `recover` merges into what it clears, so a cache it forgets to clear can only ever
  ;; *grow*: an entry whose sentex is gone would outlive the rebuild meant to re-derive
  ;; it.  The same rule the other seven caches keep.
  ;; The scenario needs the live cache to hold an entry whose record is gone, which a
  ;; retraction never produces (it drops both).  `clear!` does exactly that — it wipes
  ;; the stores and deliberately leaves the in-memory caches alone — so it is the shape
  ;; a reset-and-reload takes, and the one that catches a cache `recover` forgot.
  (tu/with-cleared-kb [kb2 tu/fresh]
    (let [rel (tu/tmp-pred) a (tu/tmp-ind)]
      (v/assert kb2 (list 'arity rel 2) 'CxUniverse)
      (is (= 2 (tax/declared-arity (:taxonomy kb2) rel)))
      (v/clear! kb2)
      (v/recover kb2)
      (is (nil? (tax/declared-arity (:taxonomy kb2) rel))
          "the rebuild re-derives from the records, it does not top up")
      (is (v/assert kb2 (list rel a) 'CxUniverse)
          "and the constraint went with the declaration"))))

(tu/deftest-kb the-arity-a-reader-sees-is-the-one-that-binds-it
  ;; Two contexts declaring different arities: each reader that sees one sees one
  ;; answer.  Uniqueness is asked of the visible declarations, so a declaration a
  ;; reader cannot see neither binds it nor suppresses the one it can.
  (tu/with-terms [CxLeft CxRight CxBoth]
    (let [rel (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind)]
      (v/assert kb (list 'genlCx CxLeft 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxRight 'CxUniverse) 'CxUniverse)
      (v/assert kb (list 'genlCx CxBoth CxLeft) 'CxUniverse)
      (v/assert kb (list 'genlCx CxBoth CxRight) 'CxUniverse)
      (v/assert kb (list 'arity rel 2) CxLeft)
      (v/assert kb (list 'arity rel 3) CxRight)
      (let [tax (:taxonomy kb)]
        (is (= 2 (tax/declared-arity tax rel CxLeft)) "sees only the binary one")
        (is (= 3 (tax/declared-arity tax rel CxRight)) "sees only the ternary one")
        (is (nil? (tax/declared-arity tax rel CxBoth))
            "sees both, so has no settled answer")
        (is (nil? (tax/declared-arity tax rel)) "and unscoped is the same"))
      (testing "and each reader is bound by what it sees"
        (is (= :arity (ex-type #(v/assert kb (list rel a) CxLeft))))
        (is (v/assert kb (list rel a b) CxLeft))
        (is (v/assert kb (list rel a b) CxBoth) "unsettled constrains nothing")))))

(tu/deftest-kb two-arities-for-one-predicate-constrain-nothing
  ;; The cache holds what it was told, and it was told two different things.  Refusing
  ;; on whichever was found first would be arbitrary — the same open-world stance the
  ;; check takes toward a predicate nobody has declared at all.  (An ordinary KB never
  ;; gets here: `(functional arity)` merges the two values instead, and CxCore
  ;; ships that declaration.  A KB without it, or an import that stored both, does.)
  (let [rel (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind)]
    (v/assert kb (list 'arity rel 2) 'CxUniverse)
    (v/assert kb (list 'arity rel 3) 'CxUniverse)
    (is (nil? (tax/declared-arity (:taxonomy kb) rel))
        "unsettled, which is not the same as undeclared but constrains the same")
    (is (v/assert kb (list rel a b) 'CxUniverse))
    (is (v/assert kb (list rel a b (tu/tmp-ind)) 'CxUniverse))
    (testing "and dropping one of them settles it again"
      (v/retract! kb (v/handle-of kb (list 'arity rel 3) 'CxUniverse))
      (is (= 2 (tax/declared-arity (:taxonomy kb) rel)))
      (is (= :arity (ex-type #(v/assert kb (list rel a) 'CxUniverse)))))))

(tu/deftest-kb a-variableArity-predicate-is-exempt
  ;; lessThan is declared binary and reads a chain of any length; the declaration says so
  (let [rel (tu/tmp-pred) a (tu/tmp-ind) b (tu/tmp-ind)]
    (v/assert kb (list 'binaryPredicate rel) 'CxUniverse)
    (is (= :arity (ex-type #(v/assert kb (list rel a b (tu/tmp-ind)) 'CxUniverse))))
    (v/assert kb (list 'variableArity rel) 'CxUniverse)
    (testing "declaring it variable arity releases the check"
      (is (v/assert kb (list rel a b (tu/tmp-ind)) 'CxUniverse)))))

;; ---- the global/scoped split in the conviction ---------------------------
;; `genls-problem` runs three probes: a **global** individual floor (could the
;; argument ever be a type?), a **scoped** open-world floor (does the writer see
;; any evidence at all?), and the scoped subtype test.  The middle one is what
;; keeps a NAF check from convicting harder the less a context sees: an imported
;; reified NAT's minting edges land in CxUniverse, and a writer whose cone does not
;; reach them must excuse, not convict.

(tu/deftest-kb an-argument-whose-edges-are-out-of-sight-is-excused-not-convicted
  (let [rel (tu/tmp-pred) root (tu/tmp-type) kind (tu/tmp-type)
        reified (tu/tmp-ind) plain (tu/tmp-ind)
        ctx (tu/tmp-ctx)]
    ;; ctx is deliberately unwired: it cannot see CxUniverse
    (v/assert kb (list 'genl root 'thing) ctx)
    (v/assert kb (list 'argGenl rel 1 root) ctx)
    ;; a reified NAT-shaped constant minted with real genl edges into CxUniverse —
    ;; the raw writer stands in for nat/mint-nat!, whose edges are exactly this
    (tax/add-genl (:taxonomy kb) reified root 999901 'CxUniverse)
    (testing "globally in the hierarchy, invisibly from ctx: open world excuses"
      (is (v/assert kb (list rel reified (tu/tmp-type)) ctx)))
    (testing "a plain individual with no edges anywhere is still convicted"
      (is (= :arg-genl (ex-type #(v/assert kb (list rel plain (tu/tmp-type)) ctx)))))
    (testing "visible evidence reaching the wrong place still convicts"
      (v/assert kb (list 'genl kind 'thing) ctx)     ; visible, but not under root
      (is (= :arg-genl (ex-type #(v/assert kb (list rel kind (tu/tmp-type)) ctx)))))
    (tax/del-genl! (:taxonomy kb) reified root 999901)))

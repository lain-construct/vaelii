;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.nat-test
  "Non-atomic terms (NATs) — docs/nat.md.

  A ground reifiable NAT `(FruitFn AppleTree)` reifies to an opaque `nat/` constant
  before it reaches the index (Strategy A), so it autoindexes like an atomic symbol;
  an unreifiable structural NAT `(QuantityFn 5 Kilogram)` stays structural.  The constant↔
  expression map is an ordinary `(termOfUnit K E)` fact, so rename rides the equality
  migration and remove rides the retraction sweep."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.nat :as nat]
            [vaelii.test-util :as tu]))

(use-fixtures :once (tu/loaded core-context/load-into))
(use-fixtures :each (tu/neutral))

(defn- k-of
  "The reified constant a stored NAT-bearing sentence's arg1 became."
  [kb h] (second (:sentence (v/sentex kb h))))

;; ---- 1. round-trip -------------------------------------------------------

(tu/deftest-kb round-trip-stores-an-opaque-constant
  (tu/with-terms [FruitFn AppleTree fruit]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (let [h (v/assert kb (list 'color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k (k-of kb h)]
      (testing "the stored sentence holds an opaque constant, not the compound"
        (is (nat/reified-nat-symbol? k))
        (is (= (list 'color k 'Red) (:sentence (v/sentex kb h))))
        (is (not-any? sequential? (rest (:sentence (v/sentex kb h))))))
      (testing "the materialized result type holds"
        (is (seq (v/sentexes-matching kb (list fruit k) '?ctx))))
      (testing "a NAT-bearing query resolves to the stored constant"
        (is (= [{'?c 'Red}] (v/ask kb (list 'color (list FruitFn AppleTree) '?c) 'CxUniverse))))
      (testing "display expands the constant back to its functional expression"
        (is (= (list 'color (list FruitFn AppleTree) 'Red)
               (nat/expand-expression kb (:sentence (v/sentex kb h))))))
      (testing "an unknown NAT resolves to no-match and mints nothing"
        (let [before (count (v/sentexes-matching kb (list 'termOfUnit '?k '?e) 'CxUniverse))]
          (is (empty? (v/sentexes-matching kb (list 'color (list FruitFn 'PearTree) '?c) '?ctx)))
          (is (= before (count (v/sentexes-matching kb (list 'termOfUnit '?k '?e) 'CxUniverse)))))))))

;; ---- 2. dedup ------------------------------------------------------------

(tu/deftest-kb the-same-nat-yields-the-same-constant
  (tu/with-terms [FruitFn AppleTree]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (let [h1 (v/assert kb (list 'color (list FruitFn AppleTree) 'Red)   'CxUniverse)
          h2 (v/assert kb (list 'taste (list FruitFn AppleTree) 'Sweet) 'CxUniverse)]
      (is (= (k-of kb h1) (k-of kb h2)))
      (testing "one termOfUnit maps the expression"
        (is (= 1 (count (v/sentexes-matching kb (list 'termOfUnit '?k (list FruitFn AppleTree))
                                             'CxUniverse))))))))

(tu/deftest-kb a-vector-spelled-nat-is-the-nat-the-list-spelling-names
  ;; Reification runs **before** `canon`, and canon makes `[F a]` and `(F a)` one
  ;; sentence — so a gate on the list spelling alone stores the raw compound for one
  ;; spelling and the constant for the other: two handles and two maps for one claim,
  ;; decided by how whoever typed it spelled a bracket.  Both arrival orders, since the
  ;; second spelling has to resolve to what the first stored either way round.
  (doseq [vector-first? [false true]]
    (tu/with-terms [MotherFn Ann Tom likes]
      (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
      (let [E         (list MotherFn Ann)
            spellings [(list likes Tom E) (list likes Tom [MotherFn Ann])]
            [a b]     (if vector-first? (reverse spellings) spellings)
            ha        (v/assert kb a 'CxUniverse)
            hb        (v/assert kb b 'CxUniverse)
            what      (str (if vector-first? "vector" "list") " spelling first")]
        (is (= ha hb) (str what ": one handle for one canonical sentence"))
        (is (nat/reified-nat-symbol? (nth (:sentence (v/sentex kb ha)) 2))
            (str what ": and it holds the constant rather than the compound"))
        (is (= 1 (count (v/sentexes-matching kb (list 'termOfUnit '?k E) 'CxUniverse)))
            (str what ": one map for one expression"))))))

;; ---- 3. nested -----------------------------------------------------------

(tu/deftest-kb a-nested-nat-reifies-inner-then-outer
  (tu/with-terms [FruitFn BestTreeIn Orchard1]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'reifiable_function BestTreeIn) 'CxUniverse)
    (let [h        (v/assert kb (list 'color (list FruitFn (list BestTreeIn Orchard1)) 'Green)
                             'CxUniverse)
          inner-k  (nat/dedup-constant kb (list BestTreeIn Orchard1))
          outer-k  (k-of kb h)]
      (testing "both the inner and outer NAT have a termOfUnit"
        (is (nat/reified-nat-symbol? inner-k))
        (is (nat/reified-nat-symbol? outer-k))
        (is (= (list FruitFn inner-k) (nat/nat-expression kb outer-k)))
        (is (= (list BestTreeIn Orchard1) (nat/nat-expression kb inner-k))))
      (testing "display expands both levels"
        (is (= (list 'color (list FruitFn (list BestTreeIn Orchard1)) 'Green)
               (nat/expand-expression kb (:sentence (v/sentex kb h)))))))))

;; ---- 4. rename -----------------------------------------------------------

(tu/deftest-kb rename-rewrites-the-expression-keeping-the-constant-stable
  (tu/with-terms [FruitFn AppleTree MalusTree]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (let [h (v/assert kb (list 'color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k (k-of kb h)]
      (v/assert kb (list 'rewriteOf MalusTree AppleTree) 'CxUniverse)   ; rename AppleTree -> MalusTree
      (testing "the constant is stable and its expression is rewritten"
        (is (= (list FruitFn MalusTree) (nat/nat-expression kb k)))
        (is (= k (nat/dedup-constant kb (list FruitFn MalusTree))))
        (is (= 1 (count (v/sentexes-matching kb (list 'termOfUnit '?k (list FruitFn MalusTree))
                                             'CxUniverse)))))
      (testing "the retired spelling stays a usable question, resolving to the same K"
        ;; AppleTree is deprecated to MalusTree, so a goal naming the old term rewrites
        ;; to the new expression before lookup (docs/equality.md) and still finds K
        (is (= k (nat/dedup-constant kb (list FruitFn AppleTree))))))))

(tu/deftest-kb rename-collision-merges-the-two-constants
  (tu/with-terms [FruitFn AppleTree MalusTree]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (let [ha (v/assert kb (list 'color (list FruitFn AppleTree) 'Red)   'CxUniverse)
          hm (v/assert kb (list 'taste (list FruitFn MalusTree) 'Sweet) 'CxUniverse)]
      (is (not= (k-of kb ha) (k-of kb hm)))
      (v/assert kb (list 'rewriteOf MalusTree AppleTree) 'CxUniverse)
      (testing "the colliding constants merge to one"
        (is (empty? (nat/colliding-constant-groups kb)))
        (is (= 1 (count (v/sentexes-matching kb (list 'termOfUnit '?k (list FruitFn MalusTree))
                                             'CxUniverse))))
        (is (some? (nat/dedup-constant kb (list FruitFn MalusTree))))))))

(tu/deftest-kb a-collision-resolves-to-the-constant-the-repair-would-keep
  ;; Two constants can name one expression without a rename: a `:bulk?` load skips the
  ;; dedup probe and an import restores whatever the dump held, and neither is swept up
  ;; by the next unrelated equality.  `group-collisions` elects the lexicographically
  ;; smallest as the survivor a merge keeps, so the *read* has to answer with that one —
  ;; answering with whichever the retrieval yielded first makes the expression denote a
  ;; different term in a KB whose two maps arrived the other way round, and every later
  ;; read inherits it.  So both orders, and one answer.
  (doseq [smallest-first? [true false]]
    (tu/with-terms [FruitFn AppleTree]
      (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
      (let [E     (list FruitFn AppleTree)
            ks    (vec (sort [(nat/fresh-constant) (nat/fresh-constant)]))
            what  (str "the " (if smallest-first? "smallest" "largest") " asserted first")]
        ;; staged the way the mint writes one — the map is `:monotonic` bookkeeping,
        ;; and the second is the one no dedup probe stopped
        (doseq [k (if smallest-first? ks (rseq ks))]
          (v/assert kb (list 'termOfUnit k E) 'CxUniverse {:strength :monotonic}))
        (is (= 2 (count (v/sentexes-matching kb (list 'termOfUnit '?k E) 'CxUniverse)))
            (str what ": both maps stand, so there is a collision to resolve"))
        (is (= (first ks) (nat/dedup-constant kb E)) what)
        (is (= [(first ks)]
               (vec (keep (fn [[survivor dups]]
                            (when (= (set ks) (set (cons survivor dups))) survivor))
                          (nat/colliding-constant-groups kb))))
            (str what ": and the read named the survivor the repair elects"))))))

(tu/deftest-kb one-constant-mapped-to-two-expressions-is-swept-against-one-of-them
  ;; The collision running the other way: one constant, two expressions, the 1:1 invariant
  ;; not yet restored.  Two readers consult that map and they have to agree — `orphan?`
  ;; decides whether `k` is collectable, and `bookkeeping-handles` computes what the sweep
  ;; then retracts.  Reading it two different ways lets the sweep call `k` orphaned on
  ;; expression E₁ and retract the bookkeeping it computed for E₂: a materialized type of
  ;; the *other* expression is left stored, naming a constant that has been collected.
  ;;
  ;; Both readers take the **content-least** expression, so the answer is one whichever
  ;; order the two maps arrived in — which is what the two arms below compare.  Each arm
  ;; stores one materialized result type, once belonging to the authoritative expression's
  ;; function and once to the other's, since that is what makes the two verdicts differ.
  (doseq [type-of-least? [true false]]
    (tu/with-terms [FruitFn SeedFn AppleTree fruit seed]
      (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
      (v/assert kb (list 'reifiable_function SeedFn) 'CxUniverse)
      (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
      (v/assert kb (list 'result SeedFn seed) 'CxUniverse)
      (let [Es      (nm/sort-by-content-key identity
                                            [(list FruitFn AppleTree) (list SeedFn AppleTree)])
            least   (first Es)
            ;; the result type the mint would have written for one expression or the other
            typ     (fn [E] (if (= FruitFn (first E)) fruit seed))
            ;; one arm per arrival order of the two maps, each read back the same way
            reading (fn [order]
                      (let [k (nat/fresh-constant)]
                        (doseq [E order]
                          (v/assert kb (list 'termOfUnit k E) 'CxUniverse {:strength :monotonic}))
                        (v/assert kb (list (typ (if type-of-least? least (second Es))) k)
                                  'CxUniverse {:strength :monotonic})
                        (let [stored (set (map :id (kb/find-sentexes kb k)))]
                          {:expression (nat/nat-expression kb k)
                           :orphan?    (nat/orphan? kb k)
                           :retracts   (count (nat/bookkeeping-handles kb k))
                           :stored     (count stored)
                           ;; the contract the two readers exist to keep together
                           :coherent?  (or (not (nat/orphan? kb k))
                                           (= stored (set (nat/bookkeeping-handles kb k))))})))
            fwd     (reading Es)
            rev     (reading (reverse Es))
            what    (str "the result type belongs to the " (if type-of-least? "least" "other")
                         " expression")]
        (is (= 3 (:stored fwd) (:stored rev))
            (str what ": two maps and one materialized type name the constant"))
        (is (= least (:expression fwd) (:expression rev))
            (str what ": the content-least expression answers, in either arrival order"))
        (is (:coherent? fwd) (str what ": an orphan's whole record set is what the sweep retracts"))
        (is (:coherent? rev) (str what ": and in the other arrival order too"))
        (is (= (dissoc fwd :expression) (dissoc rev :expression))
            (str what ": the sweep outcome does not depend on which map arrived first"))))))

;; ---- 5. remove -----------------------------------------------------------

(tu/deftest-kb removing-the-last-use-collects-the-orphaned-reified-nat
  (tu/with-terms [FruitFn AppleTree fruit]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (let [h (v/assert kb (list 'color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k (k-of kb h)]
      (is (some? (nat/nat-expression kb k)))
      (v/retract! kb h)
      (testing "the reified NAT constant and its bookkeeping are gone, no dangling nat/ symbol"
        (is (nil? (nat/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (kb/find-sentexes kb k)))
        (is (empty? (nat/orphaned-constants kb)))))))

;; The sweep separates a use from bookkeeping by **what the mint wrote**, not by what a
;; sentence looks like.  The two are not the same question: a user's own unary claim about
;; a reified NAT has a materialized result type's shape — `(T K)`, and `(genl K T)` for the
;; subtype half — so a sweep reading shape retracts the claim along with the constant, in
;; silence and with nothing to read afterwards that says it happened.

(tu/deftest-kb a-users-unary-claim-about-a-reified-nat-is-a-use-not-bookkeeping
  (tu/with-terms [FruitFn AppleTree prime noted Author]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (let [h  (v/assert kb (list noted Author (list FruitFn AppleTree)) 'CxUniverse)
          k  (nth (:sentence (v/sentex kb h)) 2)
          hu (v/assert kb (list prime (list FruitFn AppleTree)) 'CxUniverse)]
      (testing "both facts stand on one constant, and neither is a declared result type"
        (is (nat/reified-nat-symbol? k))
        (is (= (list prime k) (:sentence (v/sentex kb hu))))
        (is (false? (nat/orphan? kb k))))
      (v/retract! kb h)
      (testing "the binary use goes and the unary claim survives, holding the constant"
        (is (seq (v/sentexes-matching kb (list prime k) 'CxUniverse)))
        (is (= (list FruitFn AppleTree) (nat/nat-expression kb k)))
        (is (false? (nat/orphan? kb k))))
      (v/retract! kb hu)
      (testing "and once the claim is withdrawn the constant is collected after all"
        (is (empty? (kb/find-sentexes kb k)))
        (is (nil? (nat/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (nat/orphaned-constants kb)))))))

;; A use is counted by **storage**, and the two tests below are the two ways a stored use
;; is not a believed one.  Either way the constant has to stay: a sentence naming it is in
;; the store, so collecting the map would leave that sentence holding a raw `nat/` symbol
;; nothing maps — and re-reifying the expression would then mint a second constant beside
;; the first, a collision no merge repair caused.

(tu/deftest-kb a-defeated-use-keeps-the-constant-until-it-is-actually-removed
  ;; The claim is defeated by the constant's own materialized result type, which is
  ;; `:monotonic` bookkeeping — so nothing a *use* could be read off has moved, and the
  ;; claim sits in the store exactly where a relabel can give it back.  Which is what
  ;; happens two lines later.
  (tu/with-terms [FruitFn AppleTree fruit_t stone_t color]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit_t) 'CxUniverse)
    (let [h (v/assert kb (list color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k (k-of kb h)]
      ;; the claim first, the separation over it after — the retroactive case, and the
      ;; policy under which a definitional clash is arbitrated rather than refused
      (binding [checks/*arbitrate-constraints?* true]
        (let [hs (v/assert kb (list stone_t k) 'CxUniverse)
              hd (v/assert kb (list 'disjoint fruit_t stone_t) 'CxUniverse
                           {:strength :monotonic})]
          (testing "the claim is stored and OUT, outranked by the declared result type"
            (is (false? (v/in? kb hs)))
            (is (true? (v/in? kb (v/handle-of kb (list fruit_t k) 'CxUniverse)))))
          (v/retract! kb h)
          (testing "so the sweep that the last *believed* use leaving triggers keeps it"
            (is (false? (nat/orphan? kb k)))
            (is (= k (nat/dedup-constant kb (list FruitFn AppleTree))))
            (is (some? (v/handle-of kb (list stone_t k) 'CxUniverse))))
          (v/retract! kb hd)
          (testing "and the defeat lifting revives a use naming a constant still mapped"
            (is (true? (v/in? kb hs)))
            (is (= (list FruitFn AppleTree) (nat/nat-expression kb k))))
          (v/retract! kb hs)
          (testing "removing it is what makes the constant an orphan, and it is collected"
            (is (empty? (kb/find-sentexes kb k)))
            (is (nil? (nat/dedup-constant kb (list FruitFn AppleTree))))
            (is (empty? (nat/orphaned-constants kb)))))))))

(tu/deftest-kb an-inert-use-keeps-the-constant-though-it-has-no-node-at-all
  ;; The other half, and the one belief cannot speak about either way: an inert sentex —
  ;; a labeling's materialized truth value — is never a premise, so it has no TMS node to
  ;; be IN or OUT.  It still names the constant, and it is still in the store.
  (tu/with-terms [FruitFn AppleTree noted Author color]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (let [h (v/assert kb (list color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k (k-of kb h)
          i (v/assert-inert kb (list noted Author k) 'CxUniverse)]
      (is (nat/reified-nat-symbol? k))
      (is (false? (v/in? kb i)) "inert: stored, and never believed")
      (v/retract! kb h)
      (testing "the believed use went and the inert one holds the constant"
        (is (false? (nat/orphan? kb k)))
        (is (= (list FruitFn AppleTree) (nat/nat-expression kb k)))
        (is (= k (nat/dedup-constant kb (list FruitFn AppleTree)))))
      (v/retract! kb i)
      (testing "and once that goes too the sweep collects — no dangling nat/ symbol"
        (is (empty? (kb/find-sentexes kb k)))
        (is (nil? (nat/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (nat/orphaned-constants kb)))))))

(tu/deftest-kb the-declaration-is-what-separates-a-materialized-type-from-a-claim
  (tu/with-terms [FruitFn AppleTree fruit ripe color]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (let [h  (v/assert kb (list color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k  (k-of kb h)
          hr (v/assert kb (list ripe k) 'CxUniverse)]
      (testing "two unary sentexes of one shape stand on the constant"
        (is (seq (v/sentexes-matching kb (list fruit k) 'CxUniverse)))
        (is (seq (v/sentexes-matching kb (list ripe k) 'CxUniverse))))
      (v/retract! kb h)
      (testing "the undeclared one is a use, so the constant outlives its other use"
        (is (= (list FruitFn AppleTree) (nat/nat-expression kb k)))
        (is (seq (v/sentexes-matching kb (list ripe k) 'CxUniverse))))
      (v/retract! kb hr)
      (testing "the declared one is collected with the constant — no dangling nat/ symbol"
        (is (empty? (kb/find-sentexes kb k)))
        (is (empty? (v/sentexes-matching kb (list fruit k) 'CxUniverse)))
        (is (nil? (nat/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (nat/orphaned-constants kb)))))))

(tu/deftest-kb the-bookkeeping-set-is-an-answer-rather-than-a-plan
  ;; The caller retracts what `bookkeeping-handles` hands back, and the question
  ;; "is this one of `k`'s own?" is itself read off `k`'s `termOfUnit` — so an answer
  ;; still being computed while the caller acts on it reads a KB the caller has already
  ;; torn the map out of, and everything after that point stops looking like
  ;; bookkeeping.  What survives is a materialized type naming a collected constant.
  ;; The order the term index yields decides whether it happens, so the two tests above
  ;; witness it only in some retrieval orders; this one pins the property instead.
  (tu/with-terms [FruitFn AppleTree fruit color]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (let [h  (v/assert kb (list color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k  (k-of kb h)
          hs (nat/bookkeeping-handles kb k)]
      ;; the claim is that nothing in the answer is still pending, not that it is a
      ;; vector — `counted?` covers the collection this returns, `realized?` a seq some
      ;; other realization produced, and a lazy tail satisfies neither
      (is (or (counted? hs) (realized? hs))
          "realized before it is returned, not as the caller consumes it")
      (is (= 2 (count hs)) "the map and the one materialized result type"))))

;; The sweep asks about the constants the teardown's removals named, so a nested NAT —
;; whose only reference is the expression the *outer* constant's map holds — is reached
;; only on the round after the outer one goes.  Its collection is what says the region
;; grows with the fixpoint rather than being fixed at the seed.

(tu/deftest-kb collecting-an-orphan-cascades-to-the-nat-nested-in-its-expression
  (tu/with-terms [FruitFn BestTreeIn Orchard1]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'reifiable_function BestTreeIn) 'CxUniverse)
    (let [h       (v/assert kb (list 'color (list FruitFn (list BestTreeIn Orchard1)) 'Green)
                            'CxUniverse)
          outer-k (k-of kb h)
          inner-k (nat/dedup-constant kb (list BestTreeIn Orchard1))]
      (testing "the inner constant is referenced only by the outer one's expression"
        (is (nat/reified-nat-symbol? inner-k))
        (is (= (list FruitFn inner-k) (nat/nat-expression kb outer-k)))
        (is (false? (nat/orphan? kb inner-k))))
      (v/retract! kb h)
      (testing "the outer constant goes with its last use"
        (is (empty? (kb/find-sentexes kb outer-k)))
        (is (nil? (nat/dedup-constant kb (list FruitFn inner-k)))))
      (testing "and the inner one goes with the expression that was naming it"
        (is (empty? (kb/find-sentexes kb inner-k)))
        (is (nil? (nat/dedup-constant kb (list BestTreeIn Orchard1)))))
      (is (empty? (nat/orphaned-constants kb))))))

;; A use does not always leave by the retraction's own dependency sweep: an exception
;; that starts holding blocks a justification, and the settle that follows deletes what
;; it was solely supporting (docs/exceptions.md).  Nothing is retracted here at all, so
;; the constant is reachable only through what the *settle* removed.

(tu/deftest-kb a-nat-whose-use-the-settle-swept-is-collected-too
  (tu/with-terms [FruitFn AppleTree fruity brightAs weather overcast Sunny Sun]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    ;; `fruity` is the function's declared result type, so the sentence that mints the
    ;; constant is the constant's own materialized type — one sentex, and bookkeeping.
    ;; The exception is about the weather rather than about the fruit, so the rule's
    ;; conclusion is the only sentence in the whole test that names the constant.
    (v/assert kb (list 'result FruitFn fruity) 'CxUniverse)
    (let [h (v/assert kb (list fruity (list FruitFn AppleTree)) 'CxUniverse)
          k (k-of kb h)]
      (v/assert kb (list weather Sunny) 'CxUniverse)
      (v/assert kb (list 'exceptWhen (list overcast '?w)
                         (list 'set/defaultRule
                               (list 'implies (list 'and (list fruity '?x) (list weather '?w))
                                     (list brightAs '?x Sun))))
                'CxUniverse)
      (testing "the rule's conclusion is the constant's one live use"
        (is (nat/reified-nat-symbol? k))
        (is (seq (v/sentexes-matching kb (list brightAs k Sun) 'CxUniverse)))
        (is (false? (nat/orphan? kb k))))
      (v/edit! kb {:add [[(list overcast Sunny) 'CxUniverse]]})
      (testing "the exception blocks the rule and the settle sweeps the conclusion"
        (is (empty? (v/sentexes-matching kb (list brightAs k Sun) 'CxUniverse))))
      (testing "and the constant it was the last use of goes with it"
        (is (nil? (nat/nat-expression kb k)))
        (is (nil? (nat/dedup-constant kb (list FruitFn AppleTree))))
        (is (empty? (nat/orphaned-constants kb)))))))

;; ---- 6. unreifiable gate -------------------------------------------------

(tu/deftest-kb an-unreifiable-nat-stays-structural
  (tu/with-terms [QuantityFn Obj]
    (v/assert kb (list 'unreifiable_function QuantityFn) 'CxUniverse)
    (let [nut (list QuantityFn 5 'Kilogram)
          h   (v/assert kb (list 'mass Obj nut) 'CxUniverse)]
      (testing "the compound is stored structurally, not minted"
        (is (= (list 'mass Obj nut) (:sentence (v/sentex kb h))))
        (is (nil? (nat/dedup-constant kb nut))))
      (testing "it round-trips unchanged"
        (is (seq (v/sentexes-matching kb (list 'mass Obj nut) '?ctx)))))))

;; ---- 7. no-op cost -------------------------------------------------------

(tu/deftest-kb with-no-reifiable-function-the-reify-pass-is-a-no-op
  (tu/with-terms [FruitFn AppleTree]
    (testing "the gate is off and a plain compound is stored verbatim"
      (is (false? (nat/any-reifiable-functions? kb)))
      ;; a compound argument with no reifiable_function declared is left structural
      (let [h (v/assert kb (list 'grows (list FruitFn AppleTree) 'Spring) 'CxUniverse)]
        (is (= (list 'grows (list FruitFn AppleTree) 'Spring) (:sentence (v/sentex kb h))))))))

;; ---- 8. every read path asks the same question ---------------------------
;;
;; A NAT reifies on the *write* path, so every read path has to reify its goal to meet
;; the stored constant.  `core/prepare-goal-for-read` is that step, and the interesting
;; failure is not a wrong answer but a **silently empty** one: a path that skips it
;; matches the compound against a store that holds a symbol and finds nothing, which
;; reads exactly like a KB that was never told.  So the claim is parity, checked path
;; by path rather than inferred from the one that works.

(tu/deftest-kb every-read-path-reifies-the-nat-in-its-goal
  (tu/with-terms [CapitalOfFn France isCapital Yes]
    (v/assert kb (list 'reifiable_function CapitalOfFn) 'CxUniverse)
    (let [h (v/assert kb (list isCapital (list CapitalOfFn France) Yes) 'CxUniverse)]
      (testing "the store holds a constant, so a goal spelled as the NAT must be reified"
        (is (nat/reified-nat-symbol? (second (:sentence (v/sentex kb h)))))))
    (doseq [goal [(list isCapital (list CapitalOfFn France) Yes)
                  (list isCapital (list CapitalOfFn France) '?w)]]
      (testing (str "the ground and open forms of " (pr-str goal))
        (is (= 1 (count (v/ask kb goal 'CxUniverse))))
        (is (= 1 (count (v/sentexes-matching kb goal 'CxUniverse))))
        (is (= 1 (count (v/prove kb [goal] 'CxUniverse))))
        (testing "the anytime ask is the same ask, not a differently-prepared one"
          (let [r (v/ask-within kb goal 'CxUniverse {})]
            (is (= :complete (:status r)))
            (is (= (v/ask kb goal 'CxUniverse) (:results r)))))
        (testing "and so are the two levels that claim to be the engine's dispatch"
          (is (= 1 (count (v/lookup kb 6 goal 'CxUniverse))))
          (is (= 1 (count (v/lookup kb 7 goal 'CxUniverse)))))))))

(tu/deftest-kb an-exceptWhen-query-meets-the-constant-its-fact-was-stored-under
  ;; The write walk descends a rule's antecedents, so an `(unknown <NAT goal>)` reifies
  ;; along with the rule around it.  An `exceptWhen`'s conjuncts arrive as a **vector**,
  ;; which is a list of forms rather than a literal — and there the empty answer is not
  ;; merely a missing result.  An exception that cannot be answered does not hold
  ;; (docs/exceptions.md, the open-world reading), so the rule fires unguarded and
  ;; nothing says so.  One evaluator, so all three chainers or none.
  (tu/with-terms [CapitalOfFn France isCapital Yes bird flies Tweety]
    (v/assert kb (list 'reifiable_function CapitalOfFn) 'CxUniverse)
    (v/assert kb (list bird Tweety) 'CxUniverse)
    (v/assert kb (list isCapital (list CapitalOfFn France) Yes) 'CxUniverse)
    (v/assert kb (list 'exceptWhen [(list isCapital (list CapitalOfFn France) Yes)]
                       (list 'set/defaultRule
                             (list 'implies (list bird '?x) (list flies '?x))))
              'CxUniverse)
    (is (v/ask? kb (list isCapital (list CapitalOfFn France) Yes) 'CxUniverse)
        "the conjunct is answerable when it is asked as a goal")
    (is (empty? (v/sentexes-matching kb (list flies '?x) 'CxUniverse))
        "so forward chaining concludes nothing")
    (is (empty? (v/prove kb (list flies '?x) 'CxUniverse))
        "and the DFS proves nothing")
    (is (empty? (binding [v/*query-engine* :inference
                          v/*query-options*  {:max-depth 3}]
                  (v/prove kb (list flies '?x) 'CxUniverse)))
        "and neither does the node engine")))

;; ---- genlResult + rewriteOf-to-real-term ---------------------------------

(tu/deftest-kb result-genl-materializes-a-subtype-edge
  (tu/with-terms [SubtypeFn Base super]
    (v/assert kb (list 'reifiable_function SubtypeFn) 'CxUniverse)
    (v/assert kb (list 'genl super 'thing) 'CxUniverse)
    (v/assert kb (list 'genlResult SubtypeFn super) 'CxUniverse)
    (let [h (v/assert kb (list 'studies 'Alice (list SubtypeFn Base)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (testing "the minted constant is a subtype of the result type"
        (is (nat/reified-nat-symbol? k))
        (is (v/genl? kb k super))))))

(tu/deftest-kb rewriteof-reifies-a-nat-to-an-existing-real-term
  (tu/with-terms [CapitalFn France Paris]
    (v/assert kb (list 'reifiable_function CapitalFn) 'CxUniverse)
    ;; (CapitalFn France) should reify to the real Paris, not a fresh constant
    (v/assert kb (list 'rewriteOf Paris (list CapitalFn France)) 'CxUniverse)
    (let [h (v/assert kb (list 'locatedIn (list CapitalFn France) 'Europe) 'CxUniverse)]
      (testing "the NAT resolves to the declared real term"
        (is (= (list 'locatedIn Paris 'Europe) (:sentence (v/sentex kb h))))
        (is (seq (v/sentexes-matching kb (list 'locatedIn (list CapitalFn France) '?where) '?ctx)))))))

(tu/deftest-kb two-rewrite-declarations-mint-fresh-rather-than-electing-one
  ;; `rewrite-target` answers only a **unique** believed declaration, as
  ;; `correspondence-of` answers its twin question: picking between two by whichever
  ;; the retrieval yielded first would store `(likes Tom Mary)` or `(likes Tom
  ;; Maria)` according to arrival order — divergent stored state, inherited by every
  ;; later read.  Two declarations are a disagreement, not a tie to break.
  (tu/with-terms [MotherFn Muffet Mary Maria]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'rewriteOf Mary (list MotherFn Muffet)) 'CxUniverse)
    (v/assert kb (list 'rewriteOf Maria (list MotherFn Muffet)) 'CxUniverse)
    (let [h      (v/assert kb (list 'likes 'Tom (list MotherFn Muffet)) 'CxUniverse)
          stored (nth (:sentence (v/sentex kb h)) 2)]
      (is (nat/reified-nat-symbol? stored)
          "a fresh constant stands until the disagreement is resolved")
      (is (not (contains? #{Mary Maria} stored))))))

;; ---- recover: the reifiable gate + reified NAT data survive a rebuild -----------

(tu/deftest-kb nat-data-survives-recover
  ;; the reifiable prop and the termOfUnit / result-type facts are all durable, so a
  ;; rebuild from the records must reconstruct the gate, dedup, and expansion — else a
  ;; recovered KB would disagree with the running one about what a NAT reifies to.
  ;; `recover` rebuilds the taxonomy + JTMS in place from the store (it adds no
  ;; sentex), so the fixture's net-neutral teardown still restores the baseline.
  (tu/with-terms [FruitFn AppleTree fruit]
    (v/assert kb (list 'reifiable_function FruitFn) 'CxUniverse)
    (v/assert kb (list 'result FruitFn fruit) 'CxUniverse)
    (let [h (v/assert kb (list 'color (list FruitFn AppleTree) 'Red) 'CxUniverse)
          k (k-of kb h)]
      (v/recover kb)
      (testing "the gate, the constant map, and the materialized type all rebuild"
        (is (true? (nat/any-reifiable-functions? kb)))
        (is (= (list FruitFn AppleTree) (nat/nat-expression kb k)))
        (is (= k (nat/dedup-constant kb (list FruitFn AppleTree))))
        (is (seq (v/sentexes-matching kb (list fruit k) '?ctx))))
      (testing "a fresh NAT still dedups to the same constant after recovery"
        (let [h2 (v/assert kb (list 'taste (list FruitFn AppleTree) 'Sweet) 'CxUniverse)]
          (is (= k (k-of kb h2))))))))

;; ---- the corresponding predicate -----------------------------------------
;;
;; `(functionCorrespondingPredicate F P N)` says the function and the predicate state
;; one relationship, so the reify reads it **both** ways: an application resolves to
;; the value `P` already names, and a constant minted for want of one is projected
;; back onto `P`.  What the tests below are really about is the seam between those
;; two — whichever of the application, the fact and the declaration lands last, the KB
;; ends up holding one term for one application.

(tu/deftest-kb a-corresponding-fact-names-the-term-an-application-reifies-to
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'CxUniverse)
    (v/assert kb (list motherOf Muffet Mary) 'CxUniverse)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)]
      (testing "the application resolves to the value, and mints nothing beside it"
        (is (= (list caresFor Bob Mary) (:sentence (v/sentex kb h))))
        (is (empty? (v/sentexes-matching kb (list 'termOfUnit '?k (list MotherFn Muffet))
                                         'CxUniverse))))
      (testing "a query written with the application still finds it"
        (is (= [{'?w Bob}] (v/ask kb (list caresFor '?w (list MotherFn Muffet)) 'CxUniverse)))))))

(tu/deftest-kb an-application-with-no-value-mints-a-constant-that-answers-the-predicate
  (tu/with-terms [MotherFn motherOf Muffet Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'CxUniverse)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (testing "no value is known, so the expression mints a placeholder"
        (is (nat/reified-nat-symbol? k)))
      (testing "and the placeholder is projected onto the corresponding predicate"
        (is (= [{'?m k}] (v/ask kb (list motherOf Muffet '?m) 'CxUniverse)))))))

(tu/deftest-kb a-value-arriving-after-the-mint-retires-the-placeholder
  ;; the order-independence case.  The fact and the application say the same thing, so
  ;; whichever lands second must not leave the KB with two values for one application.
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'CxUniverse)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (nat/reified-nat-symbol? k))
      (v/assert kb (list motherOf Muffet Mary) 'CxUniverse)
      (testing "one value, and it is the one somebody named"
        (is (= [{'?m Mary}] (v/ask kb (list motherOf Muffet '?m) 'CxUniverse))))
      (testing "the use of the placeholder migrated onto it"
        (is (seq (v/sentexes-matching kb (list caresFor Bob Mary) '?ctx))))
      (testing "and the expression still resolves — to the real term now"
        (is (= Mary (nat/dedup-constant kb (list MotherFn Muffet))))
        (is (= Mary (nat/correspondence-value kb (list MotherFn Muffet))))))))

(tu/deftest-kb a-declared-position-puts-the-value-where-it-says
  ;; Cyc's own example: (StreetCornerFn XING DIRECTION) = LOT exactly when
  ;; (streetCornerOf LOT XING DIRECTION), so the value is argument 1 and not the last.
  (tu/with-terms [StreetCornerFn streetCornerOf Xing1 North Lot7 ownedBy Alice]
    (v/assert kb (list 'reifiable_function StreetCornerFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate StreetCornerFn streetCornerOf 1)
              'CxUniverse)
    (v/assert kb (list streetCornerOf Lot7 Xing1 North) 'CxUniverse)
    (let [h (v/assert kb (list ownedBy (list StreetCornerFn Xing1 North) Alice) 'CxUniverse)]
      (is (= (list ownedBy Lot7 Alice) (:sentence (v/sentex kb h)))))))

(tu/deftest-kb a-declaration-arriving-last-reconciles-what-was-already-minted
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (nat/reified-nat-symbol? k))
      (v/assert kb (list motherOf Muffet Mary) 'CxUniverse)
      (testing "before the declaration the two terms are unrelated"
        (is (= k (nat/dedup-constant kb (list MotherFn Muffet)))))
      (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'CxUniverse)
      (testing "declaring it last reaches the state declaring it first would have"
        (is (= [{'?m Mary}] (v/ask kb (list motherOf Muffet '?m) 'CxUniverse)))
        (is (seq (v/sentexes-matching kb (list caresFor Bob Mary) '?ctx)))
        (is (= Mary (nat/dedup-constant kb (list MotherFn Muffet))))))))

(tu/deftest-kb a-declaration-arriving-last-projects-a-placeholder-that-has-no-value
  (tu/with-terms [MotherFn motherOf Muffet Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (empty? (v/ask kb (list motherOf Muffet '?m) '?ctx)))
      (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'CxUniverse)
      (testing "the constant minted before the declaration is projected by it"
        (is (= [{'?m k}] (v/ask kb (list motherOf Muffet '?m) 'CxUniverse)))))))

(tu/deftest-kb two-declarations-for-one-function-decide-nothing
  ;; Two correspondences are two different claims about what `(F a…)` denotes.  Choosing
  ;; between them would have to key on a handle, which is the one thing belief may never
  ;; do — so neither is read, and the application mints as if none were declared.
  (tu/with-terms [MotherFn motherOf parentOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn parentOf) 'CxUniverse)
    (v/assert kb (list motherOf Muffet Mary) 'CxUniverse)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (nat/reified-nat-symbol? k))
      (is (not= Mary k))
      (testing "and neither predicate is projected onto"
        (is (empty? (v/ask kb (list parentOf Muffet '?m) '?ctx)))
        (is (= [{'?m Mary}] (v/ask kb (list motherOf Muffet '?m) 'CxUniverse)))))))

(tu/deftest-kb retracting-the-declaration-stops-the-application-resolving
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor sees]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (let [d (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'CxUniverse)]
      (v/assert kb (list motherOf Muffet Mary) 'CxUniverse)
      (is (= Mary (nat/correspondence-value kb (list MotherFn Muffet))))
      (v/retract! kb d)
      (testing "the declaration is belief-following, so the reify stops reading it"
        (is (nil? (nat/correspondence-value kb (list MotherFn Muffet))))
        (let [h (v/assert kb (list sees Bob (list MotherFn Muffet)) 'CxUniverse)]
          (is (nat/reified-nat-symbol? (nth (:sentence (v/sentex kb h)) 2))))))))

(tu/deftest-kb an-ill-formed-correspondence-is-refused
  (tu/with-terms [MotherFn motherOf Mary]
    ;; the arity-1 row is caught by the NAMING door, which runs upstream of `wff`: a
    ;; camelCase functor at arity 1 is a unary predicate wearing a relation's spelling,
    ;; and `problems` names that before `wff` gets to count the arguments
    (doseq [[what expected s]
            [["one argument"      :naming
              (list 'functionCorrespondingPredicate MotherFn)]
             ["four arguments"    :not-well-formed
              (list 'functionCorrespondingPredicate MotherFn motherOf 2 2)]
             ["an individual"     :not-well-formed
              (list 'functionCorrespondingPredicate MotherFn Mary)]
             ["a position that is not a positive integer" :not-well-formed
              (list 'functionCorrespondingPredicate MotherFn motherOf 'first)]]]
      (let [e (try (v/assert kb s 'CxUniverse) nil
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (some? e) what)
        (is (= expected (:type (ex-data e))) what)))))

(tu/deftest-kb a-correspondence-survives-recover
  ;; the declaration is read through the index rather than a taxonomy cache, so a
  ;; rebuild has nothing to reconstruct — which is the claim worth pinning, since a
  ;; recovered KB that stopped resolving applications would be a restart changing an
  ;; answer.
  (tu/with-terms [MotherFn motherOf Muffet Mary Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'CxUniverse)
    (v/assert kb (list motherOf Muffet Mary) 'CxUniverse)
    (v/recover kb)
    (is (= Mary (nat/correspondence-value kb (list MotherFn Muffet))))
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)]
      (is (= (list caresFor Bob Mary) (:sentence (v/sentex kb h)))))))

(tu/deftest-kb a-projection-does-not-keep-an-orphaned-placeholder-alive
  ;; the projection states what the constant *is*, so it is bookkeeping like a result
  ;; type — a constant whose only remaining sentex is its own projection has no live
  ;; use, and treating one as a use would make every placeholder immortal.
  (tu/with-terms [MotherFn motherOf Muffet Bob caresFor]
    (v/assert kb (list 'reifiable_function MotherFn) 'CxUniverse)
    (v/assert kb (list 'functionCorrespondingPredicate MotherFn motherOf) 'CxUniverse)
    (let [h (v/assert kb (list caresFor Bob (list MotherFn Muffet)) 'CxUniverse)
          k (nth (:sentence (v/sentex kb h)) 2)]
      (is (seq (v/ask kb (list motherOf Muffet '?m) '?ctx)))
      (v/retract! kb h)
      (testing "the placeholder, its map and its projection all go"
        (is (nil? (nat/dedup-constant kb (list MotherFn Muffet))))
        (is (empty? (kb/find-sentexes kb k)))
        (is (empty? (v/ask kb (list motherOf Muffet '?m) '?ctx)))
        (is (empty? (nat/orphaned-constants kb)))))))

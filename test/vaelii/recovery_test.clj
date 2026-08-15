;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.recovery-test
  "Persistence/recovery: rebuild the in-memory taxonomy and JTMS from the durable
  stores, and atomicity of a rejected assert.

  This file's subject IS the durable store, and it deliberately restarts a second
  KB over the same databases, so teardown is a clear rather than JTMS retraction.
  The fixture still guards net-neutrality: it clears at both ends and asserts the
  store is empty on the way out."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.starter :as starter]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.test-util :as tu]
            [vaelii.world :as world]))

(use-fixtures :each
  (fn [f]
    (let [kb (tu/fresh)]                       ; cleared empty
      (binding [tu/*kb* kb]
        (let [before (tu/content-count kb)]    ; {:sentexes 0 :justifications 0}
          (try (f)
               (finally
                 (tu/clear-kb! kb)                ; durable content is under test — clesh to clean
                 (is (= before (tu/content-count kb))
                     "recovery test did not return the store to empty"))))))))

(defn- restart
  "Simulate a process restart: a fresh KB over the same databases, with only the
  durable stores — the in-memory taxonomy and JTMS start empty."
  []
  (tu/test-kb))

(tu/deftest-kb recover-rebuilds-taxonomy-and-beliefs
  (starter/load-into kb)
  (world/load-cast kb)                        ; the cast lives in the tests now
  (let [gp (:id (first (v/sentexes-matching kb '(grandparentOf Tom Ann) 'CxNaturalWorld)))]
    (let [kb2 (restart)]
      (testing "before recover, the in-memory graph is empty"
        (is (not (v/isa? kb2 'Muffet 'animal)))           ; taxonomy not rebuilt yet
        (is (not (v/in? kb2 gp))))                        ; jtms not rebuilt yet
      (v/recover kb2)
      (testing "after recover, the taxonomy answers isa? again"
        (is (v/isa? kb2 'Muffet 'animal))
        (is (v/disjoint? kb2 'dog 'cat)))
      (testing "the JTMS is rebuilt: the derived grandparent is IN with its support"
        (is (v/in? kb2 gp))
        (is (seq (v/supporting-justifications kb2 gp))))
      (testing "querying and retraction work on the recovered KB"
        (is (seq (v/sentexes-matching kb2 '(grandparentOf Tom Ann) 'CxNaturalWorld)))
        (let [bob (:id (first (v/sentexes-matching kb2 '(parentOf Bob Ann) 'CxNaturalWorld)))]
          (v/retract! kb2 bob)
          ;; Tom→Bob→Ann gone, but Tom→Bob→Carol keeps grandparentOf via Carol? no —
          ;; retracting (parentOf Bob Ann) removes only (grandparentOf Tom Ann)
          (is (empty? (v/sentexes-matching kb2 '(grandparentOf Tom Ann) 'CxNaturalWorld))))))))

(tu/deftest-kb recover-rebuilds-every-cache-not-only-the-transitive-ones
  ;; `clear-relations!` must empty all six caches, not `:genl` and `:genlCx`
  ;; alone: a rebuild that merged into whatever `:disjoint` / `:props` / `:inverse`
  ;; already held can only ever *add*, so an entry whose sentex is gone would survive
  ;; the recovery meant to re-derive it.  Here the second KB is given a stale entry by
  ;; hand, standing in for one left over from before the restart.
  (let [dog (tu/tmp-type) cat (tu/tmp-type)
        stale-a (tu/tmp-type) stale-b (tu/tmp-type) ghostPred (tu/tmp-pred)]
    (v/assert kb (list 'disjoint dog cat) 'CxUniverse)
    (let [kb2 (restart)]
      ;; entries with no sentex behind them anywhere in the store
      (tax/add-disjoint (:taxonomy kb2) stale-a stale-b 9999)
      (tax/mark-prop (:taxonomy kb2) :transitive ghostPred 9999)
      (is (v/disjoint? kb2 stale-a stale-b))
      (is (v/has-prop? kb2 :transitive ghostPred))
      (v/recover kb2)
      (testing "recovery drops what the store does not back"
        (is (not (v/disjoint? kb2 stale-a stale-b)))
        (is (not (v/has-prop? kb2 :transitive ghostPred))))
      (testing "and re-derives what it does"
        (is (v/disjoint? kb2 dog cat))))))

(tu/deftest-kb recover-does-not-answer-through-an-unsupported-edge
  ;; The replay reads **stored** declarations, so an edge whose record carries no premise
  ;; mark and no justification is activated exactly as a supported one is — and nothing in
  ;; the rebuild opposes it.  No defeat, no block, no supersession: the closing settle has
  ;; no event to react to, and the region-scoped reconcile it runs when it does have one
  ;; would not name this edge either.  So recovery reconciles against belief itself, before
  ;; the settle.  The defeated twin of the claim is
  ;; `taxonomy_belief_test/recover-does-not-revive-a-defeated-edge`, which the opposition
  ;; alone would carry; a store whose records lost their strength marks is what presents
  ;; the unsupported case, and the record store's own API is what stages it here.
  (tu/with-terms [dog_t mammal_t Rex]
    (v/assert kb (list 'genl dog_t mammal_t) 'CxUniverse)
    (v/assert kb (list dog_t Rex) 'CxUniverse)
    (let [h (v/handle-of kb (list 'genl dog_t mammal_t) 'CxUniverse)]
      (p/unmark-premise! (:records kb) h)     ; the record survives, its support does not
      (let [kb2 (restart)]
        (v/recover kb2)
        (is (not (v/in? kb2 h)) "nothing stored supports the edge")
        (testing "so nothing derived from the closure answers through it"
          (is (not (contains? (set (v/genls kb2 dog_t)) mammal_t)))
          (is (not (contains? (set (v/types kb2)) mammal_t)))
          (is (not (v/isa? kb2 Rex mammal_t))))
        (testing "and the supporter is still stored, so re-marking it brings the edge back"
          (p/mark-premise (:records kb2) h :default)
          (v/recover kb2)
          (is (v/in? kb2 h))
          (is (contains? (set (v/genls kb2 dog_t)) mammal_t))
          (is (v/isa? kb2 Rex mammal_t)))))))

(tu/deftest-kb recover-rebuilds-disjoint-metatype-membership
  ;; A metatype's members are cached in memory, not stored: the only durable trace is
  ;; the `(M T)` sentexes themselves.  So recovery has to re-read them *after* the
  ;; metatypes are known, or a restart silently loses every pair the metatype
  ;; separated — with no `(disjoint a b)` sentex left to cover for it, as there used
  ;; to be when the clique was materialized.
  (let [animalSpecies (tu/tmp-pred) dog (tu/tmp-type) cat (tu/tmp-type)]
    (v/assert kb (list 'disjointMetatype animalSpecies) 'CxUniverse)
    (v/assert kb (list animalSpecies dog) 'CxUniverse)
    (v/assert kb (list animalSpecies cat) 'CxUniverse)
    (is (v/disjoint? kb dog cat))
    (let [kb2 (restart)]
      (v/recover kb2)
      (is (v/disjoint? kb2 dog cat)
          "membership must be rebuilt, not just the metatype mark"))))

(tu/deftest-kb recover-agrees-about-a-defeated-declaration
  ;; The four flat caches follow belief now, like genl: a defeated `(disjoint A B)`
  ;; stops constraining (docs/taxonomy.md).  Recovery must reproduce that, not merely
  ;; be self-consistent.  `rebuild-taxonomy` replays the *stored* disjoint (the
  ;; defeated one included) so `:cache-support` records every asserting sentex, and the
  ;; reconcile `recover` runs over the replay then drops it by belief — the same answer
  ;; either side of a restart.  A belief-filtered rebuild would lose the disbelieved
  ;; supporter and clearing its defeat could never revive the entry.
  (let [dog (tu/tmp-type) cat (tu/tmp-type)]
    (v/assert kb (list 'disjoint dog cat) 'CxUniverse {:strength :default})
    (v/assert kb (list 'not (list 'disjoint dog cat)) 'CxUniverse {:strength :monotonic})
    (let [before (v/disjoint? kb dog cat)
          kb2    (restart)]
      (is (not before) "a defeated disjoint does not constrain in memory")
      (v/recover kb2)
      (is (not (v/disjoint? kb2 dog cat)) "nor after a restart")
      (is (= before (v/disjoint? kb2 dog cat))
          "the answer must not change across a restart"))))

(tu/deftest-kb recover-agrees-about-a-rule-concluded-equality
  ;; The live path reads the write and the rebuild reads the store, so a functor whose
  ;; two arms differ is a KB that disagrees with its own restart about what it entails.
  ;; A rule concluding one of the three equality relations is the case that asks it of
  ;; the closure: the conclusion is stored like any other, `rebuild-taxonomy` replays
  ;; every stored `rewriteOf` / `sameAs` / `equals`, and the derivation path has to have
  ;; put the same edge in the running KB.  All three relations, since the arm is
  ;; dispatched by functor.  The live half of the claim is
  ;; `equality-test/a-rule-concluding-an-equality-merges-like-an-asserted-one`.
  (doseq [rel '[rewriteOf sameAs equals]]
    (testing (str "a rule concluding " rel)
      (let [aliasOf  (tu/tmp-pred "alias")
            caresFor (tu/tmp-pred "caresFor")
            Tom      (tu/tmp-ind "Tom")
            [lo hi]  (sort [(tu/tmp-ind "Ann") (tu/tmp-ind "Ann")])]
        (v/assert-rule kb [(list aliasOf '?x '?y)] (list rel '?x '?y) 'CxUniverse)
        (v/assert kb (list caresFor hi Tom) 'CxUniverse)
        (v/assert kb (list aliasOf lo hi) 'CxUniverse)
        (let [live-class (set (v/equiv-class kb hi))
              live-rep   (v/representative kb hi)
              live-in?   (v/in? kb (v/handle-of kb (list caresFor hi Tom) 'CxUniverse))
              kb2        (restart)]
          (v/recover kb2)
          (testing "the rebuilt closure holds what the live one holds"
            (is (= live-class (set (v/equiv-class kb2 hi)))
                (str "the running KB and its own rebuild disagree about " hi "'s class: "
                     (pr-str live-class) " live, "
                     (pr-str (set (v/equiv-class kb2 hi))) " rebuilt"))
            (is (= live-rep (v/representative kb2 hi))))
          (testing "and they agree about the displaced spelling"
            (is (= live-in?
                   (v/in? kb2 (v/handle-of kb2 (list caresFor hi Tom) 'CxUniverse)))
                "a restart changed whether the retired spelling is believed")))))))

(tu/deftest-kb recover-agrees-about-a-rule-concluded-disjoint-metatype
  ;; The same claim one functor over: `rebuild-taxonomy` replays every stored
  ;; `disjointMetatype`, so a mark a rule concluded has to separate the metatype's
  ;; members in the running KB as well, or the restart is what makes two types
  ;; disjoint.  The members here are asserted; a member a rule *concludes* is a
  ;; structural arm rather than a table entry and is where the derivation path stops
  ;; (docs/taxonomy.md, "What a rule may conclude").
  (let [seen (tu/tmp-pred "seen") m (tu/tmp-pred "kindOf")
        a    (tu/tmp-type "aa")   b (tu/tmp-type "bb")]
    (v/assert-rule kb [(list seen '?p)] (list 'disjointMetatype '?p) 'CxUniverse)
    (v/assert kb (list m a) 'CxUniverse)
    (v/assert kb (list m b) 'CxUniverse)
    (v/assert kb (list seen m) 'CxUniverse)
    (let [live (v/disjoint? kb a b)
          kb2  (restart)]
      (is live "a metatype a rule concluded does not separate its members")
      (v/recover kb2)
      (is (= live (v/disjoint? kb2 a b))
          "a restart changed whether the metatype separates its members"))))

(tu/deftest-kb rejected-assert-leaves-no-trace
  (let [dog (tu/tmp-type) animal (tu/tmp-type) muffet (tu/tmp-ind)]
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (let [n   (p/count-at (:index kb) [])
          ids (count (p/sentex-ids (:records kb)))]
      (testing "a not-well-formed assert writes nothing (checks precede writes)"
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list 'genl muffet animal) 'CxUniverse)))  ; genl on an individual
        (is (= n   (p/count-at (:index kb) [])))
        (is (= ids (count (p/sentex-ids (:records kb))))))
      (testing "a naming violation likewise"
        (is (thrown? clojure.lang.ExceptionInfo
                     (v/assert kb (list dog muffet) 'badContext)))               ; badContext is not a valid context
        (is (= n (p/count-at (:index kb) [])))))))

(tu/deftest-kb the-recover-option-selects-rebuild-warn-or-silence
  ;; open-kb over non-empty databases without recovery returns a KB whose empty TMS
  ;; and taxonomy make every query silently answer nothing.  `:recover?` defaults to
  ;; `:auto` — rebuild at construction (the test below pins the default itself);
  ;; `false` opts out silently, and `:warn` opts out with a log, leaving recovery to
  ;; the caller.
  (tu/with-terms [dog animal Muffet]
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (testing "{:recover? false} constructs an empty-memory KB (recovery is the caller's)"
      (let [kb2 (restart)]                       ; tu/test-kb pins :recover? false
        (is (empty? (v/sentexes-matching kb2 (list dog Muffet) 'CxUniverse)))))
    (testing "{:recover? :warn} likewise — it logs instead of rebuilding"
      (let [kbw (v/open-kb (assoc tu/scratch-space :recover? :warn))]
        (is (empty? (v/sentexes-matching kbw (list dog Muffet) 'CxUniverse)))
        (is (not (v/isa? kbw Muffet animal)))))
    (testing "{:recover? :auto} answers immediately"
      (let [kb3 (v/open-kb (assoc tu/scratch-space :recover? :auto))]
        (is (seq (v/sentexes-matching kb3 (list dog Muffet) 'CxUniverse)))
        (is (v/isa? kb3 Muffet animal))))))

(tu/deftest-kb recover-defaults-to-auto-when-unstated
  ;; The pin for the default itself.  The suite states `:recover?` on every KB it
  ;; builds (`tu/space-opts` pins false, the tests above spell :warn / :auto out), so
  ;; only this open does what a user's does — a non-empty durable store, no
  ;; `:recover?` at all.  The contract: an unstated policy behaves as `:auto`, so the
  ;; KB answers at construction rather than handing back one whose queries silently
  ;; answer nothing.
  (tu/with-terms [dog animal Muffet]
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (v/assert kb (list dog Muffet) 'CxUniverse)
    (let [kb2 (v/open-kb (dissoc tu/scratch-space :recover?))]
      (is (seq (v/sentexes-matching kb2 (list dog Muffet) 'CxUniverse))
          "believed at construction — the unstated default recovered")
      (is (v/isa? kb2 Muffet animal)))))

(tu/deftest-kb recover-re-supersedes-a-schematic-rewrite
  ;; A schematic (equals L R) normalizes stored terms to justified twins and supersedes
  ;; the un-normalized originals.  Supersession is derived from the rewrite rules, not
  ;; stored, so recover must re-establish it (via `recovered-supersessions`) — else both
  ;; the original and its twin would be believed after a restart.  The twin's
  ;; justification IS stored, so it survives; only supersession needs re-deriving.
  (tu/with-terms [pp gpp chainR Nn]
    (v/assert kb (list 'equals (list pp (list pp '?x)) (list gpp '?x)) 'CxUniverse)
    (v/assert kb (list chainR (list pp (list pp Nn))) 'CxUniverse)
    (let [orig (v/handle-of kb (list chainR (list pp (list pp Nn))) 'CxUniverse)
          twin (v/handle-of kb (list chainR (list gpp Nn)) 'CxUniverse)]
      (is (some? twin) "the twin was created")
      (is (v/in? kb twin))
      (is (not (v/in? kb orig)) "the original is superseded before the restart")
      (let [kb2 (restart)]
        (v/recover kb2)
        (testing "after recover the twin is believed and the original stays superseded"
          (is (v/in? kb2 twin))
          (is (not (v/in? kb2 orig)))
          (is (seq (v/sentexes-matching kb2 (list chainR (list gpp Nn)) 'CxUniverse))))))))

(tu/deftest-kb recover-survives-a-predicate-and-type-merge
  ;; Round-two rewriteOf merges a predicate / type by moving its functor uses onto the
  ;; representative — facts, the genl closure, and rules (docs/equality.md).  The twins
  ;; (moved fact, edge, rule, rule conclusion) are stored justifications and the rule index
  ;; lives in the index, so both survive the restart; supersession alone is re-derived by
  ;; `recovered-supersessions`.
  (tu/with-terms [bornIn birthplaceOf knownPlace Ada London
                  dog canine animal Rex]
    (v/assert kb (list 'implies (list birthplaceOf '?x '?c) (list knownPlace '?c)) 'CxUniverse)
    (v/assert kb (list birthplaceOf Ada London) 'CxUniverse)
    (v/assert kb (list 'rewriteOf bornIn birthplaceOf) 'CxUniverse)   ; predicate merge
    (v/assert kb (list 'genl dog animal) 'CxUniverse)
    (v/assert kb (list dog Rex) 'CxUniverse)
    (v/assert kb (list 'rewriteOf canine dog) 'CxUniverse)             ; type merge
    (let [moved (v/handle-of kb (list bornIn Ada London) 'CxUniverse)
          known (v/handle-of kb (list knownPlace London) 'CxUniverse)
          orig  (v/handle-of kb (list birthplaceOf Ada London) 'CxUniverse)]
      (is (v/in? kb moved))
      (is (v/in? kb known) "the migrated rule concluded before the restart")
      (let [kb2 (restart)]
        (v/recover kb2)
        (testing "the predicate merge survives: fact moved, original superseded, rule rebuilt"
          (is (v/in? kb2 moved))
          (is (not (v/in? kb2 orig)))
          (is (v/in? kb2 known)))
        (testing "and the recovered rule index still carries the migrated rule"
          (tu/with-terms [Bob Paris]
            (v/assert kb2 (list bornIn Bob Paris) 'CxUniverse)
            (is (seq (v/sentexes-matching kb2 (list knownPlace Paris) 'CxUniverse)))))
        (testing "the type merge survives: isa? answers under the representative"
          (is (v/isa? kb2 Rex canine 'CxUniverse))
          (is (v/isa? kb2 Rex animal 'CxUniverse))
          (is (contains? (set (v/genls kb2 canine)) animal)))))))

(tu/deftest-kb recover-re-supersedes-a-spelling-only-a-context-retired
  ;; Supersession is the *reader's*: a term can head its whole class globally and still
  ;; be retired inside a context whose visible edges elect somebody else, when the
  ;; `rewriteOf` that made it preferred is one that context cannot see.  Nominating
  ;; recovery's candidates by the global election would drop exactly those and the KB
  ;; would come back believing both spellings (docs/equality.md).
  (tu/with-terms [admires Kim Tango Yankee Zulu Xray CxVis CxHid]
    (v/assert kb (list 'genlCx CxVis 'CxUniverse) 'CxUniverse)
    (v/assert kb (list 'genlCx CxHid 'CxUniverse) 'CxUniverse)
    ;; Vis sees: Tango~Yankee and Yankee over Zulu  -> Vis elects Yankee
    (v/assert kb (list 'sameAs Tango Yankee)   CxVis)
    (v/assert kb (list 'rewriteOf Yankee Zulu) CxVis)
    ;; Hid alone sees Tango over Xray, which is what makes Tango the *global* head
    (v/assert kb (list 'rewriteOf Tango Xray)  CxHid)
    (v/assert kb (list admires Kim Tango) CxVis)
    (is (= Tango (v/representative kb Tango)) "Tango heads the class globally")
    (is (= Yankee (v/representative kb Tango CxVis)) "...and is retired inside Vis")
    (let [orig (v/handle-of kb (list admires Kim Tango) CxVis)
          twin (v/handle-of kb (list admires Kim Yankee) CxVis)]
      (is (some? twin))
      (is (not (v/in? kb orig)) "superseded before the restart")
      (let [kb2 (restart)]
        (v/recover kb2)
        (is (v/in? kb2 twin))
        (is (not (v/in? kb2 orig)) "and still superseded after it")
        (is (= [{'?x Yankee}] (v/query kb2 (list admires Kim '?x) CxVis))
            "so Vis reports the one fact once, in the name Vis elects")))))

(tu/deftest-kb recover-gives-a-rule-back-the-class-its-assertion-stated
  ;; A rule's premise strength is now the caller's to state, so it is a value that has
  ;; to survive a restart like a fact's.  The rebuild reads `premise-strength` per
  ;; stored premise and marks each at what it finds, so nothing here is rule-specific —
  ;; which is the claim, since a rebuild that re-marked rules at a constant would put
  ;; a known-true rule back defeasible and no read of the rule would say so.
  (tu/with-terms [bird flies]
    (let [rule (list 'implies (list bird '?x) (list flies '?x))
          h    (v/assert-rule kb [(list bird '?x)] (list flies '?x) 'CxUniverse
                              {:strength :monotonic})]
      (is (= :monotonic (:strength (v/sentex kb h))))
      (let [kb2 (restart)]
        (v/recover kb2)
        (is (= :monotonic (:strength (v/sentex kb2 h))) "the record came back with it")
        (is (true? (v/premise? kb2 h)) "and as a premise")
        (is (= :monotonic (v/defeat-class kb2 h)) "so the class reads back after the rebuild")
        (is (= h (v/handle-of kb2 rule 'CxUniverse)) "at the same handle")))))

(tu/deftest-kb recover-replays-an-inherited-firing-and-its-reasons
  ;; A firing that joined on an inherited claim rests on justifications like any
  ;; other, so the rebuild replays it — and its recorded reasons still carry
  ;; retraction afterwards, which is what makes the replay a belief and not a copy.
  (tu/with-terms [dog_t cat_t chihuahua_t maine_coon_t largerThan outweighs]
    (v/with-deferred-settle kb
      (v/assert kb (list 'genl chihuahua_t dog_t) 'CxUniverse)
      (v/assert kb (list 'genl maine_coon_t cat_t) 'CxUniverse)
      (v/assert kb (list 'argPreserving largerThan 1 'genl) 'CxUniverse)
      (v/assert kb (list 'argPreserving largerThan 2 'genl) 'CxUniverse)
      (v/assert kb (list largerThan dog_t cat_t) 'CxUniverse))
    (v/assert kb (list 'implies (list largerThan '?x '?y) (list outweighs '?x '?y))
              'CxUniverse)
    (let [goal (list outweighs chihuahua_t maine_coon_t)
          h    (v/handle-of kb goal 'CxUniverse)]
      (is (v/in? kb h))
      (let [kb2 (restart)]
        (v/recover kb2)
        (is (v/in? kb2 h) "the firing is IN again after the rebuild")
        (let [reasons (into #{}
                            (comp (mapcat :because) (map :sentence))
                            (:support (v/why kb2 h)))]
          (is (contains? reasons (list largerThan dog_t cat_t)))
          (is (contains? reasons (list 'genl chihuahua_t dog_t)))
          (is (contains? reasons (list 'argPreserving largerThan 1 'genl))))
        (testing "a post-recover retraction of a reason still withdraws it"
          (v/retract! kb2 (v/handle-of kb2 (list 'genl chihuahua_t dog_t) 'CxUniverse))
          (is (not (v/in? kb2 h))))))))

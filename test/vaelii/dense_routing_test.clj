;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.dense-routing-test
  "Which index family lands in which *representation*, in the two dense backends.

  The dense backends exist for one reason — density — and density is the one property
  their oracles cannot see.  `dense_kv_oracle_test` and `dense_roots_oracle_test` prove
  set-equality against `MemoryKvBackend`, and both backends keep a **fallback** for keys
  they don't route: a family the router fails to recognize is stored as an ordinary
  boxed set, answers every read identically, and passes every oracle while buying
  nothing.  The projection tests can't see it either, since the fallback returns the
  entries verbatim.  So a misrouted family is invisible everywhere except here.

  The keys are never spelled by hand.  A hand-spelled key tests the router against the
  test's idea of a key name, which is exactly the agreement that can drift — this
  namespace builds a real KB, reads back the keys `vaelii.impl.kv` actually wrote, and
  checks each one's stored representation against its family.  A family nobody has
  declared fails as `:unclassified`, so adding an index family forces a routing decision
  rather than silently taking the fallback."
  (:require [clojure.set :as set]
            [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as vr]
            [vaelii.test-util :as tu])
  (:import (vaelii.impl.types.postings IntPostings)))

;;; ── the families ──────────────────────────────────────────────────────

(defn- family
  "The family `k` belongs to — the granularity a routing decision is made at.  Keyed on
  the shape rather than the whole key, since a family has one entry per term."
  [k]
  (if-not (vector? k)
    [:unclassified k]
    (case (nth k 0)
      :trie            [:trie (nth k 1)]
      (:argument-root :predicate-extent :rule-antecedent :rule-consequent :rule-extent
                      :opposed :tax-support :mint :mint-in :self-tuple)
      [(nth k 0) (nth k 1)]
      :exception-index (if (= :rules (nth k 1)) [:exception-index :rules] [:exception-index :predicate])
      (:context-root :argument-slot :unary-slot :term-index :term-roster :rule-antecedent-keys
                     :opposed-in :opposed-bodies :tax-installs :mint-terms :unary-multi
                     :shape-count :shape-lengths)
      [(nth k 0)]
      [:unclassified k])))

(def ^:private handle-families
  "Families whose value is a set of **handles** — the ones a dense backend must pack into
  int postings.  Handles fit an `int`, which is what makes packing possible at all."
  #{[:trie :handles] [:argument-root :handles] [:predicate-extent :handles]
    [:context-root] [:term-index]
    [:rule-antecedent :handles] [:rule-consequent :handles] [:rule-extent :handles]
    [:opposed :handles] [:opposed-in] [:self-tuple :handles]
    [:tax-support :handles] [:mint :handles] [:mint-in :handles]
    [:exception-index :predicate] [:exception-index :rules]})

(def ^:private count-families
  "Families whose value is a subtree count — an integer, a plain counter where a backend
  stores it.  `dense-roots` stores no argument-node count and answers it from the node's
  leaves, so on the columnar store it is read through `kv-get` and found in neither the
  packed map nor the fallback.  The other three count tries' counts, one per predicate or
  rule key, are counters in its fallback."
  #{[:trie :count] [:argument-root :count] [:predicate-extent :count]
    [:rule-antecedent :count] [:rule-consequent :count] [:rule-extent :count]
    [:opposed :count] [:tax-support :count] [:mint :count] [:mint-in :count] [:shape-count]
    [:self-tuple :count]})

(def ^:private other-families
  "Families whose value is deliberately *not* a handle set, so packing them as handles
  would be wrong rather than merely unrealized: the counts, the trie's child labels (path
  tokens — numbers among them, which is the case a value-type dispatch would
  misclassify), an argument node's children (contexts), the roster (term *names*), and
  the two slot rosters (*predicates* present at a slot, and those a term is the lone
  argument of — names, like the term roster's members)."
  (into #{[:trie :children] [:argument-root :children] [:predicate-extent :children]
          [:rule-antecedent :children] [:rule-consequent :children] [:rule-extent :children]
          [:opposed :children] [:self-tuple :children] [:term-roster] [:argument-slot] [:unary-slot]
          [:rule-antecedent-keys] [:opposed-bodies]
          [:tax-support :children] [:tax-installs]
          [:mint :children] [:mint-in :children] [:mint-terms] [:unary-multi] [:shape-lengths]}
        count-families))

(def ^:private interned-name-families
  "Name families the columnar roots pack anyway: a count trie's node children are
  contexts, and `dense-roots` holds each as its id in the shared token dictionary, in a
  posting under a packed key (an argument node's carries its interned `(pred, pos)`
  scope), so the family's per-node mass is ints rather than a boxed key and set in the
  fallback."
  #{[:argument-root :children] [:predicate-extent :children] [:rule-antecedent :children]
    [:rule-consequent :children] [:rule-extent :children] [:opposed :children]
    [:mint :children] [:self-tuple :children]})

(def ^:private unpackable-handle-families
  "Handle families the dense layout cannot int-route, and why.

  One, the taxonomy's supporter leaves; every other handle family packs. The one that
  carries the most names — the argument trie's leaf
  `[:argument-root :handles [pred pos term ctx]]`, index layout 4 in `kv.clj` — packs
  because its `(pred, pos, ctx)` scope is interned to a dense id of its own and rides the
  `pos` field (`dense-roots`' `argfam-id`), so the packed long spends family 8 bits |
  scope 24 | term id 32 and no family is left keyed by a boxed vector.

  A family added here must state which of the two it lacks: a term the shared dictionary
  can intern, or a field in the packed long to put it in.

  `[:tax-support :handles [k ctx]]` lacks the term: its node `k` is a taxonomy key, a
  vector such as `[:genl a b]` or `[:disjoint #{a b}]`, which the dictionary does not
  intern."
  #{[:tax-support :handles]})

;;; ── the KB, and the backends under test ───────────────────────────────

;; Own db numbers, outside the suite's block: this namespace opens whole KBs on named
;; backends rather than running on whichever one the suite's gate selected.
(defn- open-kb! [backend space]
  (doto (v/open-kb {:backend backend :space space
                    :recover? false})
    (tu/clear-kb!)))

(defn- build!
  "One KB touching every index family: a ragged trie (a numeric token, a negative fact),
  the context root, the argument trie and the predicate extent, both rule indexes, both halves of the exception index, the
  term index and the roster, and the mint family, which an argument declaration's mint
  writes with the entailment pinned on.  A family the fixture never writes cannot be checked, so the
  completeness assertion below fails when the fixture misses a family."
  [kb]
  (tu/with-terms [bird penguin animal flies feathered parentOf grandparentOf
                  Tweety Opus Ann Bob Cid CxRouting]
    (v/assert kb (list 'genl penguin bird) CxRouting {:strength :monotonic})
    (v/assert kb (list 'genl bird animal) CxRouting {:strength :monotonic})
    (v/assert kb (list 'genl animal 'thing) CxRouting {:strength :monotonic})
    (v/assert kb (list 'arg parentOf 1 animal) CxRouting {:strength :monotonic})
    ;; a rule with an exception — the rule index and both exception-index halves
    (v/assert kb (list 'exceptWhen (list penguin '?b)
                       (list 'set/defaultRule
                             (vr/rule-sentence [(list bird '?b)] (list flies '?b))))
              CxRouting)
    (v/assert kb (vr/rule-sentence [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                                   (list grandparentOf '?x '?z))
              CxRouting {:direction :forward})
    (v/assert kb (list bird Tweety) CxRouting {:strength :monotonic})
    (v/assert kb (list feathered Tweety) CxRouting)
    (v/assert kb (list bird Opus) CxRouting)
    (v/assert kb (list penguin Opus) CxRouting)
    (tu/with-entailing
      (v/assert kb (list parentOf Ann Bob) CxRouting)
      (v/assert kb (list parentOf Bob Cid) CxRouting))
    (v/assert kb (list 'bornInYear Tweety 1970) CxRouting)   ; a numeric trie token
    (v/assert kb (list 'not (list feathered Opus)) CxRouting)
    ;; a body stored in both polarities: the opposed family
    (v/assert kb (list feathered Opus) CxRouting)
    ;; a ground binary self tuple: the self-tuple trie
    (v/assert kb (list parentOf Cid Cid) CxRouting)))

(defn- families-present
  "The families the built index actually holds, with one representative key each."
  [kb]
  (reduce (fn [m [k _]] (assoc m (family k) k)) {} (p/index-entries (:index kb))))

;;; ── every family is classified ────────────────────────────────────────

(deftest the-fixture-writes-every-declared-family-and-no-other
  ;; The required half of this namespace: a family that exists but is declared
  ;; nowhere would otherwise be checked by nothing at all, and would take the fallback
  ;; in both dense backends without a single test noticing.
  (let [kb    (open-kb! :memory 82)
        _     (build! kb)
        found (set (keys (families-present kb)))]
    (is (empty? (filter #(= :unclassified (first %)) found))
        (str "an index family nobody has classified: "
             (pr-str (filter #(= :unclassified (first %)) found))
             " — declare it a handle family or not, and route it accordingly"))
    (is (= (set/union handle-families other-families) found)
        (str "declared families and written families disagree — "
             (pr-str {:declared-but-unwritten (set/difference (set/union handle-families other-families) found)
                      :written-but-undeclared (set/difference found (set/union handle-families other-families))})))
    (tu/clear-kb! kb)))

;;; ── :memory-dense — the value is packed ───────────────────────────────

(deftest the-dense-backend-packs-every-handle-family
  ;; `kv-get` on `TieredKvBackend` hands back the stored value as it is held, so the
  ;; representation is readable without reaching into the backend's state.
  (let [kb      (open-kb! :memory-dense 82)
        _       (build! kb)
        backend (:backend (:index kb))
        present (families-present kb)]
    (doseq [[fam k] (sort-by (comp str key) present)]
      (testing (pr-str fam)
        (let [v (p/kv-get backend k)]
          (cond
            (handle-families fam)
            (is (instance? IntPostings v)
                (str fam " is a handle family but " (pr-str k) " is stored as "
                     (some-> v class .getSimpleName)
                     " — the router does not recognize the key, so it took the fallback"))

            (count-families fam)
            (is (number? v) (str fam " should be a plain counter"))

            :else
            (is (and (set? v) (not (instance? IntPostings v)))
                (str fam " is not a handle family and must stay an ordinary set"))))))
    (is (seq (filter handle-families (keys present))) "no handle family in the fixture")
    (tu/clear-kb! kb)))

;;; ── :memory-columnar — the key is interned too ────────────────────────

(deftest the-columnar-roots-intern-every-non-trie-handle-family
  ;; `DenseRoots` splits differently: a routed key lives in the packed long map and a
  ;; fallback key in an embedded plain backend.  `kv-get` reads *only* the fallback, so
  ;; "has members but `kv-get` is nil" is exactly "this key was int-routed" — no reach
  ;; into the deftype's fields required.
  (let [kb      (open-kb! :memory-columnar 82)
        _       (build! kb)
        roots   (:roots (:index kb))
        present (families-present kb)]
    (doseq [[fam k] (sort-by (comp str key) present)
            :when   (not= :trie (first fam))]      ; the columnar trie is native; no [:trie …] key reaches the roots
      (testing (pr-str fam)
        (cond
          (count-families fam)
          (is (pos? (long (p/kv-get roots k))) (str fam " answers the node's count"))

          (or (and (handle-families fam) (not (unpackable-handle-families fam)))
              (interned-name-families fam))
          (do (is (seq (p/kv-members roots k)) (str fam " is missing from the roots backend"))
              (is (nil? (p/kv-get roots k))
                  (str fam " is a packed family but " (pr-str k) " is readable through `kv-get`"
                       " — it sits in the fallback backend, un-interned and boxed")))

          :else
          (do (is (seq (p/kv-members roots k)) (str fam " is missing from the roots backend"))
              (is (some? (p/kv-get roots k))
                  (str fam " must stay in the fallback — it is either not a handle family"
                       " or one the packed layout cannot carry (see"
                       " `unpackable-handle-families`)"))))))
    ;; and the trie families really are elsewhere — the roots hold no path keys at all
    (doseq [[fam k] present :when (= :trie (first fam))]
      (is (empty? (p/kv-members roots k))
          (str fam " reached the roots backend; the columnar trie is supposed to own it")))
    (tu/clear-kb! kb)))

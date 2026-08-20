;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii-deref-property-test
  "Generative property tests for koinii cross-seat dereference
  (`vaelii.impl.koinii.deref`): the invariants the example-based
  `koinii_deref_test` pins on a handful of hand-built scenarios, restated as
  test.check properties over randomly generated assertions.

  Every fact is drawn from three SMALL fixed pools — camelCase predicates,
  CapitalCamelCase individuals, Cx-prefixed contexts — so vaelii's naming door
  never refuses a generated assertion, and so the same predicates/individuals
  recur across facts and structural collisions (same locator from two routes to
  one assertion, distinct locators from distinct assertions) are actually
  exercised rather than assumed away by unique gensyms.

  What each `defspec` pins:

  - `locator-is-content-addressed-and-handle-independent` — a locator is a
    function of the assertion, agreeing across two independent seats that reached
    it among different noise, and matching `sha256:<64 hex>`.
  - `locators-are-injective-over-the-sample` — distinct assertions get distinct
    locators; context, truth polarity and sentence each move the locator.
  - `encoder-is-deterministic-and-print-var-independent` — the canonical encoder
    ignores ambient `*print-*` vars (it is not `pr-str`).
  - `commit-id-is-an-order-independent-function-of-state` — a Merkle root over the
    *set*, so order does not move it and a superset does.
  - `commit-id-is-knowledge-and-state-root-is-snapshot` — content vs. provenance:
    same facts under different provenance share a `commit-id` but not a `state-root`.
  - `inclusion-proofs-are-sound-and-complete` — every stored locator's proof
    verifies against the real root and is rejected against a wrong root, a tampered
    sibling, or when the locator is absent.
  - `markers-are-untrusted` — an honest marker resolves to its asserting creator; a
    tampered locator is `:locator-mismatch`; an unreceived sentence is `:not-received`.

  Cleanup is load-bearing: memory seats share a process-global store keyed by
  `:space`, so every seat is opened on its OWN space (already cleared by
  `fresh-seat`) and cleared again in a `finally`.  A `:once` teardown wipes every
  space this namespace touched, so nothing leaks into a later namespace."
  (:require [clojure.test :refer [use-fixtures]]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [vaelii.core :as v]
            [vaelii.impl.koinii.deref :as d]
            [vaelii.test-util :as tu]))

;;; ── seats: independent in-RAM KBs, each on its own space ──────────────────

(defn- fresh-seat
  "An independent in-RAM seat — a cleared `:memory` KB on its own derived space, so
  it shares a store with no other seat.  `fresh-seat` clears on open; clear it again
  in a `finally`."
  [tag]
  (doto (v/open-kb (assoc tu/plain-memory-space :space [::seat (name tag)]))
    (tu/clear-kb!)))

(defn- with-seat
  "Open one cleared seat on `tag`'s space, run `(f seat)`, clear it in a `finally`.
  Returns `f`'s value (a property's truthy/falsey result)."
  [tag f]
  (let [seat (fresh-seat tag)]
    (try (f seat)
         (finally (tu/clear-kb! seat)))))

(defn- with-two-seats
  "Open two cleared seats on DISTINCT spaces, run `(f a b)`, clear both in a
  `finally`.  Two seats in one trial must never share a space, or the second's
  content leaks into the first."
  [tag-a tag-b f]
  (let [a (fresh-seat tag-a)
        b (fresh-seat tag-b)]
    (try (f a b)
         (finally (tu/clear-kb! a) (tu/clear-kb! b)))))

;; Every space this namespace opens.  The `:once` teardown wipes each one so a
;; generated assertion left by the last trial cannot leak into a later namespace
;; that happens to open the same derived space.
(def ^:private seat-tags
  [:loc-a :loc-b :inj :enc :cid-a :cid-b :split-a :split-b :split-c :split-d
   :proof :marker])

(use-fixtures :once
  (fn [f]
    (try (f)
         (finally (doseq [t seat-tags] (tu/clear-kb! (fresh-seat t)))))))

;;; ── the pools and the fact generators ────────────────────────────────────

;; camelCase predicates (lowercase initial), CapitalCamelCase individuals,
;; Cx-prefixed contexts — each satisfies vaelii's naming invariant for its role, so
;; a generated fact is always assertable.  Small pools on purpose: facts collide.
(def ^:private predicates '[usesDatabase connects likes serves])
(def ^:private individuals '[Alpha Beta Gamma Delta])
(def ^:private contexts '[CxOne CxTwo CxThree])

(def ^:private gen-fact
  "A ground unary `(pred ind)` or binary `(pred ind ind)` fact over the pools."
  (gen/let [pred (gen/elements predicates)
            args (gen/one-of [(gen/fmap vector (gen/elements individuals))
                              (gen/tuple (gen/elements individuals)
                                         (gen/elements individuals))])]
    (apply list pred args)))

(def ^:private gen-fact+ctx
  "A `[fact context]` pair — the unit an assertion is keyed on."
  (gen/tuple gen-fact (gen/elements contexts)))

(defn- gen-permutation
  "A generator of a uniformly random permutation of `coll` (version-independent —
  it does not lean on a particular test.check `shuffle` combinator)."
  [coll]
  (if (empty? coll)
    (gen/return [])
    (gen/let [i   (gen/choose 0 (dec (count coll)))
              rst (gen-permutation (into (subvec (vec coll) 0 i)
                                         (subvec (vec coll) (inc i))))]
      (into [(nth coll i)] rst))))

(def ^:private gen-distinct-pairs
  "A non-empty vector of DISTINCT `[fact context]` pairs (1–8 of them)."
  (gen/vector-distinct gen-fact+ctx {:min-elements 1 :max-elements 8}))

(def ^:private gen-pairs-and-perm
  "Distinct pairs paired with one reordering of them, for the order-independence
  property."
  (gen/let [pairs gen-distinct-pairs
            perm  (gen-permutation pairs)]
    [pairs perm]))

;;; ── small helpers ─────────────────────────────────────────────────────────

(defn- assert-all!
  "Assert every `[fact context]` in `pairs` into `seat` (default provenance)."
  [seat pairs]
  (doseq [[f c] pairs] (v/assert seat f c)))

(defn- wrong-root
  "A syntactically valid `sha256:` root that differs from `root` — an all-zeros
  root, or all-f if `root` happens to be the all-zeros one."
  [root]
  (let [z (str "sha256:" (apply str (repeat 64 \0)))
        o (str "sha256:" (apply str (repeat 64 \f)))]
    (if (= root z) o z)))

(defn- tamper-first-sibling
  "Flip one hex digit of the first sibling hash in a non-empty audit path, so the
  recomputed root no longer matches."
  [proof]
  (let [p (vec proof)
        h (get-in p [0 :hash])]
    (assoc-in p [0 :hash] (str (if (= \0 (first h)) \1 \0) (subs h 1)))))

;;; ── 1. content-addressing / cross-seat agreement ─────────────────────────

(def ^:private locator-re #"sha256:[0-9a-f]{64}")

(defspec locator-is-content-addressed-and-handle-independent 80
  (prop/for-all [target  gen-fact+ctx
                 noise-a (gen/vector gen-fact+ctx 0 6)
                 noise-b (gen/vector gen-fact+ctx 0 6)]
                (with-two-seats :loc-a :loc-b
                  (fn [a b]
                    ;; the target lands among different noise in each seat, so its handles differ
                    (assert-all! a (conj (vec noise-a) target))
                    (assert-all! b (into [target] noise-b))
                    (let [[f c] target
                          ha (v/handle-of a f c)
                          hb (v/handle-of b f c)
                          la (d/locator-of a ha)]
                      (and (= la (d/locator-of b hb))                       ; agrees across seats
                           (= (d/locate a f c) (d/locator-of a (v/handle-of a f c)))
                           (boolean (re-matches locator-re la))))))))

;;; ── 2. injectivity over the sample ───────────────────────────────────────

(defspec locators-are-injective-over-the-sample 80
  (prop/for-all [pairs gen-distinct-pairs]
                (with-seat :inj
                  (fn [seat]
                    (assert-all! seat pairs)
                    (let [locs (map (fn [[f c]] (d/locate seat f c)) pairs)
                          ;; a representative pair, and one-field mutations of it
                          [f c]   (first pairs)
                          other-c (first (filter #(not= % c) contexts))
                          other-f (apply list (first (filter #(not= % (first f)) predicates))
                                         (rest f))
                          base    (d/locate seat f c)]
                      (and
                       ;; distinct assertions ⇒ distinct locators, no collisions in the sample
                       (= (count pairs) (count (distinct locs)))
                       ;; context, truth polarity and sentence each change the locator
                       (not= base (d/locate seat f other-c))
                       (not= base (d/locate seat (list 'not f) c))
                       (not= base (d/locate seat other-f c))))))))

;;; ── 3. encoder determinism & print-var independence ──────────────────────

(defspec encoder-is-deterministic-and-print-var-independent 80
  (prop/for-all [target gen-fact+ctx
                 noise  (gen/vector gen-fact+ctx 0 6)]
                (with-seat :enc
                  (fn [seat]
                    (let [[f c] target]
                      (assert-all! seat (conj (vec noise) target))
                      (let [h     (v/handle-of seat f c)
                            l1    (d/locate seat f c)
                            l2    (d/locator-of seat h)
                            root1 (d/commit-id seat)
                            ;; hostile print vars: pr-str would truncate/alter, the encoder must not
                            [l3 root3] (binding [*print-length* 1 *print-level* 1 *print-meta* true]
                                         [(d/locate seat f c) (d/commit-id seat)])]
                        (and (= l1 l2 l3) (= root1 root3))))))))

;;; ── 4. commit-id: an order-independent function of state ──────────────────

(defspec commit-id-is-an-order-independent-function-of-state 60
  (prop/for-all [[pairs perm] gen-pairs-and-perm
                 extra        gen-fact+ctx]
                (with-two-seats :cid-a :cid-b
                  (fn [a b]
                    (assert-all! a pairs)
                    (assert-all! b perm)                       ; same set, reached in another order
                    (let [order-independent? (= (d/commit-id a) (d/commit-id b))
                          cid-b              (d/commit-id b)
                          [ef ec]            extra
                          new?               (nil? (v/handle-of b ef ec))]
                      (v/assert b ef ec)                        ; a strict superset (when genuinely new)
                      (and order-independent?
                           (if new?
                             (not= cid-b (d/commit-id b))
                             true)))))))

;;; ── 5. the knowledge / snapshot split (commit-id vs state-root) ───────────

(defspec commit-id-is-knowledge-and-state-root-is-snapshot 60
  (prop/for-all [pairs gen-distinct-pairs]
                (let [;; SAME facts+contexts, DIFFERENT provenance (creator and clock)
                      diff-prov
                      (with-two-seats :split-a :split-b
                        (fn [a b]
                          (binding [v/*clock* (constantly 1000)]
                            (doseq [[f c] pairs] (v/assert a f c {:creator 'AgentA})))
                          (binding [v/*clock* (constantly 2000)]
                            (doseq [[f c] pairs] (v/assert b f c {:creator 'AgentB})))
                          (and (= (d/commit-id a) (d/commit-id b))       ; same knowledge
                               (not= (d/state-root a) (d/state-root b))))) ; different snapshot
                      ;; IDENTICAL provenance ⇒ both roots equal
                      same-prov
                      (with-two-seats :split-c :split-d
                        (fn [a b]
                          (binding [v/*clock* (constantly 1000)]
                            (doseq [[f c] pairs] (v/assert a f c {:creator 'AgentA})))
                          (binding [v/*clock* (constantly 1000)]
                            (doseq [[f c] pairs] (v/assert b f c {:creator 'AgentA})))
                          (and (= (d/commit-id a) (d/commit-id b))
                               (= (d/state-root a) (d/state-root b)))))]
                  (and diff-prov same-prov))))

;;; ── 6. inclusion-proof soundness & completeness ──────────────────────────

(defspec inclusion-proofs-are-sound-and-complete 60
  (prop/for-all [pairs  gen-distinct-pairs
                 absent gen-fact+ctx]
                (with-seat :proof
                  (fn [seat]
                    (assert-all! seat pairs)
                    (let [root     (d/commit-id seat)
                          handles  (map (fn [[f c]] (v/handle-of seat f c)) pairs)
                          locators (distinct (map #(d/locator-of seat %) handles))
                          [af ac]  absent
                          absent-loc (d/locate seat af ac)]
                      (and
                       ;; every stored locator: a proof that verifies, and is rejected against a
                       ;; wrong root and against a tampered sibling
                       (every? (fn [loc]
                                 (let [proof (d/inclusion-proof seat loc)]
                                   (and proof
                                        (d/verify-inclusion loc proof root)
                                        (not (d/verify-inclusion loc proof (wrong-root root)))
                                        (or (empty? proof)
                                            (not (d/verify-inclusion loc (tamper-first-sibling proof)
                                                                     root))))))
                               locators)
                       ;; a locator absent from the KB ⇒ no proof, and verify false.  (Guard: the
                       ;; "absent" pair may, from small pools, actually be one we stored.)
                       (if (nil? (v/handle-of seat af ac))
                         (and (nil? (d/inclusion-proof seat absent-loc))
                              (not (d/verify-inclusion absent-loc [] root)))
                         true)))))))

;;; ── 7. tamper / non-receipt in dereference ───────────────────────────────

(def ^:private marker-creator 'AgentZeta)

(defspec markers-are-untrusted 80
  (prop/for-all [pairs  gen-distinct-pairs
                 idx    gen/nat
                 absent gen-fact+ctx]
                (with-seat :marker
                  (fn [seat]
                    (doseq [[f c] pairs] (v/assert seat f c {:creator marker-creator}))
                    (let [[f c]    (nth pairs (mod idx (count pairs)))
                          h        (v/handle-of seat f c)
                          mk       (d/marker seat h)
                          honest   (d/dereference seat mk)
                          ;; reverse the whole locator string (prefix included): stored, but the
                          ;; marker's locator no longer matches what the KB recomputes
                          tampered (d/dereference seat (assoc mk :locator (apply str (reverse (:locator mk)))))
                          [af ac]  absent]
                      (and (:resolved? honest)
                           (= marker-creator (:seat honest))
                           (false? (:resolved? tampered))
                           (= :locator-mismatch (:reason tampered))
                           ;; a sentence the seat never received ⇒ :not-received (guard: the
                           ;; "absent" pair may actually be stored)
                           (if (nil? (v/handle-of seat af ac))
                             (= :not-received
                                (:reason (d/dereference seat (assoc mk :sentence af :context ac))))
                             true)))))))

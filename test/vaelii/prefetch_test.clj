;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.prefetch-test
  "`resolution/*prefetch-candidates*` — the hint a retrieval path gives its record store
  before walking a chunk of candidates.

  The engine's own stores do not implement `protocols/Prefetching`: a record fetch on the
  RAM and disk backends is a page touch, and there is nothing a batch could save.  So the
  mechanism is tested here against a **wrapper that records what it was hinted**, which is
  what lets core state the two properties that matter without a database in the room:

  - **it cannot change an answer.**  The hint returns nothing and every record still
    arrives through `get-sentex`, so the answer set is identical on and off — asserted on
    both retrieval paths, since a positive literal takes the set-algebra one by default
    and the `match-one` fan-out is the reference behind it;
  - **it is bounded by the chunk.**  A consumer that stops at the first solution has
    hinted one chunk and not the extent, which is the whole of what makes the setting
    cheap to leave on.

  A store with no capability is the third property and the default one: the setting is
  inert, because `prefetcher` answers nil and the walk is the walk it always was."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.capabilities :as cap]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]))

(defn- hinting-store
  "`inner` with `Prefetching` bolted on, recording each hint into `hints` (and each
  justification hint into `j-hints`).  A wrapper
  rather than a redef: a protocol method is dispatched on the value's type, so only a real
  implementation is in the path a compiled caller takes."
  ([inner hints] (hinting-store inner hints (atom [])))
  ([inner hints j-hints]
   (reify
     p/RecordStore
     (put-sentex [_ sx] (p/put-sentex inner sx))
     (get-sentex [_ id] (p/get-sentex inner id))
     (delete-sentex! [_ id] (p/delete-sentex! inner id))
     (put-justification [_ d] (p/put-justification inner d))
     (get-justification [_ id] (p/get-justification inner id))
     (delete-justification! [_ id] (p/delete-justification! inner id))
     (next-id [_] (p/next-id inner))
     (put-provenance [_ id prov] (p/put-provenance inner id prov))
     (get-provenance [_ id] (p/get-provenance inner id))
     (delete-provenance! [_ id] (p/delete-provenance! inner id))
     (sentex-ids [_] (p/sentex-ids inner))
     (justification-ids [_] (p/justification-ids inner))
     (mark-premise [_ id s] (p/mark-premise inner id s))
     (unmark-premise! [_ id] (p/unmark-premise! inner id))
     (premise-ids [_] (p/premise-ids inner))
     (premise-strength [_ id] (p/premise-strength inner id))
     (clear-records! [_] (p/clear-records! inner))
     p/Prefetching
     (prefetch-sentexes! [_ ids] (swap! hints conj (vec ids)) nil)
     (prefetch-justifications! [_ ids] (swap! j-hints conj (vec ids)) nil))))

(defn- populated
  "A KB with `n` facts under each of two predicates, and its hint log."
  [n]
  (let [kb    (v/open-kb {:backend :memory :space (gensym "prefetch")})
        _     (doseq [i (range n)]
                (v/assert kb (list 'rel (symbol (str "Ind" i))) 'CxPrefetch)
                (v/assert kb (list 'other (symbol (str "Ind" i))) 'CxPrefetch))
        hints (atom [])]
    [(assoc kb :records (hinting-store (:records kb) hints)) hints]))

(defn- answer-set [kb sentence]
  (set (map (fn [[h b]] [h b]) (res/matches-visible kb sentence 'CxPrefetch))))

;; ---- it cannot change an answer -----------------------------------------

(deftest the-hint-does-not-move-the-answer-set
  (let [[kb _] (populated 200)]
    (doseq [sentence ['(rel ?x) '(rel Ind7) '(?p Ind7) '(other ?x)]]
      (testing (str sentence)
        (let [off (binding [res/*prefetch-candidates* false] (answer-set kb sentence))
              on  (binding [res/*prefetch-candidates* 16]    (answer-set kb sentence))]
          (is (seq off) "the fixture answers this at all")
          (is (= off on) "identical with the hint on"))))))

(deftest the-hint-does-not-move-the-answer-on-either-retrieval-path
  ;; a positive literal takes the set-algebra path by default and the `match-one` fan-out
  ;; is the reference behind it; the hint wraps the candidates of both, so both are held
  ;; to the same set here rather than only the one a default query happens to take.
  (let [[kb _] (populated 200)]
    (doseq [sentence ['(rel ?x) '(rel Ind3)]]
      (testing (str sentence)
        (let [algebra (binding [res/*hierarchical-retrieval* true
                                res/*prefetch-candidates*    16]
                        (answer-set kb sentence))
              fan-out (binding [res/*hierarchical-retrieval* false
                                res/*prefetch-candidates*    16]
                        (answer-set kb sentence))
              plain   (binding [res/*hierarchical-retrieval* false
                                res/*prefetch-candidates*    false]
                        (answer-set kb sentence))]
          (is (= plain fan-out) "the fan-out answers the same hinted and not")
          (is (= plain algebra) "and the set-algebra path agrees with it"))))))

;; ---- it is bounded by the chunk -----------------------------------------

(defn- hinted-for-one-solution
  "How many handles the store was hinted when the consumer took **one** solution out of an
  extent of `n`."
  [n]
  (let [[kb hints] (populated n)]
    (reset! hints [])
    (binding [res/*prefetch-candidates* 16]
      (first (res/matches-visible kb '(rel ?x) 'CxPrefetch)))
    {:hints (count @hints)
     :handles (count (mapcat identity @hints))
     :widest (reduce max 0 (map count @hints))}))

(deftest a-consumer-that-stops-early-hints-a-bounded-prefix
  ;; The property that makes the setting cheap to leave on: what a stopping consumer costs
  ;; is a function of the CHUNK and not of the extent.  So it is asserted as exactly that
  ;; — the same three extents, the same hint count — rather than as a number that happens
  ;; to hold at one size.  (The constant is the lazy seq's own read-ahead, not one chunk:
  ;; `mapcat` over the chunks realizes a few before the first answer escapes.)
  (let [small (hinted-for-one-solution 100)
        mid   (hinted-for-one-solution 500)
        big   (hinted-for-one-solution 2000)]
    (is (pos? (:hints small)) "the store was hinted at all")
    (is (= (:hints small) (:hints mid) (:hints big))
        "the same number of chunks whether the extent is 100, 500 or 2000")
    (is (= (:handles small) (:handles mid) (:handles big))
        "…so the same number of handles, and the extent does not enter into it")
    (is (< (:handles big) 2000)
        "which is emphatically not the extent")
    (is (<= (:widest big) 16) "and no hint is larger than the chunk")))

(deftest a-full-walk-hints-the-whole-extent-in-chunks
  (let [[kb hints] (populated 200)]
    (reset! hints [])
    (binding [res/*prefetch-candidates* 16]
      (is (= 200 (count (res/matches-visible kb '(rel ?x) 'CxPrefetch)))))
    (is (= 200 (count (distinct (mapcat identity @hints))))
        "every candidate was hinted exactly once, across the chunks")
    (is (every? #(<= (count %) 16) @hints)
        "and each hint is one chunk")))

(deftest the-hint-carries-only-believed-handles
  ;; the store is never asked to warm a record the walk would skip, so a retracted
  ;; sentex's handle does not appear in a hint.
  (let [[kb hints] (populated 50)
        h (:id (first (v/sentexes-matching kb '(rel Ind7) 'CxPrefetch)))]
    (v/retract! kb h)
    (reset! hints [])
    (binding [res/*prefetch-candidates* 64]
      (doall (res/matches-visible kb '(rel ?x) 'CxPrefetch)))
    (is (seq @hints) "the walk happened")
    (is (not (contains? (set (mapcat identity @hints)) h))
        "the retracted handle was filtered out before the hint")))

;; ---- a store with no capability ----------------------------------------

(deftest the-setting-is-inert-without-the-capability
  ;; the default state of every backend the engine ships: `prefetcher` answers nil and
  ;; the walk is the one that was always there.
  (let [kb (v/open-kb {:backend :memory :space (gensym "prefetch")})]
    (doseq [i (range 100)] (v/assert kb (list 'rel (symbol (str "Ind" i))) 'CxPrefetch))
    (is (nil? (cap/prefetcher (:records kb)))
        "the RAM record store implements no Prefetching, so there is nobody to hint")
    (let [off (binding [res/*prefetch-candidates* false] (answer-set kb '(rel ?x)))
          on  (binding [res/*prefetch-candidates* 16]    (answer-set kb '(rel ?x)))]
      (is (= 100 (count off)))
      (is (= off on) "and turning the setting on changes nothing"))))

(deftest off-is-the-default
  (is (false? res/*prefetch-candidates*)
      "a hint is issued only when something asks for it"))

(deftest a-value-that-is-not-a-chunk-is-refused-where-it-is-bound
  ;; `true` is the guess an off-value of `false` invites, and it is truthy — so without a
  ;; refusal it passes every gate on the query path and fails in `cap/hinting`'s `(long n)`,
  ;; several frames into a lazy seq, naming neither the var nor what was bound to it.
  (doseq [v [true nil 0 -1 :always "256" 2.5]]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"\*prefetch-candidates\*"
                          (binding [res/*prefetch-candidates* v]
                            res/*prefetch-candidates*))
        (str (pr-str v) " is not a chunk size")))
  (testing "and it refuses in the one vocabulary, so a caller discriminates on the type
            rather than on the message"
    ;; `:unknown-option` is what `vaelii.impl.config` throws for a switch bound outside
    ;; its domain, and a setting is a setting whether it came from a var or the shell.
    (doseq [v [true nil 0 -1 :always "256" 2.5]]
      (let [e (try (binding [res/*prefetch-candidates* v] res/*prefetch-candidates*)
                   (catch clojure.lang.ExceptionInfo e e))]
        (is (= :unknown-option (:type (ex-data e))) (pr-str v))
        (is (= v (:value (ex-data e))) "and names the value it was given"))))
  (testing "the binding form is what throws, not the walk"
    (let [ran (atom false)]
      (is (thrown? clojure.lang.ExceptionInfo
                   (binding [res/*prefetch-candidates* true] (reset! ran true))))
      (is (false? @ran) "so the body never ran, and no query was in flight when it failed")
      (is (false? res/*prefetch-candidates*) "and the setting is what it was")))
  (testing "and the two shapes that are a chunk"
    (is (false? (binding [res/*prefetch-candidates* false] res/*prefetch-candidates*)))
    (is (= 256 (binding [res/*prefetch-candidates* 256] res/*prefetch-candidates*)))))

;; ---- the recovery walks hint unconditionally ---------------------------

(deftest the-recovery-walks-hint-without-a-setting
  ;; `reindex` fetches every live record and `recover` every stored justification, and
  ;; both consume every handle they are given — so a hint there can save round trips and
  ;; cannot waste one, and neither is gated on `*prefetch-candidates*`.  That is the whole
  ;; difference from the query path, and it is asserted with the setting explicitly OFF.
  (let [kb    (v/open-kb {:backend :memory :space (gensym "prefetch")})
        _     (do (v/assert-rule kb '[(rel ?x)] '(derived ?x) 'CxPrefetch)
                  (doseq [i (range 50)]
                    (v/assert kb (list 'rel (symbol (str "Ind" i))) 'CxPrefetch)))
        hints   (atom [])
        j-hints (atom [])
        kb2   (assoc kb :records (hinting-store (:records kb) hints j-hints))]
    (binding [res/*prefetch-candidates* false]
      (v/reindex kb2))
    (testing "the record walk was hinted"
      (is (seq @hints))
      (is (= (count (p/sentex-ids (:records kb2)))
             (count (distinct (mapcat identity @hints))))
          "every live record handle, exactly once"))
    (testing "the justification walk was hinted"
      (is (seq @j-hints))
      (is (= (count (p/justification-ids (:records kb2)))
             (count (distinct (mapcat identity @j-hints))))
          "every stored justification handle, exactly once"))))

(deftest a-store-without-the-capability-recovers-unhinted
  ;; the same walks over the engine's own stores: `prefetcher` is nil, so the seq the walk
  ;; consumes is the enumeration itself and nothing is chunked.
  (let [kb (v/open-kb {:backend :memory :space (gensym "prefetch")})]
    (v/assert-rule kb '[(rel ?x)] '(derived ?x) 'CxPrefetch)
    (doseq [i (range 20)] (v/assert kb (list 'rel (symbol (str "Ind" i))) 'CxPrefetch))
    (is (nil? (cap/prefetcher (:records kb))))
    (is (nil? (cap/justification-prefetcher (:records kb))))
    (is (map? (v/reindex kb)) "and the rebuild runs exactly as it did")))

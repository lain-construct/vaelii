;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.overlay-test
  "The `:overlay` backend — a private writable fork over a shared read-only base.

  Two claims carry the whole thing, and everything below is one of them:

  * **The base is never written.**  A fork asserts, derives, retracts and clears, and the
    base's records, premises and index come back byte-identical.  That is what lets any
    number of forks in one JVM share one frozen base with no protocol between them.
  * **The merged view is the KB.**  A fork over an *empty* base behaves exactly like a
    plain backend (the `KvBackend` contract, and the suite-parity gate — see
    `scripts/test-backends.sh`), and over a populated one the engine reasons across the
    seam without knowing it is there: an inherited fact matches, an inherited rule fires
    over a fork-local fact, and retracting an inherited premise in the fork sweeps what
    it derived — in the fork only."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.disk.backend :as disk]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.overlay.frozen :as frozen]
            [vaelii.impl.overlay.kv :as okv]
            [vaelii.impl.overlay.mount :as mount]
            [vaelii.impl.protocols :as p]
            [vaelii.kv-backend-test :as kvt]
            [vaelii.test-util :as tu])
  (:import [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

;; Own space numbers, outside the suite's block, so a fork never shares a store with
;; another test — and a *pair* per role, since a fork is two KBs' worth of stores.
(defn- base-opts  [n] {:backend :memory :record-space [::base n]  :index-space [::base n :ix]})
(defn- fork-opts  [n] {:backend :memory :record-space [::fork n]  :index-space [::fork n :ix]})

(defn- tmpdir ^String []
  (str (Files/createTempDirectory "vaelii-overlay-" (into-array FileAttribute []))))

(defn- rm-rf! [^String dir]
  (doseq [f (reverse (file-seq (java.io.File. dir)))] (.delete ^java.io.File f)))

;; ---- what a base looks like, so a change to it is visible -----------------

(defn- base-snapshot
  "Everything a base holds, in a form that compares by value: its records, its premise
  marks and its whole index.  Handles are included deliberately — the point is that the
  base is *unchanged*, not merely equivalent."
  [kb]
  {:sentexes       (into {} (map (juxt identity #(p/get-sentex (:records kb) %)))
                         (p/sentex-ids (:records kb)))
   :justifications (into {} (map (juxt identity #(p/get-justification (:records kb) %)))
                         (p/justification-ids (:records kb)))
   :premises       (set (p/premise-ids (:records kb)))
   :index          (set (kv/kv-entries (:backend (:index kb))))})

(defn- populate!
  "A small base: a taxonomy edge, a forward rule, and two facts — so a fork inherits
  something to match, something to subsume through, and something to fire."
  [kb]
  (v/assert kb '(genl dog animal) 'OverlayContext {:strength :monotonic})
  (v/assert-rule kb '[(dog ?x)] '(mammal ?x) 'OverlayContext)
  (v/assert kb '(dog Fido) 'OverlayContext {:strength :monotonic})
  (v/assert kb '(ownerOf Ann Fido) 'OverlayContext {:strength :monotonic})
  kb)

(defn- fresh-base
  "A populated base KB on its own spaces, cleared first."
  [n]
  (populate! (doto (v/open-kb (assoc (base-opts n) :recover? false)) (v/clear!))))

(defn- sentences [solutions] (set (map :sentence solutions)))

;; ---- the adapter contract -------------------------------------------------

(deftest the-overlay-kv-satisfies-the-backend-contract
  ;; A fork of nothing is the thing it forked: with an empty base, every merge rule
  ;; degenerates and the decorator has to answer the one spec every adapter answers.
  (let [base (doto (mem/memory-kv-backend {:space [::kv-base]}) (kv/kv-clear!))
        ov   (doto (mem/memory-kv-backend {:space [::kv-fork]}) (kv/kv-clear!))]
    (kvt/check-backend (okv/overlay-kv ov (frozen/frozen-kv base)))
    (is (empty? (kv/kv-entries base)) "and the base stayed empty throughout")))

(deftest a-frozen-base-refuses-every-write
  (testing "the index half"
    (let [b (frozen/frozen-kv (mem/memory-kv-backend {:space [::frozen]}))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"mounted read-only"
                            (kv/kv-add-to-set b [:x] 1)))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"mounted read-only" (kv/kv-clear! b)))
      (is (nil? (kv/kv-get b [:x])) "and reads still work")))
  (testing "the record half"
    (let [r (frozen/frozen-records (mem/memory-record-store {:space [::frozen]}))]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"mounted read-only"
                            (p/put-sentex r {:sentence '(dog Fido)})))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"mounted read-only"
                            (p/clear-records! r)))
      (is (set? (p/sentex-ids r)) "and reads still work"))))

(deftest an-index-with-no-kv-seam-is-refused-rather-than-half-forked
  ;; The columnar index is a native `IndexStore` — its trie is int-id nodes in parallel
  ;; arrays, with no backend underneath — so a KvBackend decorator would fork its roots
  ;; and silently leave the trie behind.  Say so instead.
  (let [base (doto (v/open-kb {:backend :memory-columnar
                               :record-space [::col] :index-space [::col :ix] :recover? false})
               (v/clear!))]
    (is (nil? (mount/kv-backend-of (:index base))))
    ;; Matched on what the caller can act on — the backend named and the ones that
    ;; would work — rather than on the mechanism, which the message now states after
    ;; the actionable clause instead of before it.
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cannot fork a :columnar index"
                          (v/fork base)))
    (is (= :unforkable-index
           (:type (try (v/fork base) nil (catch clojure.lang.ExceptionInfo e (ex-data e))))))
    (v/clear! base)))

(deftest a-fork-of-a-fork-is-refused
  ;; `docs/overlay.md` states one overlay over one base.  `core/fork` passes
  ;; `:base-stores` and names no backend, so the opts check has nothing to match on and
  ;; the stores are asked directly (`mount/forked?`) — which is the only place a second
  ;; layer is visible.
  (let [base (doto (v/open-kb {:backend :memory
                               :record-space [::stk] :index-space [::stk :ix] :recover? false})
               (v/clear!))
        one  (v/fork base)]
    (is (true? (mount/forked? one)) "the first fork is a fork — `forked?` reads the pair")
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"fork" (v/fork one)))
    (is (= :stacked-fork
           (:type (try (v/fork one) nil (catch clojure.lang.ExceptionInfo e (ex-data e)))))
        "and it says which refusal it is, rather than failing somewhere downstream")
    (v/clear! base)))

;; ---- fall-through, override, isolation ------------------------------------

(deftest a-fork-reads-through-to-its-base
  (let [base (fresh-base 1)
        f    (v/fork base)]
    (testing "stored content, belief and the taxonomy all arrive"
      (is (= '#{(dog Fido)} (sentences (v/sentexes-matching f '(dog ?x) 'OverlayContext))))
      (is (= '#{(ownerOf Ann Fido)} (sentences (v/sentexes-matching f '(ownerOf ?who Fido) 'OverlayContext))))
      (is (= '#{(mammal Fido)} (sentences (v/sentexes-matching f '(mammal ?x) 'OverlayContext)))
          "including what the base's rule derived")
      (is (v/isa? f 'Fido 'animal) "and the genl closure the base's edge licenses"))
    (testing "the term index and the roots read through too"
      (is (seq (v/find-sentexes f 'Fido)))
      (is (= (v/count-with-functor base 'dog) (v/count-with-functor f 'dog)))
      (is (= (v/sentex-count base) (v/sentex-count f))))
    (v/clear! base)))

(deftest a-fork-writes-only-to-itself
  (let [base   (fresh-base 2)
        before (base-snapshot base)
        f      (v/fork base)]
    (v/assert f '(dog Rex) 'OverlayContext {:strength :monotonic})
    (testing "the fork sees its own write joined to what it inherited"
      (is (= '#{(dog Fido) (dog Rex)} (sentences (v/sentexes-matching f '(dog ?x) 'OverlayContext))))
      (is (= '#{(mammal Fido) (mammal Rex)} (sentences (v/sentexes-matching f '(mammal ?x) 'OverlayContext)))
          "the base's rule fired over the fork's fact"))
    (testing "and the base saw none of it"
      (is (= '#{(dog Fido)} (sentences (v/sentexes-matching base '(dog ?x) 'OverlayContext))))
      (is (= before (base-snapshot base)) "the base is byte-identical"))
    (v/clear! base)))

(deftest retracting-an-inherited-premise-in-a-fork-leaves-the-base-alone
  (let [base   (fresh-base 3)
        before (base-snapshot base)
        f      (v/fork base)
        h      (v/handle-of f '(dog Fido) 'OverlayContext)]
    (is (some? h) "the inherited premise is reachable by handle")
    (v/retract! f h)
    (testing "gone in the fork, with what it derived"
      (is (empty? (v/sentexes-matching f '(dog ?x) 'OverlayContext)))
      (is (empty? (v/sentexes-matching f '(mammal ?x) 'OverlayContext)) "the sweep reached the conclusion")
      (is (nil? (v/handle-of f '(dog Fido) 'OverlayContext)) "the tombstone hides it from lookup"))
    (testing "present in the base"
      (is (= '#{(dog Fido)} (sentences (v/sentexes-matching base '(dog ?x) 'OverlayContext))))
      (is (= '#{(mammal Fido)} (sentences (v/sentexes-matching base '(mammal ?x) 'OverlayContext))))
      (is (= before (base-snapshot base))))
    (v/clear! base)))

(deftest a-fork-mints-handles-above-the-base-and-can-override-below-it
  (let [base   (fresh-base 4)
        before (base-snapshot base)
        top    (apply max (p/sentex-ids (:records base)))
        f      (v/fork base)
        recs   (:records f)]
    (testing "a new record gets a handle no base record holds"
      (let [h (v/assert f '(dog Rex) 'OverlayContext {:strength :monotonic})]
        (is (> (long h) (long top)) (str "minted " h " over a base topping out at " top))))
    (testing "a record written at a base handle overrides it, in the fork only"
      (let [h  (v/handle-of f '(ownerOf Ann Fido) 'OverlayContext)
            sx (p/get-sentex recs h)]
        (is (<= (long h) (long top)) "the handle is in the base's range")
        (p/put-sentex recs (assoc sx :sentence '(ownerOf Bob Fido)))
        (is (= '(ownerOf Bob Fido) (:sentence (p/get-sentex recs h))) "the override wins in the fork")
        (is (= '(ownerOf Ann Fido) (:sentence (p/get-sentex (:records base) h)))
            "and the base record is untouched")))
    (is (= before (base-snapshot base)))
    (v/clear! base)))

(deftest a-fork-can-be-cleared-back-to-empty-without-emptying-the-base
  (let [base   (fresh-base 5)
        before (base-snapshot base)
        f      (v/fork base)]
    (v/assert f '(dog Rex) 'OverlayContext {:strength :monotonic})
    (v/clear! f)
    (testing "the fork reads empty"
      (is (zero? (v/sentex-count f)))
      (is (empty? (p/sentex-ids (:records f))))
      (is (empty? (v/sentexes-matching f '(dog ?x) 'OverlayContext))))
    (testing "and is usable again, at handles nothing claims"
      (v/assert f '(cat Tom) 'OverlayContext {:strength :monotonic})
      (is (= '#{(cat Tom)} (sentences (v/sentexes-matching f '(cat ?x) 'OverlayContext)))))
    (is (= before (base-snapshot base)) "the base survived the fork's clear")
    (v/clear! base)))

(deftest reindexing-a-fork-rebuilds-the-merged-index-from-the-merged-records
  ;; `reindex` throws the whole index away and rebuilds it from the records, and on a
  ;; fork both of those are the merged view — which is what the O(1) `kv-clear!` marker
  ;; is for: without it the base's entries would survive the wipe and be counted twice.
  (let [base   (fresh-base 11)
        before (base-snapshot base)
        f      (v/fork base)]
    (v/assert f '(dog Rex) 'OverlayContext {:strength :monotonic})
    (let [{:keys [sentexes]} (v/reindex f)]
      (is (= sentexes (v/sentex-count f)) "every merged record was re-indexed, once")
      (is (= '#{(dog Fido) (dog Rex)} (sentences (v/sentexes-matching f '(dog ?x) 'OverlayContext))))
      (is (= 2 (v/count-with-functor f 'dog)) "and no posting was double-counted")
      (is (v/isa? f 'Fido 'animal) "the taxonomy came back with it"))
    (is (= before (base-snapshot base)) "and the base was not rebuilt into")
    (v/clear! base)))

;; ---- counts ---------------------------------------------------------------

(deftest merged-counts-are-exact-across-adds-deletes-and-overrides
  (let [base (fresh-base 6)
        f    (v/fork base)
        n0   (v/sentex-count base)]
    (is (= n0 (v/sentex-count f)) "a fresh fork counts what its base counts")
    (v/assert f '(dog Rex) 'OverlayContext {:strength :monotonic})
    (testing "an add moves the fork's counts and not the base's"
      ;; (dog Rex) plus the (mammal Rex) the inherited rule derived from it
      (is (= (+ 2 (long n0)) (long (v/sentex-count f))))
      (is (= n0 (v/sentex-count base)))
      (is (= 2 (v/count-with-functor f 'dog)))
      (is (= 1 (v/count-with-functor base 'dog)))
      (is (= 2 (v/count-with-arg f 1 'Rex)) "the argument root counts the merged view"))
    (testing "a delete of an inherited record moves them back"
      (v/retract! f (v/handle-of f '(dog Fido) 'OverlayContext))
      (is (= 1 (v/count-with-functor f 'dog)))
      (is (= 1 (v/count-with-functor base 'dog)))
      (is (= n0 (v/context-size f 'OverlayContext))
          "the context root too — two records added, two swept, back where it started")
      (is (= (count (p/sentexes-in-context (:index f) 'OverlayContext))
             (v/context-size f 'OverlayContext))
          "a count never disagrees with the extent it counts"))
    (v/clear! base)))

;; ---- the portable projection ----------------------------------------------

(deftest the-index-projection-of-a-fork-is-the-merged-view
  ;; `index-entries` is what an export of a fork writes, and it is the one read at which
  ;; a posting has to be merged without knowing any backend's private representation —
  ;; the contract says entries arrive as Clojure sets, which is what makes it possible.
  (let [base (fresh-base 10)
        f    (v/fork base)]
    (v/assert f '(dog Rex) 'OverlayContext {:strength :monotonic})
    (v/retract! f (v/handle-of f '(ownerOf Ann Fido) 'OverlayContext))
    (let [entries (into {} (p/index-entries (:index f)))
          fork-h  (v/handle-of f '(dog Rex) 'OverlayContext)
          base-h  (v/handle-of base '(dog Fido) 'OverlayContext)]
      (testing "a root inherited from the base and extended by the fork comes out merged"
        (is (= #{fork-h base-h} (get entries '[:functor-root dog]))))
      (testing "and one the fork emptied of its inherited member is simply gone"
        (is (nil? (get entries '[:functor-root ownerOf]))))
      (testing "the bookkeeping keys are the overlay's own and never project"
        (is (empty? (filter (fn [k] (or (keyword? k) (and (vector? k) (keyword? (first k))
                                                          (namespace (first k)))))
                            (keys entries)))))
      (testing "the term roster merges too — inherited names, plus and minus the fork's"
        (let [terms (set (v/terms f))]
          (is (contains? terms 'Fido) "a name the fork inherited and left alone")
          (is (contains? terms 'Rex)  "one the fork introduced")
          (is (not (contains? terms 'Ann))
              "and one the fork's retraction retired — the roster is derived from the
               merged postings, so it is not merely the base's plus more"))))
    (v/clear! base)))

;; ---- several forks over one base ------------------------------------------

(deftest several-forks-over-one-base-evolve-independently
  (let [base   (fresh-base 7)
        before (base-snapshot base)
        forks  (mapv (fn [_] (v/fork base)) (range 3))]
    (doseq [[i f] (map-indexed vector forks)]
      (v/assert f (list 'dog (symbol (str "Fork" i))) 'OverlayContext {:strength :monotonic}))
    ;; the middle fork also drops what it inherited, so the three differ in both directions
    (v/retract! (nth forks 1) (v/handle-of (nth forks 1) '(dog Fido) 'OverlayContext))
    (testing "each fork sees its own edit over the base and nobody else's"
      (is (= '#{(dog Fido) (dog Fork0)} (sentences (v/sentexes-matching (nth forks 0) '(dog ?x) 'OverlayContext))))
      (is (= '#{(dog Fork1)}            (sentences (v/sentexes-matching (nth forks 1) '(dog ?x) 'OverlayContext))))
      (is (= '#{(dog Fido) (dog Fork2)} (sentences (v/sentexes-matching (nth forks 2) '(dog ?x) 'OverlayContext)))))
    (testing "and the base is what it was"
      (is (= '#{(dog Fido)} (sentences (v/sentexes-matching base '(dog ?x) 'OverlayContext))))
      (is (= before (base-snapshot base))))
    (v/clear! base)))

;; ---- durability -----------------------------------------------------------

(deftest a-durable-fork-remounts-onto-the-same-merged-view
  ;; The record-level bookkeeping — the tombstones and released premise marks — is not
  ;; derivable from the overlay's own records (nothing there records the *absence* of an
  ;; inherited one), so it has to be as durable as the fork is.  Close the fork's stores
  ;; and mount them again: a deleted inherited record must stay deleted.
  (let [base (fresh-base 8)
        dir  (tmpdir)]
    (try
      (let [f (v/fork base {:backend :disk :dir dir})]
        (v/assert f '(dog Rex) 'OverlayContext {:strength :monotonic})
        (v/retract! f (v/handle-of f '(dog Fido) 'OverlayContext))
        (is (= '#{(dog Rex)} (sentences (v/sentexes-matching f '(dog ?x) 'OverlayContext)))))
      (disk/close-dir! dir)
      (testing "remounted over the same base, the fork is where it was left"
        (let [f2 (v/fork base {:backend :disk :dir dir})]
          (is (= '#{(dog Rex)} (sentences (v/sentexes-matching f2 '(dog ?x) 'OverlayContext)))
              "the inherited premise stayed retracted and the fork's own fact came back")
          (is (empty? (v/sentexes-matching f2 '(mammal Fido) 'OverlayContext))
              "and so did what the retraction swept")
          (is (= '#{(mammal Rex)} (sentences (v/sentexes-matching f2 '(mammal ?x) 'OverlayContext)))
              "the base's rule still fires over the fork's own fact")))
      (testing "while the base never learned any of it"
        (is (= '#{(dog Fido)} (sentences (v/sentexes-matching base '(dog ?x) 'OverlayContext)))))
      (finally
        (disk/close-dir! dir)
        (rm-rf! dir)
        (v/clear! base)))))

(deftest close-releases-a-durable-forks-own-directory-and-never-the-bases
  ;; `v/close!` on the fork, not `disk/close-dir!` on the path — the fork's writable half
  ;; takes the same exclusive lock and holds the same handles as any durable KB, so
  ;; without a `:dir` of its own the directory could not be handed on short of exiting
  ;; the JVM.  A second open of the same directory is the proof the lock came back.
  (let [base (fresh-base 9)
        dir  (tmpdir)]
    (try
      (let [f (v/fork base {:backend :disk :dir dir})]
        (v/assert f '(dog Rex) 'OverlayContext {:strength :monotonic})
        ;; canonical both sides — the store canonicalizes, so `/var` arrives as `/private/var`
        (is (= (.getCanonicalPath (File. (str dir)))
               (.getCanonicalPath (File. (str (:dir f)))))
            "a durable fork carries its own directory")
        (v/close! f))
      (testing "the directory is free, so it mounts again"
        (let [f2 (v/fork base {:backend :disk :dir dir})]
          (is (= '#{(dog Fido) (dog Rex)}
                 (sentences (v/sentexes-matching f2 '(dog ?x) 'OverlayContext)))
              "with both halves of the merged view intact")
          (v/close! f2)))
      (testing "and the base is untouched — it is mounted read-only and shared"
        (is (= '#{(dog Fido)} (sentences (v/sentexes-matching base '(dog ?x) 'OverlayContext)))))
      (finally
        (disk/close-dir! dir)
        (rm-rf! dir)
        (v/clear! base)))))

;; ---- the empty-base degeneracy, at KB level -------------------------------

(deftest a-fork-of-an-empty-base-is-an-ordinary-kb
  ;; The suite-parity gate in miniature: with nothing to merge, every code path above
  ;; must reduce to the plain backend's.  (`VAELII_TEST_BACKEND=overlay` runs the whole
  ;; suite this way — see scripts/test-backends.sh.)
  (let [base (doto (v/open-kb (assoc (base-opts 9) :recover? false)) (v/clear!))
        f    (v/fork base (fork-opts 9))]
    (tu/with-terms [dog Fido ThisContext]
      (v/assert f (list 'genl dog 'thing) ThisContext {:strength :monotonic})
      (v/assert-rule f [(list dog '?x)] (list 'mammal '?x) ThisContext)
      (v/assert f (list dog Fido) ThisContext {:strength :monotonic})
      (is (= 1 (count (v/sentexes-matching f (list dog '?x) ThisContext))))
      (is (seq (v/sentexes-matching f (list 'mammal '?x) ThisContext)))
      (is (v/isa? f Fido 'thing))
      (v/retract! f (v/handle-of f (list dog Fido) ThisContext))
      (is (empty? (v/sentexes-matching f (list 'mammal '?x) ThisContext)) "and retraction sweeps"))
    (is (zero? (v/sentex-count base)) "the empty base stayed empty")
    (v/clear! f)))

(deftest a-fork-inherits-the-front-door-policies
  ;; A fork is a hypothesis over the base's own content, so it has to hold that content
  ;; to the base's conventions.  A fork that quietly refused a clash the base would have
  ;; arbitrated — or held a lenient corpus to `:strict` — answers a different question
  ;; from the one the caller asked, and nothing in the call says so.
  (let [base (doto (v/open-kb (assoc (base-opts 10) :naming :warn :constraints :arbitrate
                                     :recover? false))
               (v/clear!))]
    (try
      (let [f (v/fork base (fork-opts 10))]
        (is (= :warn (:naming f)))
        (is (= :arbitrate (:constraints f)))
        (testing "and the inherited policy is the one that acts"
          (tu/with-terms [dog_t cat_t Fido ThisContext]
            (v/assert f (list 'disjoint dog_t cat_t) ThisContext)
            (v/assert f (list dog_t Fido) ThisContext)
            (is (v/assert f (list cat_t Fido) ThisContext)
                "the base arbitrates, so the fork admits the clash rather than refusing")
            (is (= 1 (count (v/contradictions f))))))
        (v/clear! f))
      (testing "and the fork's own opts still win"
        (let [g (v/fork base (assoc (fork-opts 11) :naming :strict :constraints :refuse))]
          (is (= :strict (:naming g)))
          (is (= :refuse (:constraints g)))
          (v/clear! g)))
      (finally (v/clear! base)))))

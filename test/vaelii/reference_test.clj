;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.reference-test
  "The engine's belief against the belief reference (docs/reference.md), and against
  itself across arrival orders.

  Two kinds of test:

  - **Fixed worlds.** Scenarios run in every arrival order of the writes that can move,
    with the expected belief at named contexts written out.  These need no reference.
  - **Random worlds.** `vaelii.ref.gen/gen-world` over a fixed seed set, each world run in
    every permutation of its writes when it has at most `exhaustive-up-to` of them and in
    a seeded sample of orders otherwise.  The reference judges every write offered
    (decision D8): a write the engine refuses is a divergence of an `:engine-refused-*`
    kind, and every belief disagreement of a run that refused nothing is shrunk and
    classified (`gen/divergences`).

  **The known-divergence rule.** A divergence whose `:kind` is a key of
  `known-divergences` is counted and printed, one line per kind; any other kind fails
  the test, with one summary line per divergence and its EDN report under
  `gen/default-report-dir`.  No divergence is dropped without being counted.

  Every KB here is an in-RAM KB on a space of its own, opened by `gen/load-world!` and
  closed with its stores dropped in a `finally`, so no test shares a store with another
  and none uses the `vaelii.test-util` fixtures or their net-neutrality check: a KB that
  is closed and dropped leaves nothing behind to check."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [vaelii.ref.believe :as believe]
            [vaelii.ref.gen :as gen]
            [vaelii.ref.nogoods :as nogoods]
            [vaelii.test-util :as tu]))

(def known-divergences
  "The divergence kinds the engine shows at HEAD against the decisions of 2026-09-29 (D1–D17),
  each naming the decision it departs from and the engine change it waits on.  A kind
  leaves this map when the change lands."
  {:engine-refused-clash
   {:decision "D8"
    :waits-on "a new prompt: store an all-monotonic definitional clash and report it"
    :note     "the entry point refuses the second member of a hard disjoint, functional, cover, asymmetric or anti_transitive clash"}
   :engine-refused-mark
   {:decision "D7"
    :waits-on "a new prompt: decide an irreflexive or anti_symmetric violation as a nogood"
    :note     "the entry point refuses a tuple an irreflexive or anti_symmetric mark already stored convicts"}
   :engine-refused-genl-related
   {:decision "D8"
    :waits-on "a new prompt: store a disjoint over genl-related types, or a cover with a disjoint part, as a hard clash"
    :note     "the entry point refuses the declaration as not-well-formed after reading the stored genl and disjoint content, so what is stored depends on arrival order"}
   :late-mark-reported
   {:decision "D7"
    :waits-on "a new prompt: decide an irreflexive or anti_symmetric violation as a nogood"
    :note     "a mark arriving after the tuple it convicts files a report and leaves the tuple believed"}
   :verdict-bound-below-vantage
   {:decision "D3"
    :waits-on "a new prompt reversing settle prompt 23"
    :note     "a reader below a vantage that reads the clash released keeps the vantage's loser OUT"}
   :exception-not-reasked-below-placement
   {:decision "D4"
    :waits-on "a new prompt: ask unknown and exceptWhen at every reader below the placement"
    :note     "a blocker visible at the reader and not at the placement context leaves the conclusion believed"}
   :naf-conclusion-monotonic
   {:decision "D14"
    :waits-on "a new prompt: cap a guarded firing's class at :default"
    :note     "a firing through unknown or exceptWhen over monotonic grounds confers :monotonic, so its conclusion defeats a :default member the reference ties it with"}
   :exit-gate
   {:decision "D8"
    :waits-on "prompt 29"
    :note     "a pass whose only work is a released unknown-guarded rule ends the settle"}
   :pass-count
   {:decision "D2"
    :waits-on "prompt 30"
    :note     "a second settle pass trusts the scoped defeats of the first"}
   :joint-view
   {:decision "D8"
    :waits-on "prompt 31"
    :note     "a genlCx edge arriving last forms the joint view at a common descendant and the clash is not found"}})

(def ^:private judges
  "`gen/check-world`'s judges.  `:reference` is `world -> {C {:believed :out :inherited
  :nogoods}}`."
  {:reference #(believe/believe % nogoods/families)})

(def ^:private U 'CxUniverse)

(defn- w
  "A world write; the strength defaults to `:default`, the engine's own default."
  ([s c] (w s c :default))
  ([s c strength] {:sentence s :context c :strength strength}))

;; ---- fixed worlds ------------------------------------------------------

(defn- expected-failures
  "Run `world` in each of `orders` and return one entry per order, context and sentence
  where the engine's belief differs from `expected` (`{C {S bool}}`), naming the order,
  both answers and what the engine refused in that order.  A run whose every refusal is
  of a kind in `known-divergences` is left out and its refusals are returned under
  `:known`; the result is `{:failures [...] :known {kind n}}`."
  [world orders expected]
  (let [runs  (mapv #(gen/run-order world % {}) orders)
        known (for [r runs rf (:refused r)
                    :let [k (gen/refusal-kind rf)]
                    :when (contains? known-divergences k)]
                k)
        judge (fn [{:keys [order beliefs refused]}]
                (if (and (seq refused)
                         (every? #(contains? known-divergences (gen/refusal-kind %)) refused))
                  []
                  (for [[c m] expected
                        [s want] m
                        :let [got (contains? (get beliefs c #{}) s)]
                        :when (not= want got)]
                    {:order    (mapv :sentence order)
                     :context  c
                     :sentence s
                     :engine   got
                     :expected want
                     :refused  (mapv (juxt (comp :sentence :refused) :type) refused)})))]
    {:failures (into [] (mapcat judge) runs)
     :known    (frequencies known)}))

(defn- failure-text [label failures n]
  (str label ": " (count failures) " wrong reading(s) over " n " orders"
       (apply str (for [f (take 4 failures)] (str "\n  " (pr-str f))))))

(defn- print-known [label known]
  (doseq [[k n] (sort-by key known)]
    (println (str label ": known divergence " (name k) " × " n " ("
                  (:decision (known-divergences k)) ", waits on "
                  (:waits-on (known-divergences k)) ")"))))

(defn- release-lattice
  "The release lattice of `scoped_defeat_test` with the denial above CxB, as
  `[world wiring content]`:

    CxUniverse  (genl chi thing) (genl dog thing) (genl cat thing)
                (disjoint dog cat) monotonic
      ├─ CxA    (genl chi dog) default
      └─ CxD    (not (genl chi dog)) monotonic
    CxB sees CxA and CxD: (chi Kit) default, (cat Kit) monotonic

  CxB reads no separation between chi and cat, so both memberships are believed there."
  [{:keys [chi dog cat Kit CxA CxB CxD]}]
  (let [wiring  [(w (list 'genl chi 'thing) U) (w (list 'genl dog 'thing) U)
                 (w (list 'genl cat 'thing) U)
                 (w (list 'genlCx CxA U) U) (w (list 'genlCx CxB CxA) U)
                 (w (list 'genlCx CxD U) U) (w (list 'genlCx CxB CxD) U)
                 (w (list 'disjoint dog cat) U :monotonic)
                 (w (list 'genl chi dog) CxA)]
        content [(w (list 'not (list 'genl chi dog)) CxD :monotonic)
                 (w (list chi Kit) CxB)
                 (w (list cat Kit) CxB :monotonic)]]
    [{:contexts #{U CxA CxB CxD} :writes (into wiring content)} wiring content]))

(deftest the-release-lattice-believes-both-memberships-at-its-reader-in-every-order
  (tu/with-terms [chi dog cat Kit CxA CxB CxD]
    (let [[world wiring content] (release-lattice {:chi chi :dog dog :cat cat :Kit Kit
                                                   :CxA CxA :CxB CxB :CxD CxD})
          orders (mapv #(into wiring %) (gen/permutations content))
          {fails :failures known :known}
          (expected-failures world orders {CxB {(list chi Kit) true (list cat Kit) true}})]
      (print-known "release lattice" known)
      (is (empty? fails) (failure-text "release lattice" fails (count orders))))))

(defn- classify-failures
  "Split `fails` (from `expected-failures`) into `{:failures [...] :known {kind n}}` by
  `gen/classify` over the reference's result on `world`: a failure whose kind is in
  `known-divergences` is counted under `:known`, merged into `known`, and the rest stay
  failures."
  [world fails known]
  (let [ref (believe/believe world nogoods/families)]
    (reduce (fn [acc d]
              (let [kind (gen/classify world ref (assoc d :reference (:expected d)))]
                (if (contains? known-divergences kind)
                  (update-in acc [:known kind] (fnil inc 0))
                  (update acc :failures conj d))))
            {:failures [] :known known}
            fails)))

(deftest an-irreflexive-mark-takes-a-default-self-tuple-out-in-either-order
  ;; Decision D7: an irreflexive violation is a one-member nogood, so a :default self
  ;; tuple is OUT wherever the mark is visible, whichever arrives first.  The engine
  ;; refuses the tuple when the mark is stored first (the known divergence
  ;; :engine-refused-mark) and reports and keeps it when the tuple is stored first
  ;; (:late-mark-reported); both are counted and printed instead of judged.
  (tu/with-terms [properPartOf Ann CxA]
    (let [mark   (w (list 'irreflexive properPartOf) CxA :monotonic)
          self   (w (list properPartOf Ann Ann) CxA)
          world  {:contexts #{CxA} :writes [mark self]}
          orders (gen/permutations [mark self])
          {fails :failures known :known}
          (expected-failures world orders {CxA {(list properPartOf Ann Ann) false}})
          {fails :failures known :known} (classify-failures world fails known)]
      (print-known "irreflexive self tuple" known)
      (is (empty? fails) (failure-text "irreflexive self tuple" fails (count orders))))))

;; ---- random worlds -----------------------------------------------------

(defn- check-seed
  "Generate the world for `seed`, check it in the orders `order-opts` selects, and return
  `{:runs :refused :store-split :merge-skips :divergences}`, each divergence carrying its
  `:seed`."
  [seed order-opts]
  (let [world  (gen/gen-world seed {})
        orders (gen/orders-for world (assoc order-opts :seed seed))
        check  (gen/check-world world orders judges)]
    {:runs        (:runs check)
     :refused     (:refused check)
     :store-split (:store-split check)
     :merge-skips (count (:merge-skips check))
     :divergences (mapv #(assoc % :seed seed) (gen/divergences world check judges))}))

(defn- random-worlds
  "Check every seed of `seeds`, print one line with the number of worlds and runs, the
  refusals counted by `:type` and the refused sentence's functor, the number of worlds
  whose orders stored different content, the contexts skipped for a `:merge` verdict and
  the wall time, then one line per kind of `known-divergences` with its count.  Returns
  the report lines of every divergence of a kind outside `known-divergences`."
  [label seeds order-opts]
  (let [t0      (System/nanoTime)
        results (mapv #(check-seed % order-opts) seeds)
        divs    (mapcat :divergences results)
        counts  (frequencies (map :kind divs))]
    (println (str label ": " (count seeds) " worlds, "
                  (reduce + (map :runs results)) " runs, refusals "
                  (pr-str (frequencies (for [{:keys [type refused]} (mapcat :refused results)]
                                         [type (first (:sentence refused))])))
                  ", store splits " (count (filter :store-split results))
                  ", merge skips " (reduce + (map :merge-skips results))
                  ", " (quot (- (System/nanoTime) t0) 1000000) " ms"))
    (print-known label (into (sorted-map) (for [k (keys known-divergences)] [k (get counts k 0)])))
    (into [] (for [d divs
                   :when (not (contains? known-divergences (:kind d)))]
               (gen/report! (:seed d) d)))))

;; A run (open, load, read, close) costs about 3.7 ms.  Twenty worlds walked whole up to
;; six writes are about 3,000 runs and 11 s, so the sampled test walks every order only
;; up to four writes; the slow twin walks two hundred worlds whole up to six.

(deftest a-random-world-settles-as-the-reference-says
  (let [unknown (random-worlds "reference sampled" (range 1 21)
                               {:exhaustive-up-to 4 :sample 8})]
    (is (empty? unknown) (str/join "\n" unknown))))

(deftest ^:slow two-hundred-random-worlds-settle-as-the-reference-says
  (let [unknown (random-worlds "reference slow" (range 1 201)
                               {:exhaustive-up-to 6 :sample 8})]
    (is (empty? unknown) (str/join "\n" unknown))))

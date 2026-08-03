;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.round-trip-test
  "Export a KB and import it back: the oracle for the portable dump.

  It compares two **KBs**, not two files, because what a dump promises is not bytes —
  it is that the knowledge comes back.  So every comparison is over *content*: a handle
  is a number this build minted and a round trip never promised the same numbers, which
  is why a sentence embedding one (`(exceptWhen … (sentexHandle H))`) is compared by
  what the handle names rather than by the number.

  Where the two sides disagree, the reading side is right by construction — it
  re-canonicalizes everything through this build's own constructor — so a difference is
  a lossy *writer*.

  Both directions across backends (`:memory` → dump → `:disk`, and back), because a
  format that only round-trips within one backend is not a format."
  (:require [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.test :refer [deftest is testing]]
            [clojure.walk :as walk]
            [vaelii.core :as v]
            [vaelii.impl.catalog :as catalog]
            [vaelii.impl.disk.backend :as backend]
            [vaelii.impl.io.export :as export]
            [vaelii.impl.io.import :as imp]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.rules :as vr]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu])
  (:import (java.io File)
           (java.nio.file Files)
           (java.nio.file.attribute FileAttribute)))

;;; ── scaffolding ───────────────────────────────────────────────────────

(defn- temp-dir ^File [nm]
  (.toFile (Files/createTempDirectory (str "vaelii-rt-" nm "-") (into-array FileAttribute []))))

(defn- rm-rf! [^File d]
  (doseq [^File f (reverse (file-seq d))] (.delete f)))

(defn- memory-kb
  "A cleared KB on the suite's scratch pair, forced to `:memory` whatever the suite's
  backend gate says — this namespace is *about* the two backends, so it names both."
  []
  (doto (v/open-kb (assoc tu/scratch-space :backend :memory)) (tu/clear-kb!)))

(defn- disk-kb [^File dir]
  (v/open-kb {:backend :disk :dir (.getPath dir) :recover? false}))

;;; ── the KB under test ─────────────────────────────────────────────────

(defn- terms []
  (tu/with-terms [bird penguin animal flies feathered nests happy
                  parentOf grandparentOf ancestorOf
                  Tweety Opus Rex Ann Bob Cid Preferred Deprecated
                  StoryContext SubStoryContext]
    {:bird bird :penguin penguin :animal animal :flies flies :feathered feathered
     :nests nests :happy happy
     :parentOf parentOf :grandparentOf grandparentOf :ancestorOf ancestorOf
     :Tweety Tweety :Opus Opus :Rex Rex :Ann Ann :Bob Bob :Cid Cid
     :Preferred Preferred :Deprecated Deprecated
     :ctx StoryContext :sub SubStoryContext}))

(defn- build!
  "Every shape a round trip has ever dropped, in one KB."
  [kb {:keys [bird penguin animal flies feathered nests happy
              parentOf grandparentOf ancestorOf
              Tweety Opus Rex Ann Bob Cid Preferred Deprecated ctx sub]}]
  (binding [v/*clock*   (constantly 1750000000000)
            v/*creator* "round-trip-test"]
    ;; a taxonomy to recover: a genl edge and a context edge
    (v/assert kb (list 'genl penguin bird) ctx {:strength :monotonic})
    (v/assert kb (list 'genl bird animal) ctx {:strength :monotonic})
    (v/assert kb (list 'genlContext sub ctx) sub)
    ;; a defeasible forward rule that states its own exception, and a second rule
    ;; concluding the same literal — so `(flies Tweety)` rests on two justifications
    (v/assert kb (list 'exceptWhen (list penguin '?b)
                       (list 'set/defaultRule
                             (vr/rule-sentence [(list bird '?b)] (list flies '?b))))
              ctx)
    (v/assert kb (list 'set/forwardRule (vr/rule-sentence [(list feathered '?f)]
                                                          (list flies '?f)))
              ctx)
    ;; a backward-only rule, and a rule with a conjunctive antecedent whose variables
    ;; the canonical form renumbers
    (v/assert kb (list 'set/backwardRule (vr/rule-sentence [(list flies '?a)] (list nests '?a)))
              ctx)
    (v/assert kb (vr/rule-sentence [(list parentOf '?x '?y) (list parentOf '?y '?z)]
                                   (list grandparentOf '?x '?z))
              ctx)
    ;; ground facts, one known-true, and the join that fires the conjunctive rule
    (v/assert kb (list bird Tweety) ctx {:strength :monotonic})
    (v/assert kb (list feathered Tweety) ctx)
    (v/assert kb (list bird Opus) ctx)
    (v/assert kb (list penguin Opus) ctx)          ; blocks the flight rule for Opus
    (v/assert kb (list parentOf Ann Bob) ctx)
    (v/assert kb (list parentOf Bob Cid) ctx)
    ;; a negative fact, defeated by the known-true positive: stored, not believed
    (v/assert kb (list 'not (list happy Rex)) ctx)
    (v/assert kb (list happy Rex) ctx {:strength :monotonic})
    ;; an equality merge: the retired spelling is superseded, and what mentioned it
    ;; gets a derived twin under the representative
    (v/assert kb (list bird Deprecated) sub)
    (v/assert kb (list 'rewriteOf Preferred Deprecated) ctx)
    ;; provenance an application layered on afterwards
    (v/add-provenance kb (v/handle-of kb (list bird Tweety) ctx) {:source :field-guide})
    ;; a term the ancestor rule mentions nowhere else, so the vocabulary is not
    ;; accidentally the same set twice
    (v/assert kb (list 'set/inertRule (vr/rule-sentence [(list parentOf '?p '?q)]
                                                        (list ancestorOf '?p '?q)))
              ctx)))

;;; ── the oracle ────────────────────────────────────────────────────────

(defn- deref-handles
  "A sentence with every `(sentexHandle H)` replaced by the *content* H names.  A
  meta-sentex points at a rule by number; the round trip promises the same rule, not
  the same number."
  [kb sentence]
  (walk/postwalk (fn [x]
                   (if-let [id (sx/handle-id x)]
                     (list 'sentexHandle (:sentence (v/sentex kb id)))
                     x))
                 sentence))

(defn- content
  "A sentex as content: its whole field map, minus the handle, with embedded handles
  dereferenced.  The *whole* map, because the fields a translation drops silently are
  `:varmap` (every rule then renders as ?var0), `:direction` and `:defeasible`."
  [kb sx]
  (-> (into {} sx)
      (dissoc :id)
      (update :sentence #(deref-handles kb %))))

(defn- content-of [kb h] (some->> (v/sentex kb h) (content kb)))

(defn- same!
  "Assert two collections of content hold the same things, reporting **what differs**
  rather than both sides in full — a KB printed twice is unreadable, and the answer to
  \"what did the round trip lose\" is a handful of records."
  [label source target]
  (let [a (set source) b (set target)]
    ;; a snapshot that came out empty would make every comparison below pass on nothing
    (is (pos? (count source)) (str label ": the fixture holds none — the oracle is vacuous"))
    (is (= (count source) (count a)) (str label ": source content is not unique"))
    (is (empty? (set/difference a b)) (str label " — in the source and not the copy"))
    (is (empty? (set/difference b a)) (str label " — in the copy and not the source"))))

(defn- sentex-contents [kb]
  (map #(content-of kb %) (p/sentex-ids (:records kb))))

(defn- justification-contents
  "Every justification as content: what it rests on, what it concludes, what licensed
  it, and the class it confers."
  [kb]
  (vec
   (for [jid (p/justification-ids (:records kb))
         :let [j (v/justification kb jid)]]
     {:antecedents (set (map #(content-of kb %) (:antecedents j)))
      :consequence (content-of kb (:consequence j))
      :informant   (if (integer? (:informant j)) (content-of kb (:informant j)) (:informant j))
      :bindings    (:bindings j)
      :strength    (:strength j)})))

(defn- beliefs
  "What is believed, keyed by content — and for what is not, the reason `why-not` gives,
  since \"not believed\" is several different situations and a round trip has to land in
  the same one."
  [kb]
  (vec
   (for [h (p/sentex-ids (:records kb))
         :let [in? (v/in? kb h)]]
     [(content-of kb h) (if in? :in (:reason (v/why-not kb h)))])))

(defn- taxonomy [kb]
  {:types    (set (v/types kb))
   :contexts (set (v/contexts kb))
   :genls    (into {} (for [t (v/types kb)] [t (set (v/genls kb t))]))
   :up       (into {} (for [c (v/contexts kb)] [c (set (v/context-up kb c))]))})

(defn- provenance-contents [kb]
  (vec (for [h (p/sentex-ids (:records kb))
             :let [prov (v/provenance kb h)]
             :when prov]
         [(content-of kb h) prov])))

(defn- compare-kbs!
  "Assert `target` holds the same knowledge as `source`."
  [source target]
  (testing "the same stored sentences"
    (same! "sentences" (sentex-contents source) (sentex-contents target)))
  (testing "the same justifications, as what they rest on"
    (same! "justifications" (justification-contents source) (justification-contents target)))
  (testing "the same beliefs, and the same reason for each that is not believed"
    (same! "beliefs" (beliefs source) (beliefs target)))
  (testing "the same taxonomy after recover"
    (is (= (taxonomy source) (taxonomy target))))
  (testing "the same provenance"
    (same! "provenance" (provenance-contents source) (provenance-contents target)))
  (testing "the same vocabulary"
    (is (= (set (v/terms source)) (set (v/terms target))))))

(defn- round-trip!
  "Build a KB with `open-source`, export it, import into a KB from `open-target`, and
  run `(f source target summary)`."
  [open-source open-target f]
  (let [dump (temp-dir "dump")]
    (rm-rf! dump)                                   ; export! makes its own directory
    (let [t      (terms)
          source (open-source)
          target (open-target)]
      (try
        (build! source t)
        (export/export! source dump {:compression :none})
        (let [summary (imp/import-dump target dump)]
          (f source target summary t))
        (finally (rm-rf! dump))))))

;;; ── the round trips ───────────────────────────────────────────────────

(deftest memory-out-disk-in
  (let [store (temp-dir "disk-in")]
    (try
      (tu/with-cleared-kb [_ memory-kb]
        (round-trip!
         (fn [] (memory-kb))                        ; the same cleared scratch KB
         (fn [] (disk-kb store))
         (fn [source target summary _t]
           (testing "the summary says what it read and what it did with the handles"
             (is (= :pure (:dialect summary)))
             (is (= :preserved (:handle-policy summary)))
             (is (zero? (:collapsed summary)) "nothing canonicalized onto another handle")
             (is (zero? (:rewritten-handles summary))
                 "nothing to rewrite: the embedded handle is already the right number")
             (is (zero? (:dropped-justifications summary)))
             (is (zero? (:dropped-meta-sentexes summary))))
           (compare-kbs! source target))))
      (finally (backend/close-dir! (.getPath store)) (rm-rf! store)))))

(deftest disk-out-memory-in
  (let [store (temp-dir "disk-out")]
    (try
      (tu/with-cleared-kb [_ memory-kb]
        (round-trip!
         (fn [] (disk-kb store))
         (fn [] (memory-kb))
         (fn [source target _summary _t] (compare-kbs! source target))))
      (finally (backend/close-dir! (.getPath store)) (rm-rf! store)))))

;;; ── handles ───────────────────────────────────────────────────────────

(defn- meta-sentexes
  "The `exceptWhen` meta-sentexes, as `[own-handle embedded-handle]` — the one place a
  handle is stored *inside content*, and so the one place its number has to be right
  rather than merely consistent."
  [kb]
  (set (for [h (p/sentex-ids (:records kb))
             :let [s (:sentence (v/sentex kb h))]
             :when (and (seq? s) (= 'exceptWhen (first s)))]
         [h (first (keep sx/handle-id (tree-seq sequential? seq s)))])))

(deftest handles-are-identity-across-the-round-trip
  ;; The comparisons above are deliberately handle-free, because content is what a dump
  ;; owes.  This is the stronger claim ours makes on top: the numbers come back too.  An
  ;; index entry is a posting of handles, so replaying one is possible only over an
  ;; import that keeps them; and a caller holding a handle across an export/import cycle
  ;; is holding a reference rather than a coincidence.
  (let [store (temp-dir "handles")]
    (try
      (tu/with-cleared-kb [_ memory-kb]
        (round-trip!
         (fn [] (memory-kb))
         (fn [] (disk-kb store))
         (fn [source target _summary t]
           (let [sx-ids (p/sentex-ids (:records source))]
             (testing "the same sentex handles, each holding the same record"
               (is (= sx-ids (p/sentex-ids (:records target))))
               (doseq [h sx-ids]
                 (is (= (content-of source h) (content-of target h))
                     (str "handle " h " holds a different record"))))

             (testing "and the same justification handles"
               (is (= (p/justification-ids (:records source))
                      (p/justification-ids (:records target)))))

             (testing "so the handle a meta-sentex embeds is the same number, not just the same rule"
               (is (seq (meta-sentexes source)) "the fixture has one, or this proves nothing")
               (is (= (meta-sentexes source) (meta-sentexes target))))

             (testing "and the imported KB is still usable: a fresh assert cannot collide"
               ;; the corruption this exists to prevent — a counter left behind the
               ;; imported handles overwrites a record on the very next write.  Last,
               ;; because it adds to the target.
               (let [ceiling (apply max (concat sx-ids (p/justification-ids (:records target))))
                     h       (v/assert target (list (:bird t) (:Rex t)) (:ctx t))]
                 (is (< ceiling h))
                 (doseq [h sx-ids]
                   (is (some? (v/sentex target h))
                       (str "handle " h " was overwritten by the assert")))))))))
      (finally (backend/close-dir! (.getPath store)) (rm-rf! store)))))

(deftest records-only-reads-our-dialect-too
  ;; The `{:belief? false}` path exists for a corpus past what the JTMS scales to.  It
  ;; shares one seam with the belief path — `field-map->sentence` — so the dialect
  ;; discrimination has to hold there as well: the corpus lands stored and indexed, with
  ;; no TMS behind it.
  (let [dump (temp-dir "records-only")]
    (rm-rf! dump)
    (try
      (let [t (terms)]
        (tu/with-cleared-kb [source memory-kb]
          (build! source t)
          (export/export! source dump {:compression :none})
          (let [store (temp-dir "records-only-store")]
            (try
              (let [target  (disk-kb store)
                    summary (imp/import-dump target dump {:belief? false})]
                (is (false? (:belief? summary)))
                (is (= (v/sentex-count source) (:sentexes summary) (v/sentex-count target)))
                (is (zero? (:justifications summary)) "no belief, so nothing rests on anything")
                (is (seq (v/find-sentexes target (:Tweety t)))
                    "and the corpus is indexed — findable by any term it mentions"))
              (finally (backend/close-dir! (.getPath store)) (rm-rf! store))))))
      (finally (rm-rf! dump)))))

(deftest the-catalog-offers-a-dump-we-wrote-and-says-whose-it-is
  ;; `classify` keys on `meta.edn`, and ours carries both the keys it looks for — but a
  ;; card that only said "a dump" would leave the operator guessing which dialect (and so
  ;; how much re-canonicalization) a load faces.
  (let [root (temp-dir "catalog")
        dump (io/file root "an-export")]
    (try
      (tu/with-cleared-kb [source memory-kb]
        (build! source (terms))
        (export/export! source dump {:compression :none})
        (is (= :dump (catalog/classify dump)))
        (System/setProperty "vaelii.kb.path" (.getPath root))
        (try
          (let [card (first (filter #(= "an-export" (:name %)) (catalog/sources)))]
            (is (some? card) "discovered on the search path")
            (is (= :dump (:kind card)))
            (is (= :pure (:dialect card)) "and named as ours")
            (is (re-find #"our own dialect" (:blurb card)))
            (is (re-find #"justifications" (:blurb card))
                "counted in the units this dialect keeps"))
          (finally (System/clearProperty "vaelii.kb.path"))))
      (finally (rm-rf! root)))))

;;; ── the claims content comparison alone would not make ────────────────

(deftest what-the-round-trip-has-to-keep-working
  (let [store (temp-dir "claims")]
    (try
      (tu/with-cleared-kb [_ memory-kb]
        (round-trip!
         (fn [] (memory-kb))
         (fn [] (disk-kb store))
         (fn [source target _summary t]
           (let [{:keys [bird penguin flies nests grandparentOf
                         Tweety Opus Ann Cid Preferred Deprecated ctx]} t]

             (testing "the exception still blocks — the meta-sentex found its rule again"
               (is (seq   (v/sentexes-matching target (list flies Tweety) ctx)) "the unexcepted bird flies")
               (is (empty? (v/sentexes-matching target (list flies Opus) ctx)) "the penguin does not")
               (is (= :excepted (:reason (v/why-not target (list flies Opus) ctx)))))

             (testing "a rule reads back in the author's variable names, not ?var0"
               (let [rule-of (fn [kb]
                               (->> (p/sentex-ids (:records kb))
                                    (map #(v/sentex kb %))
                                    (filter #(= grandparentOf (some-> (:consequent %) first)))
                                    first))]
                 (is (some? (rule-of target)))
                 (is (= (v/readable-sentence (rule-of source))
                        (v/readable-sentence (rule-of target)))
                     "the varmap survived — losing it is silent and cosmetic")))

             (testing "backward chaining works over the imported rules"
               (is (seq (v/query target (list nests Tweety) ctx {:max-depth 3}))))

             (testing "the taxonomy answers, so the closures were rebuilt from the records"
               (is (v/genl? target penguin bird))
               (is (v/isa? target Opus bird)))

             (testing "the merge is still a merge"
               (is (v/deprecated? target Deprecated))
               (is (= Preferred (v/representative target Deprecated))))

             (testing "and the conjunctive rule's derived fact came across believed"
               (is (seq (v/sentexes-matching source (list grandparentOf Ann Cid) ctx)))
               (is (seq (v/sentexes-matching target (list grandparentOf Ann Cid) ctx))))))))
      (finally (backend/close-dir! (.getPath store)) (rm-rf! store)))))

;;; ── a corpus with spelling conventions of its own ─────────────────────

(defn- lenient-kb
  "A cleared `:memory` KB whose front door is open — the KB a corpus in someone else's
  dialect is loaded into."
  []
  (doto (v/open-kb (assoc tu/scratch-space :backend :memory :naming :off)) (tu/clear-kb!)))

(def ^:private foreign-dialect
  "Sentences shaped like the real imported corpus: a `Cx`-prefixed context rather than a
  `Context`-suffixed one, namespaced predicates, and argument names carrying a hyphen or
  a trailing apostrophe.  Every one of them is a name `assert` refuses under `:strict`,
  and not one of them is a name this build may quietly repair."
  '[(ex/disambiguator mining')
    (genl choriocarcinoma' testicular_cancer-reproductive)
    (sense game_theory' game-theory)
    (summary psychological_profiling-profiling "A technique used by law enforcement.")])

(deftest a-corpus-in-its-own-dialect-round-trips-verbatim
  ;; The property the whole naming policy rests on: a corpus the front door disagrees
  ;; with is *storable*, *portable* and *findable by the very names that broke the
  ;; convention* — and comes back spelled the way it went in.  A loader that silently
  ;; repaired `game-theory` to `gameTheory` would round-trip its own invention, and the
  ;; corpus it was given would be gone.
  (let [dump (temp-dir "foreign-dialect")]
    (rm-rf! dump)
    (try
      (tu/with-cleared-kb [source lenient-kb]
        (doseq [s foreign-dialect] (v/assert source s 'CxWell))
        (is (= (count foreign-dialect) (v/sentex-count source)))
        (export/export! source dump {:compression :none})
        (let [store (temp-dir "foreign-dialect-store")]
          (try
            (let [target  (disk-kb store)
                  summary (imp/import-dump target dump {:belief? false})]
              (testing "every sentence comes back spelling-identical"
                (is (= (set foreign-dialect)
                       (set (map #(:sentence (v/sentex target %))
                                 (p/sentex-ids (:records target)))))))
              (testing "and each is findable by the name that broke the convention"
                (doseq [t '[mining' game-theory choriocarcinoma'
                            psychological_profiling-profiling]]
                  (is (seq (v/find-sentexes target t)) (str "not findable by " t))))
              (testing "the load reports the disagreement it did not enforce"
                ;; the whole point of counting rather than checking: the operator who
                ;; chose the bulk path learns the number while the records go past
                (let [{:keys [checked refused by-class] :as tally} (:naming summary)]
                  (is (= (count foreign-dialect) checked refused)
                      "every record — they share a context the front door refuses")
                  (is (= (count foreign-dialect) (:context-name by-class)))
                  (is (= (count foreign-dialect) (:argument by-class))
                      "and every one also carries a hyphenated or apostrophed name")
                  (is (re-find #"records .* `assert` would refuse" (nm/tally-line tally)))))
              (testing "and a strict KB over the same store still reads all of it"
                ;; the policy travels with the KB, not with the records
                (let [strict (v/open-kb {:backend :disk :dir (.getPath store)
                                         :recover? false :naming :strict})]
                  (is (= :strict (:naming strict)))
                  (is (seq (v/find-sentexes strict 'game-theory))))))
            (finally (backend/close-dir! (.getPath store)) (rm-rf! store)))))
      (finally (rm-rf! dump)))))

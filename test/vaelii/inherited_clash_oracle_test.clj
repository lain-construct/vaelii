;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.inherited-clash-oracle-test
  "The carried inherited clashes are the ones a full re-ask finds, and the ones a KB built
  from scratch finds.

  A randomized oracle runs one operation stream into two KBs, one with
  `discovery/*incremental-preserving*` bound false, and compares believed content, dilemmas,
  conflicts and refusals after every step, so a divergence names its operation.  A second
  replays what a stream left stored into a fresh KB in content order and compares the
  final readings, since both arms of the first ask through `discovery/preserving-entry`.  A
  third closes a `:disk-snapshot` KB after every write and reopens it from its reasoning
  image, so the memo the incremental arm carries crosses an install.  The
  stream writes claims of a preserved asymmetric predicate in three contexts, the `genl`
  edges and declarations the readings travel, and the `genlCx` edge that brings two
  contexts' claims into one reader (docs/nmtms.md, \"What qualifies as a nogood\")."
  (:require [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.impl.decide.inherited :as inherited]
            [vaelii.impl.discovery :as discovery]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.types.reasoning :as reasoning]
            [vaelii.test-util :as tu])
  (:import [java.io File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]))

;; ---- the shared ontology ------------------------------------------------
;;
;;   CxIcBase   ibig binary, asymmetric, preserved along genl at both positions
;;     ├─ CxIcLeft
;;     └─ CxIcRight
;;   CxIcJoin sees both once the stream writes its two edges
;;
;;   ic_top ← ic_mid ← ic_low, ic_top ← ic_side, and ic_far on its own

(def ^:private ctxs '[CxIcBase CxIcLeft CxIcRight])
(def ^:private types '[ic_top ic_mid ic_low ic_side ic_far])
(def ^:private edges '[[ic_mid ic_top] [ic_low ic_mid] [ic_side ic_top] [ic_far ic_side]])

(defn- build-ontology! [kb]
  (v/with-deferred-settle kb
    (doseq [c (rest ctxs)]
      (v/assert kb (list 'genlCx c (first ctxs)) 'CxUniverse {:strength :monotonic}))
    (doseq [d '[(binary_predicate ibig) (asymmetric ibig)]]
      (v/assert kb d (first ctxs) {:strength :monotonic}))
    (doseq [t types]
      (v/assert kb (list 'genl t 'thing) (first ctxs) {:strength :monotonic}))))

;; ---- the operation stream -----------------------------------------------

(defn- rand-op
  "One write: a claim or its denial at a random tuple, context and strength, a `genl`
  edge or a declaration asserted or retracted, or a `genlCx` edge to `CxIcJoin`."
  [^java.util.Random rng]
  (let [pick (fn [xs] (nth xs (.nextInt rng (count xs))))
        ctx  #(pick ctxs)
        str8 #(if (zero? (.nextInt rng 2)) {:strength :monotonic} {})
        claim #(list 'ibig (pick types) (pick types))
        edge #(let [[a b] (pick edges)] (list 'genl a b))
        decl #(list 'transitiveInArgInverse 'ibig (inc (.nextInt rng 2)) 'genl)]
    (case (.nextInt rng 12)
      (0 1 2) [:assert (claim) (ctx) (str8)]
      3       [:assert (list 'not (claim)) (ctx) (str8)]
      4       [:retract (claim) (ctx)]
      (5 6)   [:assert (edge) (ctx) (str8)]
      7       [:retract (edge) (ctx)]
      8       [:assert (decl) (first ctxs) (str8)]
      9       [:retract (decl) (first ctxs)]
      10      [:assert (list 'genlCx 'CxIcJoin (nth ctxs 1)) 'CxUniverse {:strength :monotonic}]
      11      [:assert (list 'genlCx 'CxIcJoin (nth ctxs 2)) 'CxUniverse {:strength :monotonic}])))

(defn- apply-op!
  "Run one op, returning a refusal's `:type` as an observation the two KBs must agree on."
  [kb [kind sentence context opts]]
  (try (case kind
         :assert  (do (v/assert kb sentence context opts) :ok)
         :retract (if-let [h (v/handle-of kb sentence context)]
                    (do (v/retract! kb h) :ok)
                    :absent))
       (catch clojure.lang.ExceptionInfo e
         [:refused (:type (ex-data e))])))

;; ---- the observation ----------------------------------------------------

(defn- clash-key
  "A reported clash as content, without handles, which differ between the two KBs."
  [e]
  [(:priority e) (:kind e) (:sentence e) (:sentence (:inherited e))
   (into #{} (map (juxt :sentence :context :defeat-class)) (:sides e))])

(defn- snapshot [kb]
  {:believed  (into #{}
                    (comp (filter #(v/in? kb %))
                          (keep #(p/get-sentex (:records kb) %))
                          (map (juxt :sentence :context)))
                    (jtms/in-datums (reasoning/tms kb)))
   :standing  (into #{}
                    (for [[_ ng] (inherited/inherited-clashes kb)]
                      [(:sentence ng) (:vantages ng)]))
   :dilemmas  (into #{} (map clash-key) (v/contradictions kb))
   :conflicts (into #{} (map clash-key) (v/conflicts kb))
   :joined    (into #{} (map clash-key) (v/contradictions kb 'CxIcJoin))})

(defn- diff
  "`{key {la only-in-a lb only-in-b}}` over the snapshot keys where `a` and `b` differ."
  ([a b] (diff a b :incremental-only :exhaustive-only))
  ([a b la lb]
   (into {} (keep (fn [k]
                    (let [x (get a k) y (get b k)]
                      (when (not= x y)
                        [k {la (set/difference x y) lb (set/difference y x)}]))))
         (keys a))))

(defn- run-stream
  "The same ops into both KBs, comparing after every write.  Returns `[step op
  incremental-snapshot exhaustive-snapshot]` for the first divergence, or nil."
  [ops]
  (let [inc-kb (tu/fresh)
        exh-kb (tu/isolated-fresh)]
    (try
      (binding [discovery/*incremental-preserving* true]  (build-ontology! inc-kb))
      (binding [discovery/*incremental-preserving* false] (build-ontology! exh-kb))
      (loop [step 0, [op & more] ops]
        (if-not op
          nil
          (let [ri (binding [discovery/*incremental-preserving* true]  (apply-op! inc-kb op))
                re (binding [discovery/*incremental-preserving* false] (apply-op! exh-kb op))
                si (snapshot inc-kb)
                se (snapshot exh-kb)]
            (if (and (= ri re) (= si se))
              (recur (inc step) more)
              [step op si se]))))
      (finally (tu/clear-kb! inc-kb) (tu/clear-kb! exh-kb)))))

(defn- settled
  "`ops` into one KB under `incremental?`, returning the snapshot after the last."
  [ops incremental?]
  (let [kb (if incremental? (tu/fresh) (tu/isolated-fresh))]
    (try
      (binding [discovery/*incremental-preserving* incremental?]
        (build-ontology! kb)
        (run! #(apply-op! kb %) ops)
        (snapshot kb))
      (finally (tu/clear-kb! kb)))))

(defn- divergence [[step op si se]]
  (str "diverged at step " step " on " (pr-str op) "\n" (pr-str (diff si se))))

;; ---- oracle 1: randomized operation streams -----------------------------

(deftest randomized-streams-find-the-same-inherited-clashes
  (doseq [seed (range 10)]
    (let [rng (java.util.Random. (long seed))
          r   (run-stream (repeatedly 40 #(rand-op rng)))]
      (is (nil? r) (str "seed " seed " " (when r (divergence r)))))))

;; ---- oracle 2: directed streams -----------------------------------------

(deftest a-second-known-true-claim-is-read-where-the-first-was-carried
  ;; the declarations and edges `:default`, so the clash is a dilemma and its report names
  ;; the claim read; `(ibig ic_mid ic_side)` arrives reaching the same tuple and sorts
  ;; before `(ibig ic_top ic_side)`, with nothing of the standing clash moving
  (is (nil? (run-stream
             [[:assert '(transitiveInArgInverse ibig 1 genl) 'CxIcBase {}]
              [:assert '(transitiveInArgInverse ibig 2 genl) 'CxIcBase {}]
              [:assert '(genl ic_mid ic_top) 'CxIcBase {}]
              [:assert '(genl ic_low ic_mid) 'CxIcBase {}]
              [:assert '(ibig ic_side ic_low) 'CxIcBase {}]
              [:assert '(ibig ic_top ic_side) 'CxIcBase {:strength :monotonic}]
              [:assert '(ibig ic_far ic_far) 'CxIcBase {}]
              [:assert '(ibig ic_mid ic_side) 'CxIcBase {:strength :monotonic}]
              [:assert '(ibig ic_far ic_top) 'CxIcBase {}]]))))

(deftest a-reading-withdrawn-at-the-vantage-is-read-again-there
  ;; the stored claim is known-true, so the reading's `:default` edge is the pair's unique
  ;; weakest member and loses at CxIcJoin alone; CxIcJoin then reads the second route, and
  ;; every later settle clears the scoped defeats and decides them again
  (is (nil? (run-stream
             [[:assert '(genlCx CxIcJoin CxIcLeft) 'CxUniverse {:strength :monotonic}]
              [:assert '(genlCx CxIcJoin CxIcRight) 'CxUniverse {:strength :monotonic}]
              [:assert '(transitiveInArgInverse ibig 1 genl) 'CxIcBase {:strength :monotonic}]
              [:assert '(transitiveInArgInverse ibig 2 genl) 'CxIcBase {:strength :monotonic}]
              [:assert '(genl ic_low ic_mid) 'CxIcLeft {}]
              [:assert '(genl ic_mid ic_top) 'CxIcLeft {:strength :monotonic}]
              [:assert '(genl ic_low ic_far) 'CxIcLeft {}]
              [:assert '(genl ic_far ic_top) 'CxIcLeft {:strength :monotonic}]
              [:assert '(ibig ic_side ic_low) 'CxIcRight {:strength :monotonic}]
              [:assert '(ibig ic_top ic_side) 'CxIcLeft {:strength :monotonic}]
              [:assert '(ibig ic_far ic_far) 'CxIcBase {}]
              [:assert '(ibig ic_side ic_far) 'CxIcBase {}]]))))

(deftest a-clash-split-across-contexts-is-carried-through-its-scoped-defeat
  ;; the stored default in CxIcRight loses at CxIcJoin only, so every settle re-decides it
  ;; there while it stays believed in CxIcRight
  (is (nil? (run-stream
             [[:assert '(transitiveInArgInverse ibig 1 genl) 'CxIcBase {:strength :monotonic}]
              [:assert '(transitiveInArgInverse ibig 2 genl) 'CxIcBase {:strength :monotonic}]
              [:assert '(genl ic_low ic_mid) 'CxIcLeft {:strength :monotonic}]
              [:assert '(genl ic_mid ic_top) 'CxIcLeft {:strength :monotonic}]
              [:assert '(ibig ic_side ic_low) 'CxIcRight {}]
              [:assert '(genlCx CxIcJoin CxIcLeft) 'CxUniverse {:strength :monotonic}]
              [:assert '(genlCx CxIcJoin CxIcRight) 'CxUniverse {:strength :monotonic}]
              [:assert '(ibig ic_top ic_side) 'CxIcLeft {:strength :monotonic}]
              [:assert '(ibig ic_far ic_far) 'CxIcBase {}]
              [:retract '(genl ic_mid ic_top) 'CxIcLeft]
              [:assert '(ibig ic_far ic_side) 'CxIcBase {}]]))))

(deftest a-route-edge-raised-to-known-true-is-read-again
  ;; the reading rests on the direct `:default` edge until the route through ic_mid is
  ;; raised to `:monotonic`; the claim then opposes the stored converse at that route, and
  ;; the dilemma becomes a defeat with no member of the carried entry changing class
  (let [ops '[[:assert (transitiveInArgInverse ibig 1 genl) CxIcBase {:strength :monotonic}]
              [:assert (transitiveInArgInverse ibig 2 genl) CxIcBase {:strength :monotonic}]
              [:assert (genl ic_low ic_mid) CxIcBase {}]
              [:assert (genl ic_mid ic_top) CxIcBase {}]
              [:assert (genl ic_low ic_top) CxIcBase {}]
              [:assert (ibig ic_side ic_low) CxIcBase {}]
              [:assert (ibig ic_top ic_side) CxIcBase {:strength :monotonic}]
              [:assert (genl ic_low ic_mid) CxIcBase {:strength :monotonic}]
              [:assert (genl ic_mid ic_top) CxIcBase {:strength :monotonic}]]]
    (is (nil? (run-stream ops)))
    (is (= [#{} false]
           ((juxt :dilemmas #(contains? (:believed %) '[(ibig ic_side ic_low) CxIcBase]))
            (settled ops true))))))

(def ^:private joined-last
  "Two known-true claims in CxIcLeft and CxIcRight that clash through `(genl ic_low
  ic_mid)` in a reader that sees both, with that reader's second `genlCx` edge written
  last.  The `icAgeOf` pair gives CxIcLeft a scoped defeat, and the `anti_transitive`
  writes are settles whose region holds nothing of the clash."
  '[[:assert (functional icAgeOf) CxIcBase {:strength :monotonic}]
    [:assert (genl ic_low ic_mid) CxIcBase {:strength :monotonic}]
    [:assert (ibig ic_mid ic_low) CxIcRight {:strength :monotonic}]
    [:assert (icAgeOf IcI2 0) CxIcBase {}]
    [:assert (ibig ic_low ic_low) CxIcLeft {:strength :monotonic}]
    [:assert (icAgeOf IcI2 2) CxIcLeft {:strength :monotonic}]
    [:assert (genlCx CxIcJoin CxIcLeft) CxUniverse {:strength :monotonic}]
    [:assert (transitiveInArgInverse ibig 2 genl) CxIcBase {:strength :monotonic}]
    [:assert (anti_transitive icPrecedes) CxIcBase {:strength :monotonic}]
    [:assert (transitiveInArgInverse ibig 2 genl) CxIcBase {}]
    [:assert (anti_transitive icPrecedes) CxIcBase {:strength :monotonic}]
    [:assert (genlCx CxIcJoin CxIcRight) CxUniverse {:strength :monotonic}]])

(deftest a-genlCx-edge-that-joins-a-denial-and-its-claim-forms-the-pair-in-either-order
  (let [joins?    #(= 'genlCx (first (second %)))
        reference (settled (into (filterv joins? joined-last) (remove joins?) joined-last)
                           true)]
    (is (seq (:conflicts reference)))
    (is (nil? (run-stream joined-last)))
    (is (= reference (settled joined-last true) (settled joined-last false)))))

(def ^:private swept-claim
  "A standing clash whose stored side a guarded rule concludes, beside a second entry.
  Blocking the firing sweeps the conclusion, so the settle's second pass reads a region
  handle with no record; the release derives it again."
  '[[:assert (transitiveInArgInverse ibig 1 genl) CxIcBase {}]
    [:assert (genl ic_mid ic_top) CxIcBase {}]
    [:assert (genl ic_low ic_mid) CxIcBase {}]
    [:assert (ibig ic_top ic_side) CxIcBase {:strength :monotonic}]
    [:assert (exceptWhen (ic_skip ?x)
                         (set/defaultRule
                          (set/forwardRule (implies (and (icLink ?x ?y)) (ibig ?x ?y)))))
     CxIcBase {}]
    [:assert (icLink ic_side ic_low) CxIcBase {}]
    [:assert (ibig ic_far ic_side) CxIcBase {}]
    [:assert (ic_skip ic_side) CxIcBase {}]
    [:retract (ic_skip ic_side) CxIcBase]
    [:retract (icLink ic_side ic_low) CxIcBase]])

(deftest a-claim-a-guard-block-sweeps-leaves-the-clash-it-stood-in
  (is (seq (:dilemmas (settled (take 7 swept-claim) true))) "the derived claim clashes")
  (is (empty? (:dilemmas (settled (take 8 swept-claim) true))) "the block sweeps it")
  (is (nil? (run-stream swept-claim))))

(def ^:private retracted-reasons
  "A standing clash beside a second entry, then the mark, the declaration and an edge the
  reading rests on retracted and the first two asserted again: each retraction's region
  holds a handle with no record."
  '[[:assert (transitiveInArgInverse ibig 1 genl) CxIcBase {}]
    [:assert (genl ic_mid ic_top) CxIcBase {}]
    [:assert (genl ic_low ic_mid) CxIcBase {}]
    [:assert (ibig ic_side ic_low) CxIcBase {}]
    [:assert (ibig ic_top ic_side) CxIcBase {:strength :monotonic}]
    [:assert (ibig ic_far ic_side) CxIcBase {}]
    [:retract (asymmetric ibig) CxIcBase]
    [:assert (asymmetric ibig) CxIcBase {:strength :monotonic}]
    [:retract (transitiveInArgInverse ibig 1 genl) CxIcBase]
    [:assert (transitiveInArgInverse ibig 1 genl) CxIcBase {}]
    [:retract (genl ic_low ic_mid) CxIcBase]])

(deftest a-retracted-reason-leaves-the-clash-it-read
  (is (seq (:dilemmas (settled (take 6 retracted-reasons) true))) "the clash stands")
  (is (empty? (:dilemmas (settled (take 7 retracted-reasons) true))) "the mark leaves it")
  (is (nil? (run-stream retracted-reasons))))

(def ^:private predicate-edge-streams
  "A standing clash that a `genl` edge between predicates carries, then that edge
  retracted.  In the first stream the edge carries the `asymmetric` mark down to `icSub`
  (`tax/props-over`); in the second it makes `icSub`'s claim one of `ibig`'s.  The edge is
  neither a member of the entry nor its stored claim, and moves no input of the memo's
  stamp, so the entry is re-asked only because the retracted edge's sentence, kept under
  `:left` (`discovery/note-removed!`), reaches it."
  (let [edges '[[:assert (genl ic_low ic_mid) CxIcBase {:strength :monotonic}]
                [:assert (genl ic_mid ic_top) CxIcBase {:strength :monotonic}]
                [:assert (genl icSub ibig) CxIcBase {}]
                [:assert (icSub ic_top ic_side) CxIcBase {:strength :monotonic}]]
        drop  '[:retract (genl icSub ibig) CxIcBase]]
    [(-> '[[:assert (transitiveInArgInverse icSub 1 genl) CxIcBase {:strength :monotonic}]]
         (into edges)
         (conj '[:assert (icSub ic_side ic_low) CxIcBase {}] drop))
     (-> '[[:assert (transitiveInArgInverse ibig 1 genl) CxIcBase {:strength :monotonic}]]
         (into edges)
         (conj '[:assert (ibig ic_side ic_low) CxIcBase {}] drop))]))

(deftest a-retracted-genl-edge-between-predicates-leaves-the-clash-it-carried
  (doseq [ops predicate-edge-streams]
    (is (seq (:standing (settled (pop ops) true))) "the clash stands")
    (is (nil? (run-stream ops)))))

;; ---- oracle 3: the stored set replayed from scratch ----------------------

(defn- stored-set
  "The sentences `ops` name that `kb` still stores as premises, `[sentence context
  strength]`, in content order."
  [kb ops]
  (let [tms (reasoning/tms kb)]
    (->> (distinct (map (fn [[_ s c]] [s c]) ops))
         (keep (fn [[s c]]
                 (when-let [h (v/handle-of kb s c)]
                   (when-let [st (jtms/premise-strength tms h)] [s c st]))))
         (sort-by (fn [[s c]] [(pr-str s) (str c)])))))

(defn- replay-divergence
  "Run `ops` into one KB, replay its `stored-set` into a fresh KB one write at a time, and
  return the stored set and where the two final snapshots differ, or nil."
  [ops]
  (let [kb (tu/fresh)]
    (try
      (build-ontology! kb)
      (run! #(apply-op! kb %) ops)
      (let [streamed (snapshot kb)
            ws       (stored-set kb ops)
            rk       (tu/isolated-fresh)]
        (try
          (build-ontology! rk)
          (doseq [[s c st] ws] (v/assert rk s c {:strength st}))
          (let [replayed (snapshot rk)]
            (when (not= streamed replayed)
              {:stored ws :diff (diff streamed replayed :streamed-only :replayed-only)}))
          (finally (tu/clear-kb! rk))))
      (finally (tu/clear-kb! kb)))))

(defn- replayed-streams [seeds]
  (doseq [seed seeds]
    (let [rng (java.util.Random. (long seed))
          r   (replay-divergence (repeatedly 40 #(rand-op rng)))]
      (is (nil? r) (str "seed " seed " " (pr-str r))))))

(deftest ^:slow streams-replayed-from-scratch-read-as-streamed
  (replayed-streams (range 100 130)))

(deftest a-sample-of-streams-replayed-from-scratch-reads-as-streamed
  (replayed-streams (range 100 103)))

;; ---- a later pass of one settle -----------------------------------------

(defn- two-pass-settle
  "One settle over a batch that stores `n` claims and a standing clash beside a fact that
  blocks a guarded firing, so the settle runs a second pass whose window still holds every
  claim.  `[snapshot questions passes]` under `incremental?`, `questions` the
  `preserving-entry` calls the settle made."
  [n incremental?]
  (let [kb    (if incremental? (tu/fresh) (tu/isolated-fresh))
        calls (atom 0)
        orig  @#'discovery/preserving-entry]
    (try
      (binding [discovery/*incremental-preserving* incremental?]
        (build-ontology! kb)
        (v/assert kb '(exceptWhen (ic_skip ?x)
                                  (set/defaultRule
                                   (set/forwardRule (implies (and (ic_probe ?x)) (ic_seen ?x)))))
                  'CxIcBase)
        (doseq [x '[IcA IcB]] (v/assert kb (list 'ic_probe x) 'CxIcBase))
        (with-redefs [discovery/preserving-entry (fn [kb s] (swap! calls inc) (orig kb s))]
          (v/with-deferred-settle kb
            (run! #(apply-op! kb %)
                  (concat [[:assert '(transitiveInArgInverse ibig 1 genl) 'CxIcBase {}]
                           [:assert '(genl ic_mid ic_top) 'CxIcBase {}]
                           [:assert '(genl ic_low ic_mid) 'CxIcBase {}]
                           [:assert '(ibig ic_side ic_low) 'CxIcBase {}]
                           [:assert '(ibig ic_top ic_side) 'CxIcBase {:strength :monotonic}]]
                          (for [i (range n)]
                            [:assert (list 'ibig 'ic_far (symbol (str "ic_far_" i))) 'CxIcBase {}])
                          [[:assert '(ic_skip IcA) 'CxIcBase {}]]))))
        [(snapshot kb) @calls (:passes (v/settle-stats kb))])
      (finally (tu/clear-kb! kb)))))

(deftest a-later-pass-asks-only-the-claims-an-earlier-pass-moved
  ;; The window a pass reads spans the settle, so a second pass that read it whole would
  ;; ask every claim the first asked again; the discovery reads what the window recorded
  ;; since its own last mark (`jtms/touched-since`).  The exhaustive arm asks every pass.
  (let [n 60
        [si qi pi] (two-pass-settle n true)
        [se qe pe] (two-pass-settle n false)]
    (is (= 2 pi pe) "the batch's settle runs a second pass in each arm")
    (is (= si se) (pr-str (diff si se)))
    (is (seq (:dilemmas si)) "the standing clash is read in the batch")
    (is (< qi (+ n 10)) (str "the incremental arm asked " qi " questions over two passes"))
    (is (> qe (* 2 n)) (str "the exhaustive arm asks each pass whole: " qe))))

;; ---- a retraction in the region -----------------------------------------

(defn- retraction-settles
  "`n` stored claims that each keep an entry, each denied by a `:default` reading of a
  claim on `ic_top`, beside a guarded firing per term of `ic_probe`.  Then each op of
  `ops` under its own settle.  `[snapshot entries questions]` under `incremental?`,
  `questions` the `preserving-entry` calls each op's settle made."
  [n ops incremental?]
  (let [kb    (if incremental? (tu/fresh) (tu/isolated-fresh))
        calls (atom 0)
        orig  @#'discovery/preserving-entry]
    (try
      (binding [discovery/*incremental-preserving* incremental?]
        (build-ontology! kb)
        (v/assert kb '(exceptWhen (ic_skip ?x)
                                  (set/defaultRule
                                   (set/forwardRule (implies (and (ic_probe ?x)) (ic_seen ?x)))))
                  'CxIcBase)
        (v/with-deferred-settle kb
          (run! #(apply-op! kb %)
                (concat [[:assert '(transitiveInArgInverse ibig 1 genl) 'CxIcBase {}]
                         [:assert '(genl ic_mid ic_top) 'CxIcBase {}]
                         [:assert '(genl ic_low ic_mid) 'CxIcBase {}]
                         [:assert '(ic_probe IcA) 'CxIcBase {}]
                         [:assert '(ic_probe IcB) 'CxIcBase {}]]
                        (for [i (range n), :let [t (symbol (str "ic_s_" i))]]
                          [:assert (list 'ibig t 'ic_low) 'CxIcBase {}])
                        (for [i (range n), :let [t (symbol (str "ic_s_" i))]]
                          [:assert (list 'ibig 'ic_top t) 'CxIcRight {}]))))
        (let [entries (count (:entries @(reasoning/preserved-clashes kb)))
              qs      (with-redefs [discovery/preserving-entry
                                    (fn [kb s] (swap! calls inc) (orig kb s))]
                        (mapv (fn [op] (reset! calls 0) (apply-op! kb op) @calls) ops))]
          [(snapshot kb) entries qs]))
      (finally (tu/clear-kb! kb)))))

(deftest a-retraction-in-the-region-asks-only-what-it-moved
  ;; Each op's region holds a handle whose record is gone: a retracted fact with its
  ;; conclusion, a firing the guard block sweeps on a second pass, and a stored claim
  ;; holding an entry.  The exhaustive arm asks every entry on every settle.
  (let [n   40
        ops '[[:retract (ic_probe IcB) CxIcBase]
              [:assert (ic_skip IcA) CxIcBase {}]
              [:retract (ibig ic_s_0 ic_low) CxIcBase]]
        [si ni qi] (retraction-settles n ops true)
        [se _  qe] (retraction-settles n ops false)]
    (is (= si se) (pr-str (diff si se)))
    (is (>= ni n) (str ni " entries stand before the retractions"))
    (is (every? #(< % 10) qi) (str "the incremental arm asked " qi))
    (is (every? #(>= % (dec n)) qe) (str "the exhaustive arm asks every entry: " qe))))

;; ---- across an image install ----------------------------------------------

(defn- reopened-stream
  "`ops` into a `:disk-snapshot` KB that is closed after every write and reopened from
  its own reasoning image, and into an exhaustive KB, comparing after every write.
  Returns `[installs divergence]`: whether each reopen installed the image (an install
  leaves the manifest as it was), and `run-stream`'s divergence or nil."
  [ops]
  (let [dir    (str (Files/createTempDirectory "vaelii-ic-image-" (into-array FileAttribute [])))
        mf     (io/file dir "reasoning" "manifest.edn")
        text   #(when (.exists mf) (slurp mf))
        open   #(v/open-kb {:backend :disk-snapshot :dir dir})
        exh-kb (tu/isolated-fresh)]
    (try
      (binding [discovery/*incremental-preserving* false] (build-ontology! exh-kb))
      (let [kb (open)] (build-ontology! kb) (v/close! kb))
      (loop [step 0, [op & more] ops, installs []]
        (if-not op
          [installs nil]
          (let [before   (text)
                kb       (open)
                installs (conj installs (= before (text)))
                [ri si]  (try [(apply-op! kb op) (snapshot kb)] (finally (v/close! kb)))
                re       (binding [discovery/*incremental-preserving* false] (apply-op! exh-kb op))
                se       (snapshot exh-kb)]
            (if (and (= ri re) (= si se))
              (recur (inc step) more installs)
              [installs [step op si se]]))))
      (finally
        (tu/clear-kb! exh-kb)
        (doseq [^File f (reverse (file-seq (io/file dir)))] (.delete f))))))

(defn- reopened-streams
  "Each seed's stream of `n` writes through `reopened-stream`."
  [seeds n]
  ;; Each session's one write is its network's first settle, the settle a mark the image
  ;; carried from the session before would name.
  (doseq [seed seeds]
    (let [rng (java.util.Random. (long seed))
          [installs r] (reopened-stream (repeatedly n #(rand-op rng)))]
      (is (every? true? installs) (str "seed " seed " recovered on a reopen: " installs))
      (is (nil? r) (str "seed " seed " " (when r (divergence r)))))))

(deftest ^:slow streams-reopened-from-the-image-after-every-write-find-the-same-inherited-clashes
  (reopened-streams (range 200 210) 20))

(deftest a-sampled-stream-reopened-from-the-image-finds-the-same-inherited-clashes
  ;; seed 201's eighteenth write is a denial whose clash a mark carried across the install
  ;; hid
  (reopened-streams [201] 18))

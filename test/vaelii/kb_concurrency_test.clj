;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.kb-concurrency-test
  "A reader thread beside the writer, one level up from the network.

  `vaelii.jtms-concurrency-test` holds the same guarantee for the truth-maintenance
  structures themselves.  This is the guarantee **through the API**: the reads an
  application actually makes — `sentexes-matching`, the `genl` closure, and belief off a
  handle — while a writer asserts and retracts in bursts.  Those reads cross more state
  than the TMS: the index postings, the record store behind them, the taxonomy closure
  caches, and the literal-match cache, each of which the writer is moving.

  Four things must hold, and they are what the checks below count:

  - **No reader ever throws.**  An index posting is written before the record it points
    at is, and swept after — a read that caught either gap on an unsynchronized
    structure would fault or hand back nothing.
  - **Nothing is invented.**  Every sentence a read returns is one the writer wrote.  A
    torn posting is not a wrong answer that looks plausible; it is content from another
    handle, which is what makes this the check worth having.
  - **A read is internally consistent.**  A sentex a match returns carries its own
    sentence and handle — the posting resolved to a record inside the one read, rather
    than to a hole the sweep had already made.
  - **Locality holds under load.**  The writer churns one region; a monotonic fact and a
    taxonomy edge *outside* it are believed and true at every sample, never briefly
    false while a relabel or a closure recompute passes over something else.

  Both representations run, in one test, with the same assertions either way — the
  reference (persistent maps, consistent by construction) is the control, and the dense
  network (bitmaps mutated in place under a `StampedLock`) is the claim the default
  rests on.  Which one the suite's own KBs use (`VAELII_TEST_TMS`) changes nothing
  here: each arm names its representation."
  (:require [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.test-util :as tu]))

(def ^:private pool
  "The individuals the writer churns.  A fixed pool, so \"nothing invented\" is a set
  membership rather than a pattern match."
  (mapv #(symbol (str "Churn" %)) (range 8)))

(def ^:private burst-ms
  "How long one representation's writer churns.  Long enough that a reader samples the
  middle of many bursts and not only their edges; short enough that both arms and the
  suite around them stay a test rather than a run."
  2500)

(defn- seed!
  "The fixed region — believed throughout, and never written again — plus the rule that
  makes the churned region derive something."
  [kb]
  (v/assert kb '(genl dog animal) 'CxUniverse {:strength :monotonic})
  (v/assert kb '(genl animal thing) 'CxUniverse {:strength :monotonic})
  (v/assert-rule kb '[(dog ?x)] '(likes ?x Water) 'CxUniverse)
  (v/assert kb '(dog Anchor) 'CxUniverse {:strength :monotonic})
  (v/handle-of kb '(dog Anchor) 'CxUniverse))

(defn- known-sentences
  "Every sentence the writer can ever have written, as a set — the churned facts, what
  the rule concludes from them, and the fixed region."
  []
  (into #{'(genl dog animal) '(genl animal thing) '(dog Anchor) '(likes Anchor Water)
          '(genl churn_kind animal)}
        (mapcat (fn [x] [(list 'dog x) (list 'likes x 'Water)]))
        pool))

(defn- stress
  "Run the readers-beside-a-writer stress on a KB using `tms` and report what the readers
  saw: `{:errors [...] :invented n :torn n :stale n :reads n :writes n}`."
  [tms]
  (let [kb      (v/open-kb {:backend :memory :space [::kb-concurrency tms]
                            :tms tms :recover? false})
        _       (tu/clear-kb! kb)
        anchor  (seed! kb)
        known   (known-sentences)
        stop    (atom false)
        errs    (atom [])
        invented (atom 0)
        torn    (atom 0)
        stale   (atom 0)
        reads   (atom 0)
        writes  (atom 0)
        reader  (fn []
                  (try
                    (while (not @stop)
                      (let [ms (v/sentexes-matching kb '(likes ?x Water) 'CxUniverse)]
                        (doseq [sx ms]
                          (when-not (contains? known (:sentence sx)) (swap! invented inc))
                          (when-not (and (:sentence sx) (integer? (:id sx)))
                            (swap! torn inc))))
                      ;; the region the writer never touches: a relabel or a closure
                      ;; recompute over the churned region must not pass through it
                      (when-not (v/genl? kb 'dog 'thing)          (swap! stale inc))
                      (when-not (v/isa? kb 'Anchor 'animal)       (swap! stale inc))
                      (when-not (v/believed? kb anchor 'CxUniverse) (swap! stale inc))
                      (swap! reads inc))
                    (catch Throwable t (swap! errs conj t))))
        writer  (future
                  (try
                    (let [deadline (+ (System/currentTimeMillis) (long burst-ms))]
                      (while (< (System/currentTimeMillis) deadline)
                        ;; a burst: every churned fact in, then every one out, so the
                        ;; rule's conclusions are minted and swept each pass
                        (let [hs (mapv #(v/assert kb (list 'dog %) 'CxUniverse) pool)]
                          (doseq [h hs] (v/retract! kb h)))
                        ;; and a taxonomy edge, which moves the genl closure the readers
                        ;; are asking about the *other* side of
                        (let [h (v/assert kb '(genl churn_kind animal) 'CxUniverse)]
                          (v/retract! kb h))
                        (swap! writes inc)))
                    (finally (reset! stop true))))
        rs      (mapv (fn [_] (future (reader))) (range 3))]
    @writer
    (run! deref rs)
    (tu/clear-kb! kb)
    {:errors @errs :invented @invented :torn @torn :stale @stale
     :reads @reads :writes @writes}))

(defn- check!
  "The four claims, asserted the same number of times for either representation."
  [label {:keys [errors invented torn stale reads writes]}]
  (is (empty? errors)
      (str label ": a reader faulted beside the writer — "
           (when-let [^Throwable t (first errors)]
             (str (class t) ": " (.getMessage t)))))
  (is (zero? invented)
      (str label ": a read returned a sentence the writer never wrote (" invented ")"))
  (is (zero? torn)
      (str label ": a match returned a sentex with no sentence or no handle (" torn ")"))
  (is (zero? stale)
      (str label ": a fact or taxonomy edge outside the churned region read false ("
           stale ") — a relabel or a closure recompute reached past its region"))
  (is (pos? reads) (str label ": the readers never ran"))
  (is (pos? writes) (str label ": the writer never completed a burst")))

(deftest ^:slow kb-reads-stay-consistent-under-a-concurrent-writer
  ;; Both representations in one test, so the count is the same however the suite's own
  ;; KBs are configured — `VAELII_TEST_TMS` picks what `tu/fresh` builds and has no say
  ;; over the two KBs here.
  (doseq [tms [:dense :reference]]
    (check! (name tms) (stress tms))))

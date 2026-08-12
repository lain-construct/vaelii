;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.assert-cost-test
  "What one assert costs the index, as **counted operations** — the gate for the class of
  regression `lein perf` is structurally blind to.

  `bench/vaelii/bench/perf.clj` asserts a ratio and never a millisecond, which is what
  makes it survive a loaded laptop.  The price of that is stated in its own preamble: **a
  ratio cannot see a constant.**  An unconditional read added to the assert path moves the
  reading at both sizes by the same amount and divides out, so every one of its checks
  passes untouched.  One regression has already shipped through that gap —
  `inter-args-problem` ran its `interArgIsa` declaration retrieval unconditionally, on
  every assert of every KB, and nothing declares `interArgIsa` (`f64b334`, ~11% per assert
  of a declaration-carrying predicate).  It was found by hand, against a worktree at the
  parent commit.

  This gate closes that gap from the other side.  It runs ten fixed workloads with
  `vaelii.impl.profile` collecting and pins the **exact** index-operation counts each one
  costs: every `IndexStore` read by family, every `index-sentex` batch op by family, and
  every `unindex-sentex!` batch op by family.  Six of the ten assert and four retract, so
  a constant added to either write path lands here.

  ## Why a count and not a duration

  The quantity is an integer the engine computes, not a measurement of the machine, so
  there is no warm-up, no tail mean, no noise floor and no tolerance.  It is bit-identical
  across runs, across machines and across a loaded box — which is the standing complaint
  against the ratio gate and the reason this one can live in the suite rather than behind
  a command somebody has to remember.  It costs a few seconds.

  It is also *more sensitive than a duration in the region that matters*.  The historical
  regression above is 4.8% of the plain workload's total reads, which no wall-clock gate
  would separate from noise — and 33% of the `:argument-root` family, which this one
  fails on.  Counting per family is what buys that: a constant hides in a total and
  stands out in the family it lands on.

  ## Why exact, and not a ceiling

  A ceiling would let a change spend anything already budgeted, and the budget is not a
  design target — it is a record of what the engine does today.  Exact equality means any
  movement, in either direction, is a diff somebody has to look at and either explain or
  fix, and the number that lands beside the explanation is the change's own cost.  That is
  the whole product: an index change proposing a new family becomes a line saying how many
  operations per assert it added.

  So a legitimate optimization **fails this gate**, and that is correct.  Re-pin the
  number, and the commit that does so carries the improvement as data.

  ## What it does not catch

  - **Work that is not an index operation.**  Computation, allocation, a record-store
    read, a taxonomy walk.  The seams are on `IndexStore`, so a constant added between two
    of them is invisible here.
  - **A more expensive version of the same operation.**  One `sentexes-with-arg` counts
    once whether it returns four handles or four million.  `lein perf`'s
    `intersect-selectivity` is the check that holds *that*, and this gate does not
    subsume it.
  - **A retraction cost read as a per-retraction constant.**  `unindex-sentex!` reports
    what it cost (`:retracts`, docs/profile.md), so a teardown is budgeted the same way —
    except `:dead`, the trie nodes a removal emptied, which is decided by what else is
    still stored under the same prefix rather than by the sentex.  It is exact for a
    fixed corpus torn down in a fixed order, which is what a workload is, and it is not a
    figure another corpus reproduces.  So a moved `:dead` is read against the workload
    that produced it: change `n` or the shape of the facts and it moves for that reason
    alone, where every other family scales with `n`.
  - **A store that is not `KvIndexStore`.**  The columnar index walks its own trie and
    reports nothing, which is why the KB below is pinned to `:backend :memory` instead of
    inheriting whatever `scripts/test-backends.sh` selected.  The gate therefore says the
    same thing on all eight backend runs rather than eight different things.
  - **A configuration other than the shipped one.**  `with-shipped-retrieval` pins the
    four switches that decide which family answers a read, so the budgets are a claim
    about the defaults and about nothing else.  The reference retrieval path
    (`VAELII_HIER=0`) really does cost differently — two reads per sentex off
    `:argument-root` and onto `:trie-lookup` — and it carries no budget here.
  - **Anything that scales.**  A cost that grows with the KB is `lein perf`'s subject and
    it is a ratio for good reason.  The two gates are complements: that one holds the
    *shape*, this one holds the *constant*, and neither sees the other's regressions."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

;; The instrument is process-wide, so a test that threw while collecting would hand the
;; next namespace a running tally.
(use-fixtures :each (fn [t] (try (t) (finally (prof/stop)))))

(def ^:private n
  "Operations per workload — asserts in the six assert workloads, retractions in the four
  teardowns.  Large enough that a per-operation constant lands as a three-digit difference
  rather than a rounding one, small enough that ten workloads are a few seconds."
  100)

(def ^:private cost-space
  "The KB every workload runs on: in-RAM, its own space, the reference TMS.

  Pinned rather than inherited, and each half has its own reason.  The **backend**,
  because the seams live in `KvIndexStore` and the columnar store has none — inheriting
  `VAELII_TEST_BACKEND` would make this gate read near-zero on the two columnar runs and
  pass by measuring nothing.  The **TMS**, because a budget is a claim about one
  configuration and `VAELII_TEST_TMS=dense` is a different one.  Derived from
  `tu/plain-memory-space` so it follows `VAELII_TEST_SPACE` when a parallel run moves the
  block, with one more segment so it shares a store with nothing."
  (-> tu/plain-memory-space
      (update :space conj ::cost)
      (assoc :tms :reference)))

(defn- fresh []
  (let [kb (v/open-kb cost-space)]
    (p/clear-records! (:records kb))
    (p/clear-index!   (:index kb))
    kb))

(defn- ind [prefix i] (symbol (str prefix i)))

;; ---- the workloads -------------------------------------------------------
;;
;; Each returns a **thunk**, and the split is the whole reason the counts are stable:
;; everything the workload needs in place — the KB, its taxonomy, its declarations, its
;; rule — is built by the time the thunk is called, so `measure` starts the instrument
;; over the asserts being priced and nothing else.  Building the KB inside would count
;; `open-kb`'s coverage-gate read, which is one op and differs on the first call in a
;; process.

(defn- plain
  "A binary fact of fresh individuals: no declaration, no membership, no rule.  The floor,
  and the workload the shipped `interArgIsa` regression is clearest on, because a KB with
  nothing to check should be paying for nothing."
  []
  (let [kb (fresh)]
    (fn [] (dotimes [i n]
             (v/assert kb (list 'acPlain (ind "AcA" i) (ind "AcB" i)) 'CxPerf {})))))

(defn- membership
  "A type membership into a declared taxonomy — the arriving fact `settle` does real work
  for, since the disjointness arm reads the term's own argument-1 root."
  []
  (let [kb (fresh)]
    (v/assert kb '(genl acm_t thing) 'CxPerf {:strength :monotonic})
    (fn [] (dotimes [i n]
             (v/assert kb (list 'acm_t (ind "AcM" i)) 'CxPerf {})))))

(defn- declared
  "A fact of a predicate carrying an `argIsa` declaration at both positions, over
  individuals that already hold the type.  **The shape of the historical regression**: the
  argument-constraint checks are the reads `assert` names as its dominant per-fact cost,
  so a fourth declaration kind read unconditionally lands here first."
  []
  (let [kb (fresh)]
    (v/assert kb '(genl acd_t thing) 'CxPerf {:strength :monotonic})
    (v/assert kb '(argIsa acDecl 1 acd_t) 'CxPerf {:strength :monotonic})
    (v/assert kb '(argIsa acDecl 2 acd_t) 'CxPerf {:strength :monotonic})
    (dotimes [i n] (v/assert kb (list 'acd_t (ind "AcD" i)) 'CxPerf {}))
    (fn [] (dotimes [i n]
             (v/assert kb (list 'acDecl (ind "AcD" i) (ind "AcD" i)) 'CxPerf {})))))

(defn- negative
  "A negative fact with no positive twin.  Its own workload because the `:false` node is a
  separate trie subtree and the polarity checks are a separate read path — a constant
  added to the negation arm shows up here and in none of the others."
  []
  (let [kb (fresh)]
    (fn [] (dotimes [i n]
             (v/assert kb (list 'not (list 'acNeg (ind "AcN" i) 'AcNval)) 'CxPerf {})))))

(defn- compound
  "A fact carrying a compound argument, which is the write side of the structural trie and
  the term index at once: the compound linearizes into extra trie levels and its interior
  atoms each earn a term posting."
  []
  (let [kb (fresh)]
    (fn [] (dotimes [i n]
             (v/assert kb (list 'acCmp (ind "AcC" i) (list 'acFn (ind "AcC" i) 'AcUnit))
                       'CxPerf {})))))

(defn- rule-fired
  "A fact arriving through one forward rule, so each assert indexes **two** sentexes — the
  datum and the conclusion.  The derived half is where an index cost is easiest to add
  without noticing, since nothing a caller wrote is on that path."
  []
  (let [kb (fresh)]
    (v/assert kb (rules/rule-sentence ['(acSrc ?x ?y)] '(acDst ?x ?y))
              'CxPerf {:strength :monotonic})
    (fn [] (dotimes [i n]
             (v/assert kb (list 'acSrc (ind "AcR" i) (ind "AcS" i)) 'CxPerf {})))))

;; ---- the retraction workloads --------------------------------------------
;;
;; The same shape with one difference: the thunk **retracts**, and everything it retracts
;; was asserted during the build.  So the instrument covers the teardowns and none of the
;; asserts that set them up, exactly as the six above cover asserts and not the taxonomy
;; behind them.
;;
;; What a retraction costs is countable because `unindex-sentex!` reports it
;; (`:retracts`, docs/profile.md).  What it is **not** is quotable per retraction, and
;; `:dead` is why: how many trie nodes a removal empties is decided by what else is still
;; stored under the same prefix, so the number below is a property of *this corpus torn
;; down in this order* and not of a fact of this shape.  Every other family is decided by
;; the sentex and reads like an assert budget.

(def ^:private nat-population
  "Reified NATs standing in the KB for the two NAT workloads.  Its own knob rather than
  `n`, because it is the quantity the bystander read budget is currently proportional to
  while `n` counts retractions — separating them is what lets a re-pin say which of the
  two moved."
  100)

(defn- plain-teardown
  "The `plain` workload's n facts, retracted in the order they arrived.  The floor for a
  teardown, and the one an unconditional read added to the retraction path is clearest
  on, for the reason `plain` is the clearest on the assert path: a KB with nothing to
  check should be paying for nothing."
  []
  (let [kb (fresh)
        hs (mapv (fn [i] (v/assert kb (list 'acPlain (ind "AcA" i) (ind "AcB" i))
                                   'CxPerf {}))
                 (range n))]
    (fn [] (doseq [h hs] (v/retract! kb h)))))

(defn- rule-derived-teardown
  "The `rule-fired` workload's n premises, retracted.  Each teardown unindexes **two**
  sentexes — the datum and the conclusion it solely supported — so this is the workload
  that prices the dependency-directed sweep's own removals rather than only the ones a
  caller asked for."
  []
  (let [kb (fresh)]
    (v/assert kb (rules/rule-sentence ['(acSrc ?x ?y)] '(acDst ?x ?y))
              'CxPerf {:strength :monotonic})
    (let [hs (mapv (fn [i] (v/assert kb (list 'acSrc (ind "AcR" i) (ind "AcS" i))
                                     'CxPerf {}))
                   (range n))]
      (fn [] (doseq [h hs] (v/retract! kb h))))))

(defn- nat-bystander-teardown
  "n plain facts retracted on a KB carrying `nat-population` **live** reified NATs that
  none of them names.

  A teardown runs the reified-NAT orphan collection, since a constant whose last use has
  just gone would leave its `termOfUnit` map dangling a raw `nat/` symbol
  (docs/nat.md).  Here it has nothing to collect at any point: every constant is named by
  its own `(acNatUse …)` fact and no retraction touches one, so the population is the same
  after the workload as before it and every read the sweep takes is a read that changed
  nothing.

  So its read budget is a reading of the sweep's **candidate set** rather than of the
  retraction, and it tracks `nat-population`.  A sweep whose candidates are the constants
  the retracted sentexes named prices out near `plain-teardown` and breaks this budget on
  the way, which is the gate doing its job: re-pin from the failure report, where the
  delta is what the narrowing bought."
  []
  (let [kb (fresh)]
    (v/assert kb '(reifiableFunction AcNatFn) 'CxUniverse {:strength :monotonic})
    (dotimes [i nat-population]
      (v/assert kb (list 'acNatUse (ind "AcNU" i) (list 'AcNatFn (ind "AcNA" i)))
                'CxPerf {}))
    (let [hs (mapv (fn [i] (v/assert kb (list 'acBystand (ind "AcBy" i) 'AcByVal)
                                     'CxPerf {}))
                   (range n))]
      (fn [] (doseq [h hs] (v/retract! kb h))))))

(defn- nat-orphan-teardown
  "n facts retracted, each the **last use** of one reified NAT, so every teardown orphans
  a constant and unindexes its `termOfUnit` bookkeeping alongside the fact.

  The twin of `nat-bystander-teardown`, and the two fail for opposite reasons.  That one
  says the sweep must not read the population it is not about; this one says it must
  still collect the constant it *is* about — a narrowing that stops finding the orphan
  turns this workload's unindexed count from 2n into n, which is a correctness bug
  wearing a performance win's clothes."
  []
  (let [kb (fresh)]
    (v/assert kb '(reifiableFunction AcOrphFn) 'CxUniverse {:strength :monotonic})
    (let [hs (mapv (fn [i] (v/assert kb (list 'acOrphUse (ind "AcOU" i)
                                              (list 'AcOrphFn (ind "AcOA" i)))
                                     'CxPerf {}))
                   (range n))]
      (fn [] (doseq [h hs] (v/retract! kb h))))))

(def ^:private merge-population
  "Standing `sameAs` merges in the merge workload — its own knob rather than `n`, for
  `nat-population`'s reason: it is the quantity the reconcile's read budget could be
  proportional to while `n` counts retractions, and separating them is what lets a re-pin
  say which of the two moved."
  100)

(defn- merge-bystander-teardown
  "n plain facts retracted on a KB carrying `merge-population` standing `sameAs` merges
  that none of them names.

  The equality twin of `nat-bystander-teardown`, and it prices the same kind of thing.
  Every settle reconciles the superseded set against the equality closure, because a
  supersession is derived state that must not outlive the merge behind it
  (docs/equality.md).  Re-examining an entry means fetching its record, rewriting its
  sentence through the closure and probing the store for the restatement — so a
  reconcile that walks the whole displaced set puts `merge-population` store probes on
  every retraction of every KB that has merged anything.

  Here it has nothing to reconcile at any point: each merge displaces one `(mergeBorn
  AcMHi_i AcMPlace)` fact, no timed retraction names a merged term, and the closure is
  the same after the workload as before it.  So the budget is a reading of the
  reconcile's **scope**, and it tracks `merge-population` if the scope is the whole set
  and `n` if it is the moved region."
  []
  (let [kb (fresh)]
    (dotimes [i merge-population]
      (v/assert kb (list 'acMergeBorn (ind "AcMHi" i) 'AcMPlace) 'CxPerf {})
      (v/assert kb (list 'sameAs (ind "AcMAa" i) (ind "AcMHi" i)) 'CxPerf {}))
    (let [hs (mapv (fn [i] (v/assert kb (list 'acMergeBystand (ind "AcMBy" i) 'AcMByVal)
                                     'CxPerf {}))
                   (range n))]
      (fn [] (doseq [h hs] (v/retract! kb h))))))

;; ---- the budgets ---------------------------------------------------------
;;
;; Measured, not designed.  Each is what the engine does today at `n` = 100; the point of
;; writing them down is that the next change to any of these numbers is visible.  A
;; failure prints the delta per family, so re-pinning is reading the report.
;;
;; **`:functor-root` counts no visibility gate, and that is worth knowing before reading
;; it as high.**  Every assert runs a settle and a settle asks `res/excepted-handles`,
;; whose gate is the KB's own `:excepted` roster being empty (`kb/note-excepted!`) — a
;; deref, and no index read.  A gate keyed on the `except` functor root instead would add
;; three reads per assert to every workload here and seven to `rule-fired`, on a KB that
;; excepts nothing; none of that is in these numbers.

(def ^:private budgets
  [{:name    :plain
    :build   plain
    :sentexes 100
    :reads   {:argument-root 300 :argument-slot 100 :exception-index 100
              :functor-root 1000 :rule-index 100 :trie-counts 100 :trie-lookup 100}
    :writes  {:levels 500 :terms 400 :roots 400 :roster 202 :slots 200}}

   {:name    :membership
    :build   membership
    :sentexes 100
    :reads   {:argument-root 400 :argument-slot 200 :exception-index 100
              :functor-root 1000 :rule-index 200 :trie-counts 100 :trie-lookup 100}
    :writes  {:levels 400 :terms 300 :roots 300 :roster 100 :slots 100}}

   {:name    :declared
    :build   declared
    :sentexes 100
    :reads   {:argument-root 400 :argument-slot 200 :exception-index 100
              :functor-root 1000 :rule-index 100 :trie-counts 100 :trie-lookup 100}
    :writes  {:levels 500 :terms 300 :roots 400 :roster 0 :slots 200}}

   {:name    :negative
    :build   negative
    :sentexes 100
    :reads   {:argument-root 300 :argument-slot 100 :exception-index 200
              :functor-root 1000 :rule-index 100 :trie-counts 200 :trie-lookup 100}
    :writes  {:levels 400 :terms 400 :roots 400 :roster 103 :slots 101}}

   {:name    :compound
    :build   compound
    :sentexes 100
    :reads   {:argument-root 300 :argument-slot 100 :exception-index 100
              :functor-root 1000 :rule-index 100 :trie-counts 100 :trie-lookup 100}
    :writes  {:levels 800 :terms 600 :roots 400 :roster 104 :slots 200}}

   ;; 200 indexed sentexes for 100 asserts — the rule concludes one apiece
   {:name    :rule-fired
    :build   rule-fired
    :sentexes 200
    :reads   {:argument-root 600 :argument-slot 200 :exception-index 300
              :functor-root 1500 :rule-index 200 :trie-counts 200 :trie-lookup 200}
    :writes  {:levels 1000 :terms 800 :roots 800 :roster 200 :slots 400}}])

;; The retraction half.  `:unindexed` is the retraction budgets' `:sentexes` — how many
;; sentexes left the index — and it is checked first for the same reason: a budget
;; compared against a different number of teardowns is comparing two workloads.
;;
;; `:dead` inside `:retracts` is the one number here that is **not** a per-operation
;; constant, and it is budgeted anyway because it is exactly reproducible for a fixed
;; corpus torn down in a fixed order.  Read it as a property of this workload, never as
;; what a fact of this shape costs: the same fact retracted out of a corpus that shares
;; more prefix kills fewer nodes, and moving `n` moves this number non-proportionally
;; while every other family scales with it.
(def ^:private retraction-budgets
  [{:name    :plain-teardown
    :build   plain-teardown
    :sentexes 0
    :unindexed 100
    :reads   {:exception-index 100 :functor-root 700 :trie-counts 100}
    :writes  {}
    :retracts {:levels 500 :terms 400 :roots 400 :roster 202 :slots 200 :dead 302}}

   ;; 200 unindexed for 100 retractions — each premise solely supported one conclusion
   {:name    :rule-derived-teardown
    :build   rule-derived-teardown
    :sentexes 0
    :unindexed 200
    :reads   {:exception-index 200 :functor-root 900 :trie-counts 200}
    :writes  {}
    :retracts {:levels 1000 :terms 800 :roots 800 :roster 200 :slots 400 :dead 602}}

   ;; **`:functor-root` and `:term-index` are the two a narrowing of the orphan sweep
   ;; **The workload the orphan sweep's scope is priced by, and the numbers below are the
   ;; second pinning.**  The first read 10,800 functor-root and 10,000 term-index for 100
   ;; retractions — 108 and 100 per retraction, one pair per standing reified NAT, on a
   ;; teardown naming none of them and collecting none of them, because the sweep read what
   ;; the KB held rather than what the retraction reached.  Narrowed to the removed region
   ;; it is 7 functor-root and 0 term-index per retraction, which is `plain-teardown`'s own
   ;; cost: a bystander NAT population now costs a teardown nothing at all.  `:trie-lookup`
   ;; goes to 0 for the same reason.  The other five families are the same removal either
   ;; way and did not move.
   ;;
   ;; `:term-index` and `:trie-lookup` are **absent rather than pinned at 0**: a family the
   ;; workload never reads is a key the tally never emits, and under exact equality an
   ;; absent key is the stronger claim of the two — one read of either fails this budget.
   {:name    :nat-bystander-teardown
    :build   nat-bystander-teardown
    :sentexes 0
    :unindexed 100
    :reads   {:exception-index 100 :functor-root 700 :trie-counts 100}
    :writes  {}
    :retracts {:levels 500 :terms 400 :roots 400 :roster 102 :slots 101 :dead 301}}

   ;; 200 unindexed for 100 retractions — the use, plus the `termOfUnit` its removal
   ;; orphaned.  **That count is the workload's point and is not a number to re-pin
   ;; downward**: a sweep that stops finding the orphan unindexes 100 here and leaves a raw
   ;; `nat/` symbol behind, so the narrowing is admissible only while this stays 200.  It
   ;; did.  The reads fell with the scope, exactly as the bystander's did — the first
   ;; pinning read 11,800 functor-root and 10,100 term-index, off a *declining* population
   ;; the sweep walked twice per retraction (`:term-index` was 2·(100+99+…+1)).  What is
   ;; left is the region: 14 functor-root and 3 term-index per retraction, for a constant
   ;; the population no longer enters.
   ;;
   ;; The orphan question itself settles on the `termOfUnit` clause here — a collected
   ;; constant has its map and nothing else left — so it reads neither the expression nor
   ;; the declarations to find out what the mint wrote about it (`nat/minted-for`, held
   ;; behind a delay).  That is the whole of the difference between this budget and one
   ;; that asks those questions unconditionally: three functor-root reads and one
   ;; trie-lookup per retraction, on the path every teardown of a NAT-bearing KB takes.
   {:name    :nat-orphan-teardown
    :build   nat-orphan-teardown
    :sentexes 0
    :unindexed 200
    :reads   {:exception-index 200 :functor-root 1400 :term-index 300
              :trie-counts 200}
    :writes  {}
    :retracts {:levels 1200 :terms 1000 :roots 800 :roster 303 :slots 400 :dead 802}}

   ;; **The workload the supersession reconcile's scope is priced by**, and `:trie-lookup`
   ;; is the family that reads it: the reconcile probes the store for each displaced
   ;; spelling's restatement, so a pass over the whole displaced set costs one lookup per
   ;; standing merge per retraction.  A reconcile scoped to the KB reads **10,000** of them
   ;; here — 100 merges × 100 retractions, on a teardown that names none of them and
   ;; un-merges nothing — and one scoped to the moved region reads **none**.
   ;;
   ;; Everything else is `plain-teardown` exactly: 700 `:functor-root`, 100
   ;; `:exception-index`, 100 `:trie-counts`.  The three retract families that differ from
   ;; it (`:roster`, `:slots`, `:dead`) differ because the *victims* are a different shape
   ;; of fact, not because the merges are there.
   ;;
   ;; `:term-index` and `:trie-lookup` are **absent rather than pinned at 0**, and that is
   ;; the stronger claim: a family the workload never reads is a key the tally never emits,
   ;; so one read of either fails this budget.
   {:name    :merge-bystander-teardown
    :build   merge-bystander-teardown
    :sentexes 0
    :unindexed 100
    :reads   {:exception-index 100 :functor-root 700 :trie-counts 100}
    :writes  {}
    :retracts {:levels 500 :terms 400 :roots 400 :roster 102 :slots 101 :dead 301}}])

;; ---- measuring -----------------------------------------------------------

(defmacro ^:private with-shipped-retrieval
  "Run `body` under the four switches that decide where a read goes, each bound to its
  **shipped default** rather than to whatever the run inherited.

  A budget is a claim about one configuration, and these are the vars that change which
  family answers.  `scripts/test-sweeps.sh` runs the whole suite under `VAELII_HIER=0`,
  which routes context-scoped matching through the reference nested fan-out instead of the
  set-algebra path: measured here, that moves two reads per sentex off `:argument-root`
  and onto `:trie-lookup` — the trade the two paths exist to make, and a budget written for
  one of them is simply false about the other.  Pinning is the same argument that pins the
  backend, and it is preferred to standing aside, since a gate that skips under a sweep is
  a gate that is not running on the configuration somebody is currently changing."
  [& body]
  `(binding [res/*hierarchical-retrieval* true
             res/*arg-root-retrieval*     true
             res/*structural-index*       true
             sx/*min-indexed-depth*       1]
     ~@body))

(defn- by-family
  "One functor-keyed tally totalled across functors, with the operation count dropped.
  `{}` and not nil for a tally nothing wrote, since an absent family and an empty one are
  the same claim here and only one of them compares equal to a budget."
  [rows op-key]
  (reduce #(merge-with + %1 %2) {} (map #(dissoc % op-key) rows)))

(defn- measure
  "Run one workload under the instrument and total its tallies by family.  `:writes` and
  `:retracts` are keyed by functor in the snapshot, which is a diagnostic the *profile*
  wants and a distinction a budget does not: what a family costs an operation is the same
  question whichever predicate arrived.

  The KB is built inside the pinned configuration too: a taxonomy or a declaration laid
  down under one retrieval path and priced under another would be a workload nobody runs."
  [build]
  (with-shipped-retrieval
    (let [thunk (build)
          _     (prof/start)
          _     (thunk)
          snap  (prof/stop)
          wrows (vals (:writes snap))
          rrows (vals (:retracts snap))]
      {:reads     (into {} (:reads snap))
       :writes    (by-family wrows :asserts)
       :retracts  (by-family rrows :retracts)
       :sentexes  (reduce + 0 (map :asserts wrows))
       :unindexed (reduce + 0 (map :retracts rrows))})))

(defn- delta-report
  "The families whose count moved, as a table.  Every family either side names is listed,
  so a family that appeared from nowhere reads as `0 -> 300` rather than going missing."
  [expected actual]
  (->> (sort (into (set (keys expected)) (keys actual)))
       (keep (fn [k]
               (let [e (get expected k 0), a (get actual k 0)]
                 (when (not= e a)
                   (format "    %-16s %6d -> %-6d  (%+d)" (name k) e a (- a e))))))
       (str/join "\n")))

(defn- check-tally [what wl expected actual]
  (is (= expected actual)
      (format (str "%s: the %s budget moved.\n%s\n"
                   "  If this change is intended, re-pin the number in its budget — the diff "
                   "is the change's own index cost.\n"
                   "  If it is not, a constant was added to the path this workload drives "
                   "and `lein perf` cannot see it.")
              (name (:name wl)) what (delta-report expected actual))))

;; ---- the gate ------------------------------------------------------------

(defn- check-workload
  "One workload measured and held to its whole budget.  The two counts come first,
  because a budget compared against a different number of indexed or unindexed sentexes
  is comparing two workloads; the three tallies follow.  A workload that declares no
  `:writes` or `:retracts` budget is claiming the empty one, which is a claim worth
  making in both directions — an assert workload that started unindexing something, or a
  teardown that started writing, is a change somebody has to explain."
  [{:keys [name build sentexes unindexed] :as wl}]
  (testing (str "the " (clojure.core/name name) " workload")
    (let [got (measure build)]
      (is (= sentexes (:sentexes got))
          (str (clojure.core/name name) ": the workload indexed a different number of "
               "sentexes, so its budgets are about something else now"))
      (is (= (or unindexed 0) (:unindexed got))
          (str (clojure.core/name name) ": the workload unindexed a different number of "
               "sentexes, so its budgets are about something else now"))
      (check-tally "read"    wl (get wl :reads {})    (:reads got))
      (check-tally "write"   wl (get wl :writes {})   (:writes got))
      (check-tally "retract" wl (get wl :retracts {}) (:retracts got)))))

(deftest assert-cost-is-what-it-was
  (doseq [wl budgets] (check-workload wl)))

(deftest retraction-cost-is-what-it-was
  (doseq [wl retraction-budgets] (check-workload wl)))

(deftest instrument-is-silent-when-off
  ;; The budgets above are only meaningful if the seams cost nothing when nobody is
  ;; collecting — a gate on an instrument that is always running measures the instrument.
  (testing "a workload outside `start`/`stop` records nothing"
    (is (false? (prof/profiling?)))
    ((plain))
    (is (nil? (prof/snapshot)))))

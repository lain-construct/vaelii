;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.bench.perf
  "The performance regressions this engine has actually shipped, as a gate.

  Every `vaelii.bench.*` harness beside this one *reports* — it prints numbers a person
  reads.  This one *decides*, and it exists because the same defect has now landed twice:
  a per-operation cost that grows with something it should be independent of, turning a
  linear load quadratic.  The defaults phase rescanned every default rule per assert
  (docs/nmtms.md); definitional-clash discovery re-derived every standing pair per
  settle.  Neither broke a test.  Both
  were invisible until somebody sat down and measured, and both had been sitting in
  `main`.

  **What is asserted is a ratio, never a millisecond.**  A wall-clock threshold is either
  loose enough to be useless or tight enough to fail on a loaded laptop, and it has to be
  re-tuned on every machine the project is built on.  What the claims here are actually
  about is *shape*: a cost that should not grow with n is measured at two values of n
  eight to thirty-two times apart, and what is checked is the growth between them.  A
  machine that is twice as slow moves both readings and leaves the ratio alone.

  So a check fails only for the reason it exists: the cost grew with the thing it is
  supposed to be independent of.  Bounds carry real slack — a claim of *flat* passes at
  anything under 2×, which no algorithmic regression respects and no scheduler noise
  reaches.  Two further guards keep it from crying wolf: a check whose baseline is below
  `noise-floor-ns` reports `noise` and is not failed (a ratio between two readings that
  are mostly timer jitter means nothing), and a check that exceeds its bound is measured
  again from scratch, the better of the two runs standing — a GC pause landing in one
  window is not a regression, and a real one survives a second look.

  **A ratio is only as good as its baseline**, and both ways of getting that wrong have
  already happened here.  Warming the JVM proportionally to `n` gave the large size a
  head start and made an n-*independent* check read 0.68x (see `measure`).  And a
  baseline large enough to already carry the cost being measured divides that cost out of
  the answer: `clash-arbitration` at 100 vs 800 could not tell a healthy engine from one
  re-deriving every standing pair, because 100 pairs' worth of the per-pair cost was
  sitting in the denominator.  Both failures read as a *comfortable pass*.  So when
  adding a check, pick the small size to be a size at which the thing being measured has
  barely started.

  **A small baseline is also a cold one, so `--only` and the full run are two different
  measurements — and the difference is large enough to reverse a verdict.**  Where a
  reading is `a + b·n`, the ratio is decided by how big the n-independent `a` is at the
  baseline, and `a` is mostly JIT warmth: by the twentieth check of a run the JVM is far
  warmer than it is on the first.  `negation-arbitration` reads **5.70x under `--only`
  and 6.63x in the full run** on the same tree, and the split is entirely in the
  denominator — its n=100 baseline is 0.347 ms alone against 0.208 in place, while n=800
  barely moves (1.978 against 1.377).  So
  **`--only <name>` cannot clear a failure the full run reported**: it is a quicker way to
  iterate, not a second opinion, and a check that fails in the gate and passes alone has
  said where its baseline is rather than that the gate was wrong.  Judge a check where it
  runs — `retract-merge-scaling` and the two taxonomy-edge checks each carry their own
  numbers for this, and their bounds are read off full runs for it.

  **A bound is read off two measurements, not off one — and never off a guess.**  A
  plausible-looking number nobody measured states its claim in the same shape as every
  measured bound beside it, and no reader downstream can tell the two apart: not a failing
  gate, not a changelog line, not the next person deciding whether a ratio is healthy.  So
  calibrate a new check from **both** ends, on full runs.  Above: the healthy reading, more
  than once, since the spread between runs is what the slack has to cover.  Below: the
  shape the check exists to catch, implemented and measured, because that is the only way
  to know the bound sits under it.  Put the bound between, at about twice the worse healthy
  reading, which is the slack the arbitration checks carry.

  `standing-clash-reading` is the worked example, and it also shows why the guess is worth
  refusing: healthy it reads 85.4x and 80.9x over a floor near 66x, and with the read
  filtering the standing set by cross product it reads 937.8x.  A placeholder of 1000x —
  written to mean \"nobody has measured this\" — **passed** the defective shape.  A bound
  that cannot fail is not a lenient gate, it is an absent one wearing the same syntax.

  **What a ratio cannot see, and it is worth knowing before trusting a green run.**  A
  *constant* per-operation cost added to every write moves both readings by the same
  amount and leaves every ratio here alone — so a new unconditional retrieval on the
  assert path passes this gate untouched.  One has already shipped that way: a third
  argument-constraint declaration read, ~11% on every assert of a declaration-carrying
  predicate, invisible to all of these and found only by timing the absolute cost against
  the previous commit.

  **That class has its own gate now**, and it is a count rather than a duration:
  `test/vaelii/assert_cost_test.clj` pins the exact number of index operations ten fixed
  workloads cost, so an unconditional read added to the assert path fails the suite.
  Restoring the regression above passes every check here and fails six of the ten budgets
  there.  The two are complements — this file holds the *shape* of a cost and that one
  holds the *constant* — and a change to the write path wants both.

  Run: `lein perf [--only <name>] [--tolerance <x>] [--quick]`

    --only       run one check by name (the `:name` below, without the colon)
    --tolerance  multiply every bound by this — 1.5 on a noisy box, 1.0 in anger
    --quick      one attempt over the real pair at a 1.5x-widened bound — a coarse
                 verdict for a pre-commit read, still a verdict

  Exit status is 0 when every check passes, 1 when any fails, which is what makes it
  usable from a hook or a workflow."
  (:require [vaelii.core :as v]
            [vaelii.impl.asp.solve-context :as sc]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.columnar :as columnar]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.dense-kv :as dense]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.literal-cache :as lc]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.overlay.frozen :as frozen]
            [vaelii.impl.overlay.kv :as okv]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reroute :as reroute]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.space :as space]
            [vaelii.impl.special :as special]
            [vaelii.impl.stp :as stp]
            [vaelii.impl.taxonomy :as tax]))

;; ---- measurement --------------------------------------------------------

(def ^:private noise-floor-ns
  "Below this a per-operation reading is mostly timer and scheduler jitter, and the ratio
  of two such readings says nothing.  A check that lands here is reported and skipped
  rather than passed, so a check that becomes too fast to gate says so instead of turning
  into a green light nobody notices has stopped meaning anything."
  20000)                                                    ; 20µs

(defn- fresh-kb
  "An empty KB on its own space, so one check cannot leave state in another's."
  []
  (let [k (v/open-kb {:space 9 :recover? false})]
    (p/clear-records! (:records k))
    (p/clear-index!   (:index k))
    k))

(def ^:private tail-samples
  "How many readings from the end of a run the answer is the mean of — the same count at
  both sizes, so the two answers are averages over windows of equal width rather than
  over a fifth of two runs of different length."
  50)

(defn- tail-mean
  "The mean of the last `tail-samples` readings.  The *last*, because these checks grow a
  KB as they measure it and the question is always what an operation costs once the KB is
  the size the check is about — an average over the whole build would be dominated by the
  cheap early operations and would hide exactly the growth being looked for."
  ^double [xs]
  (let [v (vec xs)
        n (count v)
        k (min n (max 1 tail-samples))]
    (/ (double (reduce + (subvec v (- n k)))) k)))

(defn- measure
  "Per-operation nanoseconds for `f` at size `n`, after warming to `warm`.

  **Both sizes warm to the same amount**, and that is the whole point of the argument.
  Warming proportionally to `n` — a fifth of the run, say — hands the large size a JVM
  that has JIT-compiled the very code being timed while the small size is still climbing
  to it, and the reading comes back *faster at the larger size for no reason but that*.
  It is not a subtle effect: `arg-root-retrieval` does work that is n-independent by
  construction, and it measured 0.68x that way.

  A gate is exactly where that matters, since the bias flatters the large size and a
  ratio bound is a claim about the large size.  A regression would be measured against a
  baseline that had been quietly discounted."
  ^double [f n warm]
  (f warm)
  (f warm)
  (System/gc)
  (tail-mean (f n)))

(defmacro ^:private nanos [& body]
  `(let [t# (System/nanoTime)] ~@body (- (System/nanoTime) t#)))

;; ---- the checks ---------------------------------------------------------
;;
;; Each is `{:name :claim :sizes [small large] :max-ratio :run}`, where `:run` takes a
;; size and returns per-operation nanosecond readings.  `:claim` is what the check is
;; for; it prints beside the verdict, so a failure says which promise broke rather than
;; only which number moved.
;;
;; A check with no `:max-ratio` is a **baseline**: measured once at both sizes, printed
;; with its growth, and never judged.  It is the before-reading for a cost whose curve
;; still grows by design, and the change that flattens the curve gives it a bound read
;; off both ends, as the header says.  A baseline cannot fail the run, and its report
;; says so in place of PASS.

(defn- clash-arbitration
  "n individuals each holding two separated types, so the KB carries n standing dilemmas,
  and every assert settles against all of them.

  The discovery it gates is the same one the derivation path runs, so the entry point
  and a rule firing pay the same cost here."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(disjoint pa_t pb_t) 'CxPerf {:strength :monotonic})
    (doall
     (for [i (range n)
           :let [x (symbol (str "PX" i))]]
       (do (v/assert kb (list 'pa_t x) 'CxPerf {})
           (nanos (v/assert kb (list 'pb_t x) 'CxPerf {})))))))

(defn- constraint-exposure-shared-arg
  "n facts of a declared-`asymmetric` predicate that all share argument 1, under
  `:refuse`.

  **A declared property opens the tuple-mark candidates.**  This declares `asymmetric`,
  so each assert reads the converse its own arguments name (`decide/note-candidate!`).

  The shared argument is what makes it a claim rather than a formality: `PA`'s posting
  grows by one per assert, so a pass that walks it per assert is O(n) each and O(n²) over
  the load, and the reading tracks the KB rather than the region. One context throughout,
  so no pair is ever visible from anywhere and nothing is decided — this measures the
  cost of *deciding that*, which is the cost every assert on such a KB pays.

  **The posting is predicate-agnostic**, which is what makes the shape general rather
  than contrived: `believed-at-arg1` reads every sentex holding the term at argument 1
  and the functor filter runs after. So the risk is a heavily-used *individual* and not
  only a wide slot — a term at argument 1 of ten thousand facts of other predicates costs
  the same walk. This check drives it with one predicate because that is the shortest
  load that grows the posting; the narrowing it guards (`decide/note-candidate!` reads
  the one converse the tuple's arguments name) is what keeps either shape flat."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(asymmetric plarger) 'CxPerf {:strength :monotonic})
    (doall
     (for [i (range n)]
       (nanos (v/assert kb (list 'plarger 'PA (symbol (str "PL" i)))
                        'CxPerf {}))))))

(defn- per-reading-vantages
  "A cross-context membership pair whose separation is declared where the members'
  maximal common descendant cannot see it, under n contexts below that maximum.

  ```
  CxPA  (plt_a x)     CxPB  (plt_b x)     CxPDecl  (disjoint plt_a plt_b)
  CxPW sees CxPA and CxPB, and n contexts CxPL0 … see CxPW
   └─ CxPV sees CxPW and CxPDecl
  ```

  `CxPW` reads no separation, and `CxPV` does: each reader reads the separation over its
  own ancestor set (`membership/term-nogoods`).  **The claim is that an assert reads none of
  the n contexts below `CxPW`.**  Each timed assert is the second membership of a fresh
  term, so every one forms a pair, and the lattice is the only thing n moves.

  The maxima themselves are the other half of it: `CxPA` and `CxPB` see neither the other,
  so `tax/maximal-common-descendant-contexts` answers from its general path, which walks
  down from a member rather than filtering every common descendant."
  [n]
  (let [kb (fresh-kb)]
    (doseq [[k up] '[[CxPA CxUniverse] [CxPB CxUniverse] [CxPDecl CxUniverse]
                     [CxPW CxPA] [CxPW CxPB] [CxPV CxPW] [CxPV CxPDecl]]]
      (v/assert kb (list 'genlCx k up) 'CxUniverse {:strength :monotonic}))
    (v/assert kb '(disjoint plt_a plt_b) 'CxPDecl {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genlCx (symbol (str "CxPL" i)) 'CxPW) 'CxUniverse
                  {:strength :monotonic})))
    (doall
     (for [i (range 60)
           :let [x (symbol (str "PLX" i))]]
       (do (v/assert kb (list 'plt_a x) 'CxPA {})
           (nanos (v/assert kb (list 'plt_b x) 'CxPB {})))))))

(defn- chain-join
  "The closing step of an `anti_transitive` chain split across three contexts, beside n
  open chains split the same way.

  ```
  CxPA  (pnear a b)     CxPB  (pnear b c)     CxPC  (pnear a c)
  CxPAB, CxPBC and CxPAC each see two of them
   └─ CxPW sees all three
  ```

  The closing step reads the steps sharing an argument with it (`tuple/found-for`), and
  `CxPW`, which sees all three, decides the chain.  The open chains name terms of their
  own and share none with a timed chain, so the read reaches no posting n grows.  60 chains are closed and timed at
  either size, so the standing decisions are the same 60 at both.

  **The chain's cost past this is its standing decision.**  Measured when this check was
  added, n closed chains at 250 and 2000: the closing step 2.95 and 25.5 ms, an assert of
  an unrelated predicate beside the same n standing chains 3.42 and 27.7 ms, and this
  check's open chains 1.02 and 0.80 ms.  The growth is the standing set the settle
  republishes, which `clash-arbitration` prices, and a standing chain costs about twice a
  standing membership dilemma there (27.7 against 13.7 ms at 2000)."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (doseq [[k up] '[[CxPA CxUniverse] [CxPB CxUniverse] [CxPC CxUniverse]
                     [CxPAB CxPA] [CxPAB CxPB] [CxPBC CxPB] [CxPBC CxPC]
                     [CxPAC CxPA] [CxPAC CxPC]
                     [CxPW CxPAB] [CxPW CxPBC] [CxPW CxPAC]]]
      (v/assert kb (list 'genlCx k up) 'CxUniverse m))
    (v/assert kb '(binary_predicate pnear) 'CxUniverse m)
    (v/assert kb '(anti_transitive pnear) 'CxUniverse m)
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pnear (symbol (str "POA" i)) (symbol (str "POB" i))) 'CxPA m)
        (v/assert kb (list 'pnear (symbol (str "POB" i)) (symbol (str "POC" i))) 'CxPB m)))
    (doall
     (for [i (range 60)
           :let [a (symbol (str "PNA" i)) b (symbol (str "PNB" i)) c (symbol (str "PNC" i))]]
       (do (v/assert kb (list 'pnear a b) 'CxPA m)
           (v/assert kb (list 'pnear b c) 'CxPB m)
           (nanos (v/assert kb (list 'pnear a c) 'CxPC {})))))))

(defn- membership-read-under-busy-term
  "A type membership checked about a term that is already argument 1 of n facts of an
  unrelated binary predicate, on a KB that declares one separation.

  **The retrieval every definitional check bottoms out on.**  `kb/types-of` answers what
  types a term holds, and the disjointness arm asks it of the arriving sentence's
  argument on every membership.  The argument root cannot narrow to the memberships —
  `(T x)` and `(P x y)` share the `[1 x]` node and the trie level below it — so the read
  used to fetch the record behind every fact naming the term at argument 1 and keep the
  arity-1 ones.  A densely described individual therefore paid its whole description on
  every assert of a type for it, to find the handful of types it holds.
  `protocols/UnaryArgIndex` is the narrowing, and this is its gate.

  **The separation is what opens the arm**, and without it the check would measure
  nothing: `disjoint-problems` reads the argument's memberships only once the KB has a
  separation to test them against, so a `fresh-kb` with no declaration at all short-
  circuits before the retrieval.  One declaration, about two types the term does not
  hold, is enough — it decides nothing here and this measures the cost of deciding that.

  `check` rather than `assert`: the decision is what is being measured, and `check`
  leaves the KB identical at every reading — no sentex, no settle — so the term's
  description is the only thing n moves."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(binary_predicate pbtLikes) 'CxPerf {:strength :monotonic})
    (v/assert kb '(disjoint pbt_alpha pbt_beta) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pbtLikes 'PBTBusy (symbol (str "PBT" i)))
                  'CxPerf {:strength :monotonic})))
    (v/assert kb '(pbt_known PBTBusy) 'CxPerf {:strength :monotonic})
    (doall (for [_ (range 60)]
             (nanos (count (v/check kb '(pbt_person PBTBusy) 'CxPerf)))))))

(defn- mint-withdrawal-under-busy-term
  "A membership asserted about a term that n facts of an unrelated predicate already
  name, on a KB that prunes subsumed mints and holds one mint about another term.

  **The trigger `settle` runs on every membership it moves** with pruning on:
  `special/subsumed-mint-blocks` asks which mints the membership makes redundant.  The
  mints are read off the mint roster by term, so a term holding none costs a map lookup
  whatever else names it.  The mint about `PMWOther` keeps the roster non-empty, which is
  the gate in front of the lookup."
  [n]
  (binding [checks/*assertive-arg-types?*  true
            checks/*prune-subsumed-mints?* true]
    (let [kb (fresh-kb)]
      (v/assert kb '(genl pmw_animal thing) 'CxPerf {:strength :monotonic})
      (v/assert kb '(arg pmwOwns 1 pmw_animal) 'CxPerf {:strength :monotonic})
      (v/assert kb '(pmwOwns PMWOther PMWThing) 'CxPerf {:strength :monotonic})
      (v/with-deferred-settle kb
        (doseq [i (range n)]
          (v/assert kb (list 'pmwLikes 'PMWBusy (symbol (str "PMW" i)))
                    'CxPerf {:strength :monotonic})))
      (doall (for [i (range 60)]
               (nanos (v/assert kb (list (symbol (str "pmw_t" i)) 'PMWBusy) 'CxPerf {})))))))

(defn- settle-beside-withheld-mints
  "A fact of an unrelated predicate asserted into a KB that withholds n mints, each
  `(pwh_animal x)` drawn from `(pwhOwns x …)` while `(pwh_dog x)` says it more
  specifically.

  **The settle every write runs**, with pruning on: nothing records a withheld mint, so a
  settle that moves no membership, `genl` edge or `genlCx` edge reads nothing about the
  ones standing (`special/withheld-releases`)."
  [n]
  (binding [checks/*assertive-arg-types?*  true
            checks/*prune-subsumed-mints?* true]
    (let [kb (fresh-kb)
          m  {:strength :monotonic}]
      (v/assert kb '(genl pwh_animal thing) 'CxPerf m)
      (v/assert kb '(genl pwh_dog pwh_animal) 'CxPerf m)
      (v/assert kb '(arg pwhOwns 1 pwh_animal) 'CxPerf m)
      (v/with-deferred-settle kb
        (doseq [i (range n)
                :let [x (symbol (str "PWH" i))]]
          (v/assert kb (list 'pwh_dog x) 'CxPerf m)
          (v/assert kb (list 'pwhOwns x 'PWHThing) 'CxPerf m)))
      (doall (for [i (range 60)]
               (nanos (v/assert kb (list 'pwhLikes (symbol (str "PWHQ" i)) 'PWHThing)
                                'CxPerf {})))))))

(defn- constraint-exposure-context-edge
  "A `genlCx` edge asserted into a KB holding n facts of a declared `functional`
  predicate in the context it newly sees, under `:refuse`.

  The edge is the one trigger the tuple-mark sweep reaches *out* of the
  moved region for: visibility moved, so a pair already stored becomes jointly visible
  without either half being relabelled. Reaching out means walking the ancestor set, and an ancestor set
  is unbounded — a context cycle makes it the whole graph — so the walk is lazy and
  spends `*exposure-instance-budget*`.

  **The claim is flatness past the cap, and the cap is bound small here to reach it.**
  Below the cap the walk is proportional to the ancestor set and deliberately so: that is what
  the budget is *for*. The cap has to remain a cap — 8x the facts
  behind one edge costs the same once both sides are past it. With the budget above n, as
  the default 8192 is, the reading is the ancestor set and not the cap (5.42x at 250 →
  2000), which is the check answering a different question rather than a regression.

  Distinct subjects, so nothing in the ancestor set pairs: this measures the reach, not the
  deciding."
  [n]
  (binding [tax/*exposure-instance-budget* 100]
    (let [kb (fresh-kb)]
      (v/assert kb '(functional pbirth) 'CxPerf {:strength :monotonic})
      (v/assert kb '(genlCx CxPSrc CxPerf) 'CxPerf {:strength :monotonic})
      (v/with-deferred-settle kb
        (doseq [i (range n)]
          (v/assert kb (list 'pbirth (symbol (str "PS" i)) i) 'CxPSrc {})))
      (doall
       (for [i (range 60)]
         (nanos (v/assert kb (list 'genlCx (symbol (str "CxPW" i)) 'CxPSrc)
                          'CxPerf {:strength :monotonic})))))))

(defn- unrelated-fact-under-marked-kb-fanout
  "100 facts of a wholly unrelated, unmarked predicate, timed as they arrive in a context
  sitting below n `genlCx` readers -- with a `(functional ...)` mark declared somewhere
  else in the KB, on a predicate this fact's own predicate never touches.

  `derive-functional-equalities` sweeps `(tax/context-down tax context)` only for a fact
  whose predicate a `functional` or `functionalInArg` mark reaches:
  `special/functional-mark-relevant?` is the per-fact gate that skips the closure read
  otherwise.  Without that gate, a mark anywhere in the KB makes every assert sweep, and an
  unrelated fact measured up to 75x slower at 6400 context readers.  This check fails when
  the gate is loosened.

  The mark sits on a predicate the timed facts never mention, and the readers grow below a
  context the marked predicate never stores into: nothing here should make `context-down`
  worth reading at all, so the claim is flatness in the fanout, not merely staying under
  some bound the fanout itself would also satisfy."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(functional pFanoutMarked) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genlCx (symbol (str "CxFanR" i)) 'CxFanBase) 'CxPerf
                  {:strength :monotonic})))
    (doall
     (for [i (range 100)]
       (nanos (v/assert kb (list 'pFanoutUnrelated (symbol (str "PFU" i)) i)
                        'CxFanBase {}))))))

(defn- functional-in-arg-empty-determinant-sweep
  "100 facts arriving under a unary predicate carrying `(functionalInArg P 1)`, the empty
  determinant, where every stored tuple shares its determinant with every other, beside n
  such facts.  Each of the n facts and each of the 100 timed ones sits in its own context
  with no `genlCx` edge to anywhere, so no context sees two of them.

  The determinant is read once, when its second filler arrives, and a later tuple joins
  it with no read (`tuple/found-for`).  A member is a candidate only when a member with
  another filler sits in a context some context sees together with its own, which none
  here does, so no reader and no settle reads the n members.  The instance budget is
  bound below n, so a read of the extent capped at it would read flat too; the check
  holds the determinant read to that bound."
  [n]
  (binding [tax/*exposure-instance-budget* 100]
    (let [kb (fresh-kb)]
      (v/assert kb '(functionalInArg p_empty_det 1) 'CxPerf {:strength :monotonic})
      (v/with-deferred-settle kb
        (dotimes [i n]
          (v/assert kb (list 'p_empty_det i) (symbol (str "CxPed" i)) {})))
      (doall
       (for [i (range 100)]
         (nanos (v/assert kb (list 'p_empty_det (+ 1000000 i)) (symbol (str "CxPedT" i))
                          {})))))))

(defn- defeasible-load
  "n facts arriving through one defeasible forward rule.  The rule fires per fact and the
  conclusion is placed at `:default`; what must not happen is the whole rule set — or the
  whole KB — being rescanned to decide that."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb (list 'set/defaultRule
                       (rules/rule-sentence ['(pbird ?x)] '(pflies ?x)))
              'CxPerf {:strength :monotonic})
    (doall
     (for [i (range n)]
       (nanos (v/assert kb (list 'pbird (symbol (str "PB" i))) 'CxPerf {}))))))

(defn- taxonomy-depth
  "n `genl` edges arriving parent-before-child down one chain.  Every edge pays a `wff`
  cycle check, and what keeps that flat is the topological depth potential — a check
  walking the closure instead would be linear in the chain already built."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genl pt0_t thing) 'CxPerf {:strength :monotonic})
    (doall
     (for [i (range 1 (inc n))]
       (nanos (v/assert kb (list 'genl
                                 (symbol (str "pt" i "_t"))
                                 (symbol (str "pt" (dec i) "_t")))
                        'CxPerf {:strength :monotonic}))))))

(defn- taxonomy-belief-flip
  "One `genl` edge defeated and revived over and over, in a taxonomy of n edges.

  Every one of those settles relabels a region of exactly one handle and hands it to
  `tax/refresh-beliefs`, which has to bring the cached closure back in line.  The cost of
  that is the claim: a belief move costs what *moved*, never what the taxonomy holds.
  Two shapes break it and neither breaks a test, because both are merely slow — deciding
  which edges are active by recomputing the believed-supporter set of every edge in the
  relation, and gating that scan by walking every supporter to ask whether any moved.
  Both read as a flip that tracks the vocabulary; the fix is a reverse index off the
  moved handles, and only a load says which one is in.

  The edges are wide rather than deep (every type straight under `thing`) so the build
  stays linear and the reading is about the reconcile, not about `wff`'s cycle check —
  that is `taxonomy-depth` above, and holding both flat takes different machinery."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genl (symbol (str "pfl" i "_t")) 'thing) 'CxPerf {})))
    (let [edge (list 'not (list 'genl (symbol (str "pfl" (quot n 2) "_t")) 'thing))]
      (doall
       (for [_ (range 120)]
         (nanos (let [h (v/assert kb edge 'CxPerf {:strength :monotonic})]
                  (v/retract! kb h))))))))

(defn- flat-cache-belief-flip
  "One `(inverse P Q)` declaration defeated and revived over and over, in a KB carrying n
  `disjoint` declarations.  A `disjoint` is on the forced-monotonic roster, so no denial
  defeats one; `inverse` is not, and the same map holds both.

  The flat-cache twin of `taxonomy-belief-flip`, and the same claim on the other half of
  `tax/refresh-beliefs`: a belief move costs what *moved*, never what the KB declares.
  `:cache-support` is the one map behind all five flat caches, so its population is every
  disjoint pair, predicate property, `inverse` and declared arity in the KB together — a
  reconcile drawn over that is drawn over the vocabulary, and a corpus of OpenCyc's order
  carries tens of thousands.

  The two shapes that break it are the two the closures had, and neither breaks a test
  because both are merely slow: deciding which entries are active by evaluating belief for
  every entry in the map, and gating that scan by walking every supporter to ask whether
  any moved.  The **gate** is the one this check is really about — most settles move no
  declaration at all, so a miss that walks the whole supporter set is a cost every settle
  pays to learn it had nothing to do.  Both read as a flip that tracks the vocabulary; the
  fix is a reverse index off the moved handles, and only a load says which one is in.

  Each pair is over types of its own, so nothing is a subtype of anything and no instance
  is asserted: the reading is about the reconcile, not about `disjoint?`'s walk over two
  `genl` closures."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'disjoint (symbol (str "pfd" i "a_t")) (symbol (str "pfd" i "b_t")))
                  'CxPerf {})))
    (v/assert kb '(inverse pfdLeftOf pfdRightOf) 'CxPerf {})
    (let [decl '(not (inverse pfdLeftOf pfdRightOf))]
      (doall
       (for [_ (range 120)]
         (nanos (let [h (v/assert kb decl 'CxPerf {:strength :monotonic})]
                  (v/retract! kb h))))))))

(defn- arg-root-retrieval
  "A pattern pinning an argument that sits *after* a variable — `(pRelOf ?x Tk)`, which no
  trie prefix reaches.  The argument roots answer it by one set intersection; without them
  the whole predicate extent is scanned, so the cost would track n."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pRelOf (symbol (str "PI" i)) (symbol (str "PT" i)))
                  'CxPerf {:strength :monotonic})))
    ;; a hundred matches per reading: one is a few microseconds whatever n is, which is
    ;; the very result being gated — and a ratio between two readings that small is
    ;; timer jitter.  Batching moves the reading above the floor without changing what
    ;; it measures.
    (let [goal (list 'pRelOf '?x (symbol (str "PT" (quot n 2))))]
      (doall (for [_ (range 40)]
               (nanos (dotimes [_ 100] (doall (res/match-pattern kb goal 'CxPerf)))))))))

(def ^:private separated-types
  "Types under each side of the one declaration in `disjoint-enumeration` — the part of
  that KB the goal is actually about, held fixed while the vocabulary around it grows."
  20)

(defn- disjoint-enumeration
  "An open `(disjoint T ?t)` goal over a KB of n types in which **one** declaration
  separates two twenty-type subtrees.  The answer is twenty-one types at every n; what
  n moves is the vocabulary the goal is not about.

  A `(disjoint x y)` separates two subtrees and convicts `specs(x) × specs(y)`, and
  nothing reaches a candidate any other way — so an answer costs the answer's own size,
  and the type count is not in it.  The shape this holds flat is the other enumeration:
  one `disjoint?` per type in the KB, which on an imported ontology (docs/kbs.md) is a
  scan of 132,391 types to produce twenty-one.

  Ten asks per reading, since one is a fraction of a millisecond at any n — which is
  the result being gated, and a ratio between two readings that small is jitter."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genl pdj_left thing)  'CxPerf {:strength :monotonic})
    (v/assert kb '(genl pdj_right thing) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range separated-types)]
        (v/assert kb (list 'genl (symbol (str "pdj_l" i)) 'pdj_left)
                  'CxPerf {:strength :monotonic})
        (v/assert kb (list 'genl (symbol (str "pdj_r" i)) 'pdj_right)
                  'CxPerf {:strength :monotonic}))
      (doseq [i (range n)]
        (v/assert kb (list 'genl (symbol (str "pdj_o" i "_t")) 'thing)
                  'CxPerf {:strength :monotonic})))
    (v/assert kb '(disjoint pdj_left pdj_right) 'CxPerf {:strength :monotonic})
    (doall (for [_ (range 60)]
             (nanos (dotimes [_ 10] (count (v/ask kb '(disjoint pdj_l0 ?t) 'CxPerf))))))))

(defn- disjoint-clique-membership
  "A type membership arriving under a predicate that sits in an n-way sibling-disjoint
  clique — `(sibling_disjoint SibRoot)` with n children `genl` SibRoot, so those n
  children are mutually disjoint — where the arriving term already holds one *benign* type
  the clique does not separate.  Every such assert builds the arriving type's separation
  frame (whose sibling arm consults `specs(SibRoot)`) and tests the benign membership
  against it.

  The claim is **flatness in the clique size**.  `separation-frame` reads `specs(SibRoot)`
  once and closes over the set, and the candidate test is a `contains?` against it rather
  than a scan of the n members, so a member test costs the same against a thousand-way
  clique as against a ten-way one.  This is the assert-path twin of `disjoint-enumeration`
  (the query side) and `flat-cache-belief-flip` (the reconcile side): the shape it holds
  flat is a check that walks the whole clique per candidate, or rebuilds the frame per
  candidate over an unmemoized `specs` walk — either turns this O(clique) per assert and
  O(clique·asserts) over the load.  `checks/disjoint-problems` builds the frame once
  through `disjointness-test` for this reason.

  Distinct arriving terms, each pre-holding the same benign type, so nothing here is a
  clash and no term accumulates memberships: the reading is the cost of *deciding* a
  benign membership is admissible under a large clique, which is what every such assert
  on such a KB pays.

  Measured flat: 0.84-0.95x at 500 → 4000 clique members over three runs (the sub-1.0
  readings are the large size's JIT-warming bias `measure` documents, not a speedup).  The
  bound is the standard 2.0 the flat claims carry — about twice the worst healthy reading."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genl pdcm_benign thing) 'CxPerf {:strength :monotonic})
    (v/assert kb '(sibling_disjoint pdcm_root) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genl (symbol (str "pdcm_s" i)) 'pdcm_root)
                  'CxPerf {:strength :monotonic})))
    (doall
     (for [i (range n)
           :let [x (symbol (str "PDCM" i))]]
       (do (v/assert kb (list 'pdcm_benign x) 'CxPerf {:strength :monotonic})
           (nanos (v/assert kb (list 'pdcm_s0 x) 'CxPerf {:strength :monotonic})))))))

(defn- disjoint-metatype-membership
  "The metatype twin of `disjoint-clique-membership`: a membership arriving under a type
  that is a member of an n-member `disjoint_metatype`, the term already holding a benign
  type the metatype does not separate.  The metatype arm of `disjointness-test` scans the
  member roster (`filterv … ms`) per candidate rather than reading `contains?` off a
  memoized closure the way the sibling arm does — the members are a stored set with no
  closure to memoize — so this is the arm whose per-candidate cost tracks the member count.

  The claim is **at most linear in the member count**, not flat and not quadratic: one
  scan of the n members per candidate is the shape the arm is written to have (the comment
  at the arm says a metatype has a handful where a closure has a chain's worth), so the
  reading is expected to track n once the scan dominates.  The bound guards the step to
  quadratic — rebuilding the frame per candidate over an unmemoized member filter, or a
  member-vis probe that itself walks — which would make an assert O(members²).

  Measured linear: 4.92-5.26x at 500 -> 4000 members (the `a + b·n` shape — a ~0.07ms
  n-independent floor plus ~0.22µs a member — dilutes an 8x size step to ~5x at this
  baseline, and approaches 8x as the member scan dominates).  Bound 12.0: above the ~8x a
  larger baseline would read and well under the ~64x a per-member-quadratic regression
  would cost, the `membership-under-depth` precedent for a grows-with claim."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genl pdmt_benign thing) 'CxPerf {:strength :monotonic})
    (v/assert kb '(disjoint_metatype pdmt_meta) 'CxPerf {:strength :monotonic})
    (v/assert kb '(unary_predicate pdmt_m0) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pdmt_meta (symbol (str "pdmt_m" i))) 'CxPerf {:strength :monotonic})))
    (doall
     (for [i (range n)
           :let [x (symbol (str "PDMT" i))]]
       (do (v/assert kb (list 'pdmt_benign x) 'CxPerf {:strength :monotonic})
           (nanos (v/assert kb (list 'pdmt_m0 x) 'CxPerf {:strength :monotonic})))))))

(defn- closure-membership
  "`(pBefore Head Tail)` over an n-long chain under `(transitive pBefore)`, asked after the
  chain's closure has been asked once.

  The two questions are different and the gate is on the second.  Computing the closure is
  the length of the chain and always will be; **asking whether one pair is in a closure
  already computed is a set membership**, so it is flat in the chain — the pair asked is
  head-to-tail, the far end, which is the reading a walk cannot hold flat because a walk
  is exactly the distance between them.

  The open ask runs once, outside the timed loop: it is what fills the answer cache, and
  timing it would gate the closure's own cost instead of the membership's.  `dorun`, not a
  bare call — `ask` is lazy all the way down, so an unrealized one computes no closure and
  fills nothing.  Two hundred asks per reading, since one is microseconds at either size."
  [n]
  (let [kb (fresh-kb)
        nd #(symbol (str "PBefore" % "Individual"))]
    (v/assert kb '(transitive pBefore) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range 1 n)]
        (v/assert kb (list 'pBefore (nd (dec i)) (nd i)) 'CxPerf {:strength :monotonic})))
    (dorun (v/ask kb (list 'pBefore (nd 0) '?y) 'CxPerf))
    (let [goal (list 'pBefore (nd 0) (nd (dec n)))]
      (doall (for [_ (range 60)]
               (nanos (dotimes [_ 200] (v/ask? kb goal 'CxPerf))))))))

(defn- membership-check
  "A type membership arriving into a KB that already holds n of them, each about a
  *different* individual.  The disjointness arm reads the term's own argument-1 root
  rather than everything that mentions it, so the cost is the arriving term's own
  memberships and nothing about how many other terms have some.

  Deliberately not *one* term accumulating n types: the check must compare a new
  membership against the ones that term already holds, so that shape is linear by
  definition and gating it would be gating a claim nobody makes."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genl pm_a_t thing) 'CxPerf {:strength :monotonic})
    (v/assert kb '(genl pm_b_t thing) 'CxPerf {:strength :monotonic})
    (doall
     (for [i (range n)
           :let [x (symbol (str "PM" i))]]
       (do (v/assert kb (list 'pm_a_t x) 'CxPerf {:strength :monotonic})
           (nanos (v/assert kb (list 'pm_b_t x) 'CxPerf {:strength :monotonic})))))))

(defn- membership-under-depth
  "A type membership arriving under a predicate that sits `n` deep in a `genl` chain,
  none of the chain declaring an arity.

  The axis none of the other checks vary.  `membership-check` above holds the hierarchy
  flat and grows how many memberships the KB already holds; `taxonomy-depth` grows the
  chain but measures asserting the *edges* rather than a fact under them.  So the cost of
  the arity descension's per-super membership read — the one thing on this path that
  grows with the depth above the predicate being asserted — was invisible to all thirty
  checks, and shipped once for that reason.

  The claim is deliberately not `flat`.  `inherited-arity` asks the `variable_arity`
  release of every super-predicate; that question is a retrieval the arity table cannot
  answer, and no roster can gate it while a `variable_arity` reached through a `genl` edge
  between collections releases exactly as a directly asserted one does.  So the bound is
  a record of the shape today rather than a target, in the sense `assert-cost-test`'s
  preamble means it: a change that makes the descension flat in the depth drops this to
  about 1.0 and re-pins as an improvement, and a change that makes it worse fails."
  [n]
  (let [kb (fresh-kb)
        t  (fn [i] (symbol (str "pmud_t" i)))]
    (v/assert kb (list 'genl (t n) 'thing) 'CxPerf {:strength :monotonic})
    (doseq [i (range n)]
      (v/assert kb (list 'genl (t i) (t (inc i))) 'CxPerf {:strength :monotonic}))
    ;; warm, so the reading is the steady-state assert rather than the first one's caches
    (dotimes [i 50] (v/assert kb (list (t 0) (symbol (str "PMUDW" i))) 'CxPerf {}))
    (doall
     (for [i (range 200)]
       (nanos (v/assert kb (list (t 0) (symbol (str "PMUD" i))) 'CxPerf {}))))))

(defn- negation-arbitration
  "n **independent** P/¬P dilemmas — a fresh predicate and a fresh individual apiece, so
  no pair shares a body, a term or a context of concern with any other — and every assert
  settles against all of them.

  The twin of `clash-arbitration`, for the other nogood source.  A settle republishes the
  whole standing set either way, so the bound is Ω(standing) here too and the claim is the
  same one: the per-pair term must stay **bookkeeping** — a set union and a belief read —
  rather than re-deriving each standing pair from the store.  Re-derivation means two
  belief-filtered `query` calls and a cross product per opposed body per settle *round*,
  which is what makes a load of N dilemmas Θ(N²).

  Nothing here is a *definitional* clash, so the pairs are pure `negation-nogoods`
  business."
  [n]
  (let [kb (fresh-kb)]
    (doall
     (for [i (range n)
           :let [pr (symbol (str "pneg" i))
                 x  (symbol (str "PN" i))]]
       (do (v/assert kb (list pr x) 'CxPerf {})
           (nanos (v/assert kb (list 'not (list pr x)) 'CxPerf {})))))))

(defn- inherited-clash-arbitration
  "n standing inherited clashes, and an assert of an unrelated fact settling beside them.
  Each clash is a stored `:default` `(bigP lo2_i lo_i)` against the monotonic
  `(bigP hi_i hi2_i)`, which reaches its converse through `(genl lo_i hi_i)` and
  `(genl lo2_i hi2_i)` under `(asymmetric bigP)` and both positions preserved along `genl`.

  One context (`split?` false): everything in `CxPerf`, the edges `:default` (the
  declarations are on the forced-monotonic roster), so every clash is a standing dilemma.  Split: the stored claims in `CxPB`,
  the rest in `CxPA`, everything monotonic, so each stored claim loses at `CxPW` alone,
  and every settle empties the withdrawal cache, so `CxPW` decides every clash again.  The clashes are built
  under one deferred settle, since they are the KB this measures against.  The timed fact
  reaches none of them: a `bigP` fact in one context, and a fact of `unrelP`, which no
  declaration preserves, in the split (`checks` says why)."
  [split? n]
  (let [kb      (fresh-kb)
        M       {:strength :monotonic}
        G       (if split? M {})
        [ca cb] (if split? '[CxPA CxPB] '[CxPerf CxPerf])
        t       (fn [s i] (symbol (str s i)))]
    (doseq [[k up] (if split?
                     '[[CxPA CxUniverse] [CxPB CxUniverse] [CxPW CxPA] [CxPW CxPB]]
                     '[[CxPerf CxUniverse]])]
      (v/assert kb (list 'genlCx k up) 'CxUniverse M))
    (doseq [d '[(binary_predicate bigP) (type_relation_predicate bigP) (asymmetric bigP)
                (transitiveInArgInverse bigP 1 genl) (transitiveInArgInverse bigP 2 genl)]]
      (v/assert kb d 'CxUniverse G))
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genl (t "plo_" i) (t "phi_" i)) ca G)
        (v/assert kb (list 'genl (t "plotwo_" i) (t "phitwo_" i)) ca G)
        (v/assert kb (list 'bigP (t "plotwo_" i) (t "plo_" i)) cb {})
        (v/assert kb (list 'bigP (t "phi_" i) (t "phitwo_" i)) ca M)))
    (doall
     (for [i (range 60)]
       (nanos (v/assert kb (list (if split? 'unrelP 'bigP) (t "pu_" i) (t "pv_" i)) cb {}))))))

(defn- inherited-entry-retraction
  "n stored claims that each keep an inherited-clash entry, and a `retract!` of an
  unrelated fact settling beside them.  Each `(bigP pre_i plow)` in `CxPA` is denied by the
  `:default` reading of `(bigP phigh pre_i)` in `CxPB` through `(genl plow phigh)`, so its
  entry holds no nogood and the settle publishes nothing for it.  The retracted fact's
  handle is in the region with no record, and the discovery reads its sentence from the
  memo (`discovery/note-removed!`)."
  [n]
  (let [kb (fresh-kb)
        t  (fn [s i] (symbol (str s i)))]
    (doseq [[k up] '[[CxPA CxUniverse] [CxPB CxUniverse]]]
      (v/assert kb (list 'genlCx k up) 'CxUniverse {:strength :monotonic}))
    (doseq [d '[(binary_predicate bigP) (type_relation_predicate bigP) (asymmetric bigP)
                (transitiveInArgInverse bigP 1 genl) (genl plow phigh)]]
      (v/assert kb d 'CxUniverse {}))
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'bigP (t "pre_" i) 'plow) 'CxPA {})
        (v/assert kb (list 'bigP 'phigh (t "pre_" i)) 'CxPB {})))
    (let [hs (mapv #(v/assert kb (list 'unrelP (t "pu_" %) (t "pv_" %)) 'CxPA {}) (range 60))]
      (doall (for [h hs] (nanos (v/retract! kb h)))))))

(defn- recover-inherited-discovery
  "n stored `:default` claims `(bigP lo_i hi_i)` of a predicate preserved along `genl` at
  both positions, each argument under a chain of 60 shared types, so the product of a
  claim's two reaches (61 terms each) outnumbers the stored `bigP` extent at both sizes.
  Each reading is one `recover`, whose settle asks every claim with nothing carried,
  divided by n."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        t  (fn [s i] (symbol (str s i)))]
    (v/assert kb '(genlCx CxPA CxUniverse) 'CxUniverse M)
    (doseq [d '[(binary_predicate bigP) (type_relation_predicate bigP) (asymmetric bigP)
                (transitiveInArgInverse bigP 1 genl) (transitiveInArgInverse bigP 2 genl)]]
      (v/assert kb d 'CxUniverse M))
    (v/with-deferred-settle kb
      (doseq [j (range 60)]
        (v/assert kb (list 'genl (t "pchain_" j) (t "pchain_" (inc j))) 'CxPA M))
      (doseq [i (range n)]
        (v/assert kb (list 'genl (t "plo_" i) 'pchain_0) 'CxPA M)
        (v/assert kb (list 'genl (t "phi_" i) 'pchain_0) 'CxPA M)
        (v/assert kb (list 'bigP (t "plo_" i) (t "phi_" i)) 'CxPA {})))
    (doall (for [_ (range 3)] (quot (nanos (v/recover kb)) n)))))

(defn- recover-discovery-own-out
  "n stored `:monotonic` claims `(carryP hold_kind Bone_i)` of a predicate preserved along
  `genl`, with one denial below, and n terms each a member of two types a `disjoint`
  separates, whose `except` withdraws it at its own context, so the
  discovery reads a detached taxonomy holding it (`discovery-view`).  Each reading is one
  `recover`, divided by n."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        U  'CxUniverse
        t  (fn [s i] (symbol (str s i)))]
    (v/with-deferred-settle kb
      (doseq [d '[(binary_predicate carryP) (transitiveInArgInverse carryP 1 genl)
                  (genl hold_kind animal) (genl cartx_kind hold_kind)
                  (genl sepa_kind animal) (genl sepb_kind animal)]]
        (v/assert kb d U))
      (let [d (v/assert kb '(disjoint sepa_kind sepb_kind) U)]
        (v/assert kb (list 'except (list 'sentexHandle d)) U M))
      (doseq [i (range n)]
        (v/assert kb (list 'sepa_kind (t "Pair" i)) U M)
        (v/assert kb (list 'sepb_kind (t "Pair" i)) U M)
        (v/assert kb (list 'carryP 'hold_kind (t "Bone" i)) U M))
      (v/assert kb '(not (carryP cartx_kind Bone0)) U))
    (doall (for [_ (range 3)] (quot (nanos (v/recover kb)) n)))))

(defn- recover-discovery-separated-term
  "One term holding p types, each pair separated by a `disjoint` whose `except` withdraws
  it at its own context, so the discovery's first reader
  (`discovery-view`) decides p(p-1)/2 nogoods over p members and re-reads each once it
  withdraws the declarations.  One stored `:monotonic` claim of a predicate preserved
  along `genl`, with one denial below, makes the discovery ask.  Each reading is one
  `recover`, divided by the nogoods."
  [p]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        U  'CxUniverse
        t  (fn [s i] (symbol (str s i)))]
    (v/with-deferred-settle kb
      (doseq [d '[(binary_predicate carryP) (transitiveInArgInverse carryP 1 genl)
                  (genl hold_kind animal) (genl cartx_kind hold_kind)]]
        (v/assert kb d U))
      (v/assert kb '(carryP hold_kind Bone0) U M)
      (v/assert kb '(not (carryP cartx_kind Bone0)) U)
      (doseq [i (range p)]
        (v/assert kb (list 'genl (t "sept_kind_" i) 'animal) U)
        (v/assert kb (list (t "sept_kind_" i) 'Many) U M))
      (doseq [i (range p) j (range (inc i) p)
              :let [d (list 'disjoint (t "sept_kind_" i) (t "sept_kind_" j))]]
        (v/assert kb (list 'except (list 'sentexHandle (v/assert kb d U))) U M)))
    (doall (for [_ (range 3)] (quot (nanos (v/recover kb)) (quot (* p (dec p)) 2))))))

(defn- negation-load
  "n negative facts whose bodies are stored in ONE polarity only — the negation-heavy load
  that carries no contradiction at all.

  The complement of `negation-arbitration`, and it guards the other half of the same
  namespace.  A settle that enumerated every stored negated body looking for a believed
  positive twin would be Θ(N²) here even though not one of these bodies has a twin; the
  `:opposed` coincidence set holds exactly the doubly-stored bodies, so this pays one
  emptiness read.  The two checks fail for opposite reasons — this one if the
  *discovery* stops being incremental, its twin if the *pairing* does — and a fix aimed at
  either can regress the other, which is why both are here."
  [n]
  (let [kb (fresh-kb)]
    (doall
     (for [i (range n)]
       (nanos (v/assert kb (list 'not (list (symbol (str "pnl" i)) 'PNA))
                        'CxPerf {}))))))

(defn- compound-probe
  "`find-sentexes` on a ground **compound** — `(pcmp PI0 PTHot)`, a stored fact of a corpus
  of n over a fixed vocabulary, one of whose atoms (`PTHot`) every one of those n mentions.

  A compound earns no key of its own at the default `sx/*min-indexed-depth*` — the key
  that makes the token dictionary fact-scaled rather than vocabulary-scaled — so this read
  narrows on the atoms' postings and verifies each candidate against its record.  That is
  only a sound exchange if the narrowing is a property of the *rare* atom: `PI0` names one
  fact, so the answer is one fact, and the hot atom must not put the extent back into the
  cost.  Which is the claim `intersect-selectivity` makes about the roots, asked here of
  the read that now rests on it.

  A hundred probes per reading, since one is a few microseconds at any n and a ratio
  between two readings that small is timer jitter."
  [n]
  (let [kb (fresh-kb)]
    (v/bulk-assert-facts!
     kb (for [i (range n)] (list 'pcmp (symbol (str "PI" i)) 'PTHot)) 'CxPerf)
    (let [c (list 'pcmp 'PI0 'PTHot)]
      (doall (for [_ (range 200)]
               (nanos (dotimes [_ 100] (doall (v/find-sentexes kb c)))))))))

(def ^:private retract-victims
  "Retractions timed per run.  **The same count at both sizes**, and more than
  `tail-samples`, so each answer is the mean of the last fifty and the two windows have
  the same width.  Each victim is a separate fact, since a handle can only be retracted
  once — where an assert check re-runs one operation, this one needs a supply of them."
  60)

(defn- retract-nat-scaling
  "One `retract!` of a fact that names no NAT, on a KB carrying n **live** reified NATs.

  Every other check here times an assert or a query; this is the one that times a
  **retraction**, and the class it covers is the teardown sweep.  A retraction runs the
  reified-NAT orphan collection, because a constant whose last use has just gone would
  otherwise leave its `termOfUnit` map and materialized types dangling a raw `nat/`
  symbol (docs/nat.md).  What the sweep may cost is what the retraction *reached*; what
  it may not cost is what the KB *holds*, which is the claim measured here.

  The n NATs are all **live**: each is named by its own `(pNatUse PNUi K)` fact and no
  timed retraction touches one, so the sweep finds nothing at either size and every
  reading is the same removal doing the same work.  A population of *orphans* would
  measure the opposite thing — real removals the sweep is right to be doing, growing with
  n for a reason no fix should take away — and would read as this defect while being
  correct behaviour.

  The victims are plain binary facts of fresh individuals: nothing they name is reified,
  so nothing they leave behind can be orphaned and the population is the same at the last
  reading as at the first."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(reifiable_function PNatFn) 'CxUniverse {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pNatUse (symbol (str "PNU" i))
                           (list 'PNatFn (symbol (str "PNA" i))))
                  'CxPerf {})))
    (let [victims (mapv (fn [i]
                          (v/assert kb (list 'pRetVictim (symbol (str "PRV" i)) 'PRVal)
                                    'CxPerf {}))
                        (range retract-victims))]
      (doall (for [h victims] (nanos (v/retract! kb h)))))))

;; ---- store-level checks --------------------------------------------------
;;
;; The eight checks above drive `vaelii.core`, because the claims they defend are about
;; what an *assert* or a *query* costs.  The four below sit at the storage protocols
;; instead: each defends an operation a backend advertises as constant-time and that an
;; engine path therefore calls per firing or per query plan.  A wrong answer there is not
;; a wrong answer at all — the differential oracles prove every backend returns the same
;; sets — so nothing but a measurement can catch it, and the flat-map backend the rest of
;; the suite runs on is the one backend where each of them happens to be constant.

(def ^:private writes-per-reading
  "Index writes batched into one timed reading.  A single write is a microsecond or two —
  below `noise-floor-ns`, where a ratio is jitter — so the reading is a fixed batch of
  them, **the same batch at both sizes**, exactly as `arg-root-retrieval` times a hundred
  matches rather than one.  Small enough that the smaller size still yields more readings
  than `tail-samples` takes, or the two answers would be averages over windows of
  different width."
  50)

(def ^:private reads-per-reading
  "The same, for a root read — and an order of magnitude more of them, because a read that
  has stopped being linear is *fast*: both checks below landed at or under 20µs a batch of
  50 once fixed, which is `noise-floor-ns`, and a check that drops below the floor stops
  gating and says so rather than going quietly green.  A batch this size keeps the fixed
  reading well clear of the floor, so the check still fails if the cost comes back."
  500)

(defn- columnar-fanout
  "n sentexes on ONE predicate with n distinct first arguments, so the columnar trie's
  level-2 node ends up holding n child edges.

  What is being gated is the node's own insert, not the trie's depth: every other level
  here is width 1 (one functor, one context per argument), so the only thing that grows
  between the two sizes is the fan-out of the single node every insert passes through.  A
  per-node child structure whose insert is proportional to the children already there
  makes a load of one broad predicate — `(isa X T)`, `(genl S T)`, any hot relation in a
  real ontology — quadratic in its own extent.

  The columnar index specifically, because it is the backend built *for* 100M
  (docs/density.md): the flat-map and dense backends key a child edge in a hash and are
  flat here by construction."
  [n]
  (let [st  (columnar/columnar-index-store {:space [::fanout]})
        sxs (mapv (fn [i] (sx/sentex (list 'pfan (symbol (str "PF" i))) 'CxPerf {}))
                  (range n))]
    (p/clear-index! st)
    (doall
     (for [batch (partition-all writes-per-reading (range n))]
       (nanos (doseq [i batch] (p/index-sentex st (nth sxs i) i)))))))

(defn- exception-roster-gate
  "`exception-rule?` against a roster of n rules — the gate `chain/rule-view-of` takes
  once per candidate rule per new datum, before it will fetch a rule's exceptions.

  `p/exception-rule?` is specified as an O(1) membership test, and the firing path is
  written on the assumption: an ordinary rule is supposed to pay one set-membership read
  and nothing else.  A backend that answers it by *materializing* the roster instead turns
  every forward firing into a product of two KB-sized quantities — the rules a fact
  triggers times the rules that carry an exception.

  Measured on the `:dense` index, where the roster is a handle-set family (an
  `IntPostings`), since that is the representation the flat-map backend's plain set does
  not have and so the one where the distinction between *reading* a set and *building* one
  can be seen at all."
  [n]
  (let [st (dense/dense-index-store {:space [::roster]})]
    (p/clear-index! st)
    (doseq [i (range n)] (p/index-exception st i ['pexc]))
    (doall
     (for [r (range 200)]
       (nanos (dotimes [i reads-per-reading]
                (p/exception-rule? st (mod (+ i r) n))))))))

(defn- overlay-selectivity
  "`count-with-functor` on a fork, for a functor root of n handles the fork has never
  touched — the cardinality read `plan/order` costs every conjunct off and
  `provers/est-bindings` reads per goal.

  A fork inherits nearly all of its content: the whole point is that N processes share one
  base and each writes a little (docs/overlay.md).  So the overwhelmingly common shape of
  this read is the one measured here — a key with no overlay entry, no recorded removal
  and no tombstone, whose answer is exactly the base's own count.  Merging in order to
  count makes every query plan proportional to the extents it is costing.

  Over a `:dense` base, because that is where the base's `kv-members` builds a set rather
  than handing one back: an overlay that merges before counting is flat over a flat-map
  base and linear over that one, and only the second says whether the *code* merges."
  [n]
  (let [base (dense/dense-kv-backend {:space [::ovbase]})]
    (p/kv-clear! base)
    (doseq [i (range n)] (p/kv-add-to-set base [:functor-root 'povl] i))
    (let [own (mem/memory-kv-backend {:space [::ovfork]})
          _   (p/kv-clear! own)
          st  (kv/->KvIndexStore (okv/overlay-kv own (frozen/frozen-kv base)))]
      (doall
       (for [_ (range 200)]
         (nanos (dotimes [_ reads-per-reading] (p/count-with-functor st 'povl))))))))

(defn- intersect-selectivity
  "`sentexes-with-args` for a pattern pinning a **rare** argument beside a **hot** one
  on the same predicate — `(pint ?x PIA PIB)` with four handles at position 1 against n
  at position 2 — which is one `kv-intersect` over the two scoped argument roots,
  `[:argument-root pint 1 PIA]` ∩ `[:argument-root pint 2 PIB]`.  A single bound
  argument intersects nothing (the scoped root is one hash lookup), so two bound
  positions are the structure that exercises `kv-intersect`.

  The answer is a property of the rare side: four entries, each tested against the hot
  posting.  A backend that materializes both roots into Clojure sets before intersecting
  pays for the hot one instead, so the query becomes proportional to the extent it is
  narrowing *out of* — which is the cost the argument roots exist to avoid, and turning
  them on would buy nothing if the intersection put it back.  `arg-root-retrieval` keeps
  the same shape out of the trie path; this keeps it out of the roots.

  Over the `:dense` index, because that is where a posting has a representation to narrow
  in.  The flat-map backend hands its stored set straight back and is flat here by
  construction, so it cannot see the difference."
  [n]
  (let [b (dense/dense-kv-backend {:space [::inter]})]
    (p/kv-clear! b)
    (doseq [i (range n)] (p/kv-add-to-set b [:argument-root 'pint 2 'PIB] i))
    (doseq [i (range 4)] (p/kv-add-to-set b [:argument-root 'pint 1 'PIA] (* 7 i)))
    (let [st (kv/->KvIndexStore b)]
      (doall
       (for [_ (range 200)]
         (nanos (dotimes [_ reads-per-reading]
                  (p/sentexes-with-args st 'pint [[1 'PIA] [2 'PIB]]))))))))

(defn- plan-scaling
  "Planning one fixed four-literal conjunction against a KB of `n` facts per relation.

  The conjunction never changes, so anything that grows here is the planner reading
  something proportional to the *data* rather than to the question — and a plan is
  computed per rule expansion, per node in the node engine, and per `prove` call, so a
  planner that scales with the KB scales with it on every one of those.

  The reading this exists to hold flat is the trie's distinct-value count, which the
  cost model divides by (`plan/est-rows`, `plan/est-matches`) and therefore asks once
  per literal per plan.  `count-children` answers it off a set's cardinality or an edge
  span; `(count (children …))` would answer the same number by materializing the child
  set, which is O(how many distinct values sit at that position) and one vector per
  call.  At 32x the facts that reads 30x the planning cost, and the conjunction being
  planned is identical at both sizes — so this ratio sees it and nothing else here
  does.

  The relations are 1:1 chains beside a small disconnected one, which is the structure that
  makes the planner do all of its work: three blocks to rank, a cartesian factor to
  place, and a distinct-value count read at every literal."
  [n]
  (let [kb (fresh-kb)
        q  '[(perfPlanLoose ?u ?v) (perfPlanA ?a ?b) (perfPlanB ?b ?c) (perfPlanC ?c ?d)]]
    (v/assert-many kb
                   (concat (for [i (range n)]
                             (list 'perfPlanA (symbol (str "PpX" i)) (symbol (str "PpY" i))))
                           (for [i (range n)]
                             (list 'perfPlanB (symbol (str "PpY" i)) (symbol (str "PpZ" i))))
                           (for [i (range n)]
                             (list 'perfPlanC (symbol (str "PpZ" i)) (symbol (str "PpW" i))))
                           (for [i (range 20)]
                             (list 'perfPlanLoose (symbol (str "PpU" i)) (symbol (str "PpV" i)))))
                   'CxUniverse {:chain? false})
    (doall
     (for [_ (range 200)]
       (nanos (dotimes [_ 20] (plan/order kb q 'CxUniverse {})))))))

(defn- solve-rule-grounding
  "Grounding a recursive `set/solveRule` over a chain of `n` hops from a chosen root —
  reachability, the case a solve rule's recursion is for.  Even hops are choice edges and
  odd ones background links, so the chain continues only through both of the grounding's
  joins: a program literal matched against the atoms the round before derived, and the
  background bindings read by the variable that atom binds.

  A chain of `n` atoms is `n` semi-naive rounds of one new atom each.  A round that
  rebuilt its atom indexes, or walked every background binding rather than those its new
  atom reaches, would cost O(n), and the grounding O(n²) — 16x per atom between these
  sizes, where the indexes a round carries over read flat.  Each reading is one whole
  grounding, per thousand atoms, so it sits well above the noise floor."
  [n]
  (let [kb    (fresh-kb)
        build (var-get #'sc/build)
        nd    #(symbol (str "PsrN" %))]
    (v/assert-many kb
                   (cons (list 'perf_sr_root_cand (nd 0))
                         (for [i (range n)]
                           (list (if (even? i) 'perfSrCand 'perfSrLink) (nd i) (nd (inc i)))))
                   'CxPerf {:chain? false})
    (doseq [r '[(set/assumptionRule (implies (perf_sr_root_cand ?x) (perf_sr_root ?x)))
                (set/assumptionRule (implies (perfSrCand ?x ?y) (perfSrEdge ?x ?y)))
                (set/inertRule (set/solveRule (implies (perf_sr_root ?x) (perf_sr_reach ?x))))
                (set/inertRule (set/solveRule (implies (and (perf_sr_reach ?x) (perfSrEdge ?x ?y))
                                                       (perf_sr_reach ?y))))
                (set/inertRule (set/solveRule (implies (and (perf_sr_reach ?x) (perfSrLink ?x ?y))
                                                       (perf_sr_reach ?y))))]]
      (v/assert kb r 'CxPerf))
    (doall
     (for [_ (range 8)]
       (/ (* 1000.0 (nanos (build kb 'CxPerf))) n)))))

(defn- label-beside-unrelated-facts
  "Two choice rules and one candidate in `CxPerf` beside `n` facts no rule reads, and sixty
  groundings of the program (`solve-context/build`).  A run finds its rules off the
  `:solve-rules` roster, so a grounding reads two rules and one candidate at any `n`; a
  walk of the base's extent for the rules reads every fact there, once per rule kind."
  [n]
  (let [kb    (fresh-kb)
        build (var-get #'sc/build)]
    (v/assert-many kb
                   (cons '(perf_lb_cand PlbItem)
                         (for [i (range n)] (list 'perf_lb_noise (symbol (str "PlbX" i)))))
                   'CxPerf {:chain? false})
    (v/assert kb '(set/assumptionRule (implies (perf_lb_cand ?c) (perfLbColor ?c red))) 'CxPerf)
    (v/assert kb '(set/assumptionRule (implies (perf_lb_cand ?c) (perfLbColor ?c blue))) 'CxPerf)
    (doall (for [_ (range 60)] (nanos (build kb 'CxPerf))))))

(defn- arity-reach-trigger
  "n **conforming** facts of a predicate whose arity was declared before any of them.

  A binding recomputes the arity candidates of the functors below it when it arrives, and a
  fact of a declared predicate is no binding: `decide/note-candidate!` reads its shape in
  the candidate index, finds it tracked and no candidate, and writes nothing once the shape
  holds 64 tuples.  So an ordinary fact arriving must cost the same at 2,000 as at 250, and
  a recompute run per fact turns a linear load quadratic here and in no test.

  Conforming on purpose: a violating fact enters the candidate index and the next read
  decides it, which is `arity-binding-arrival`'s workload; what this separates is a pass
  that runs per fact from one that runs per binding."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(arity pReach 2) 'CxPerf {:strength :monotonic})
    (doall
     (for [i (range n)]
       (nanos (v/assert kb (list 'pReach (symbol (str "PR" i)) 'PRval) 'CxPerf {}))))))

(defn- feed-listener-scaling
  "n asserts on a KB with two change-feed listeners attached — one plain, one a standing
  query the arriving fact answers.

  The feed's whole cost argument is that an event is proportional to the **region a
  settle relabelled** and never to what is stored.  Two plausible implementations break
  that and neither breaks a test: snapshotting the believed set and diffing it is O(KB)
  per write, and answering a standing query by re-running its goal makes every mutation
  cost a query per listener.  Both read as a per-assert cost that grows with the load,
  which is what this separates from a per-region one.

  The listeners discard their events on purpose — what is being measured is the engine's
  cost of *producing* one, not a consumer's cost of handling it.  A standing query is
  included because it is the structure that would re-run something: it has to filter the
  region rather than ask the KB again, and only a load says which it did."
  [n]
  (let [kb (fresh-kb)]
    (v/watch kb (fn [_] nil))
    (v/watch kb '(pFeed ?x ?y) 'CxPerf (fn [_] nil))
    (doall
     (for [i (range n)]
       (nanos (v/assert kb (list 'pFeed (symbol (str "PF" i)) 'PFval) 'CxPerf {}))))))

(defn- quality-report-scaling
  "`kb-quality` over n stored facts, where n grows 8x and the **vocabulary** grows 2.8x:
  the facts pair √n individuals against √n others, so the sentex count is the square of
  the term roster.

  That shape is what separates the two implementations of the report.  Every reading it
  takes is off the vocabulary — an extent per predicate, the rule postings per predicate,
  the genl closure per type — and the one that is *easy* to write instead scans the record
  store to find the rules, which reads as O(sentexes) and grows with the square.  A
  quality report that costs what the KB costs is one nobody runs on the KB that needs it,
  and nothing but a load says which was written."
  [n]
  (let [kb   (fresh-kb)
        side (long (Math/ceil (Math/sqrt (double n))))]
    (v/assert kb '(genl qual_thing thing) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range side), j (range side)]
        (v/assert kb (list 'pQual (symbol (str "QA" i)) (symbol (str "QB" j)))
                  'CxPerf {})))
    (doall (for [_ (range 60)] (nanos (v/kb-quality kb))))))

(def ^:private census-supers
  "Predicates stacked above the one predicate `quality-declaration-census` declares
  against — the hierarchy held **fixed** while the declaration count moves, so the census's
  per-declaration arity read is a real walk at both sizes and the same walk at both."
  8)

(defn- quality-declaration-census
  "`kb-quality` over n argument constraints on **one** predicate, under a fixed hierarchy.

  The census takes seven readings and `quality-report-scaling` above drives four of them:
  its KB declares no `arg`, `genlArg` or `interArg`, so `quality/stranded-declarations`
  walks an empty list at 4,000 sentexes and at 32,000 alike, and it stores no rule, so the
  two rule-hygiene readings pair an empty set.  This is the workload that drives the
  declaration census, and it is built the other way round from that one on purpose — the
  vocabulary is one predicate, one type and `census-supers` supers at **both** sizes, so
  every other reading the census takes is fixed and the whole of the growth here is the
  declaration walk.

  Each declaration is a distinct **position** on the same predicate, which is what holds
  the vocabulary still while the count moves.  Nothing declares a length, and that is the
  expensive case rather than a degenerate one: `checks/declared-arity` answers off a map
  for a predicate carrying a length of its own and off a walk of its super-predicates for
  one that does not, so a KB that has stated no arity is the KB where every declaration
  pays the walk.  The cost is `O(declarations × super-predicates)` and this check pins the
  first factor.

  Ω(declarations) is the floor — the census reads each one, and reading them is the work —
  so the claim is linear.  What the bound separates is one reading per declaration from one
  reading per declaration *per declaration*: an arity re-derived off the index per question
  rather than off the taxonomy's table walks the argument-1 posting these n declarations
  are exactly what fills."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genl qdc_t thing) 'CxPerf {:strength :monotonic})
    (v/assert kb (list 'genl (symbol (str "qdcB" census-supers)) 'qdcTop)
              'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (v/assert kb '(genl qdcPred qdcB0) 'CxPerf {:strength :monotonic})
      (doseq [i (range census-supers)]
        (v/assert kb (list 'genl (symbol (str "qdcB" i)) (symbol (str "qdcB" (inc i))))
                  'CxPerf {:strength :monotonic}))
      (doseq [i (range 1 (inc n))]
        (v/assert kb (list 'arg 'qdcPred i 'qdc_t) 'CxPerf {:strength :monotonic})))
    (doall (for [_ (range 60)] (nanos (v/kb-quality kb))))))

(def ^:private depth-declarations
  "Argument constraints standing while `quality-declaration-depth` moves the hierarchy —
  its own knob rather than the size, because it is the factor that check holds fixed.  Big
  enough that the declaration walk is the reading: at n=256 the same KB stripped of these
  costs a tenth of what it costs with them, so nine parts in ten of what the ratio sees is
  the walk and one is the vocabulary the chain adds."
  256)

(defn- quality-declaration-depth
  "`kb-quality` over `depth-declarations` argument constraints whose predicate sits under a
  chain of n super-predicates.

  The second factor of the same bound, and the axis the check above holds still.  A
  declaration's arity read is `checks/declared-arity`, which walks the supers of a
  predicate that declares no length of its own and asks each for its own — so the census
  costs `O(declarations × super-predicates)` and neither factor alone says the product is
  right.  Nothing in the chain declares a length, so every declaration walks to the end of
  it.

  Ω(depth) is the floor, so the claim is linear here too, and it is a claim about the
  *shape* rather than about the constant: the membership read behind the walk is memoized
  for the life of one census, so a super met by the first declaration costs the other 255
  a map hit.  A change that throws that memo away pays a retrieval per super per
  declaration and this ratio cannot see it — that is `assert-cost-test`'s subject, on the
  entry point's own copy of the same walk.  What the bound separates is a walk of the supers from
  a walk of each super's own ancestry."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genl qdd_t thing) 'CxPerf {:strength :monotonic})
    (v/assert kb (list 'genl (symbol (str "qddB" n)) 'qddTop) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (v/assert kb '(genl qddPred qddB0) 'CxPerf {:strength :monotonic})
      (doseq [i (range n)]
        (v/assert kb (list 'genl (symbol (str "qddB" i)) (symbol (str "qddB" (inc i))))
                  'CxPerf {:strength :monotonic}))
      (doseq [i (range 1 (inc depth-declarations))]
        (v/assert kb (list 'arg 'qddPred i 'qdd_t) 'CxPerf {:strength :monotonic})))
    (doall (for [_ (range 20)] (nanos (v/kb-quality kb))))))

(defn- pctx [prefix i] (symbol (str "Cx" prefix i)))

(defn- store-past-checks!
  "Write `sentences` into CxUniverse of `kb`'s store the way a foreign store holds them:
  through a second KB over the same space whose taxonomy was never built, so no
  assert-time check reads what `kb` holds, then `recover` `kb` over the result.  A
  cycle-closing `genlCx` edge is refused at assert and `genlCx` is on the
  forced-monotonic roster, so no belief race forms one either: a context cycle reaches
  the taxonomy only from such a store (docs/taxonomy.md).  Answers the handles."
  [kb sentences]
  (let [raw (v/open-kb {:space 9 :recover? false})
        hs  (binding [v/*write-unrecovered?* true]
              (mapv #(v/assert raw % 'CxUniverse {}) sentences))]
    (v/recover kb)
    hs))

(defn- retract-context-cycle-scaling
  "One `retract!` of a `genlCx` edge **inside a two-context cycle**, on a KB whose
  context graph holds n unrelated contexts beside it.

  Two contexts that see each other sit in a strongly connected component, and a deletion
  inside one can split it.  A split is the only edit that invalidates the component map,
  and the map is what `sees?` reads for its O(1) same-component answer, so it may not be
  left stale.  What the repair may cost is that component; what it may not cost is the
  graph around it, which is the claim measured here.

  Each cycle is `PcB → PcA` asserted and `PcA → PcB` written past the checks
  (`store-past-checks!`), so the two contexts see each other once `kb` recovers.

  One cycle per victim, because a handle can only be retracted once and a broken cycle
  cannot be broken again.  `populate!` asserts the n unrelated contexts: by default each
  under one top context, in no cycle; `context-ring!` puts them all in one cycle, so the
  component map holds n entries the victims are not among.  No retraction names them, and
  the count is the same at the last reading as at the first."
  ([n] (retract-context-cycle-scaling
        (fn [kb n]
          (v/with-deferred-settle kb
            (doseq [i (range n)]
              (v/assert kb (list 'genlCx (pctx "PcBg" i) 'CxPcTop) 'CxUniverse {}))))
        n))
  ([populate! n]
   (let [kb (fresh-kb)]
     (populate! kb n)
     (v/with-deferred-settle kb
       (doseq [i (range retract-victims)]
         (v/assert kb (list 'genlCx (pctx "PcA" i) 'CxPcTop) 'CxUniverse {})
         (v/assert kb (list 'genlCx (pctx "PcB" i) (pctx "PcA" i)) 'CxUniverse {})))
     ;; the closing PcA → PcB edges are the timed victims; the recover builds the
     ;; component map and ranks the relation before a single reading is taken
     (let [victims (store-past-checks! kb (mapv #(list 'genlCx (pctx "PcA" %) (pctx "PcB" %))
                                                 (range retract-victims)))]
       (doall (for [h victims] (nanos (v/retract! kb h))))))))

(defn- context-ring!
  "Put n contexts `CxPr0 … CxPr(n-1)` into one `genlCx` cycle, `CxPr(i) → CxPr(i+1)` and
  `CxPr(n-1) → CxPr0`: the chain asserted, the closing edge written past the checks
  (`store-past-checks!`).  The relation then holds one component of n members."
  [kb n]
  (let [edge #(list 'genlCx (pctx "Pr" %1) (pctx "Pr" %2))]
    (v/with-deferred-settle kb
      (doseq [i (range (dec n))]
        (v/assert kb (edge i (inc i)) 'CxUniverse {})))
    (store-past-checks! kb [(edge (dec n) 0)])))

(defn- assert-context-edge-beside-cycle
  "One `assert` of a `genlCx` edge between two fresh contexts, on a KB whose context graph
  holds a cycle of n contexts the edge does not touch.

  Both endpoints are fresh, so both sit at depth 0 and the insert lifts the source above
  the target.  A lift moves the source's whole component, and the source is in none, so
  the repair's cost is one node and the n-member component beside it is not read."
  [n]
  (let [kb (fresh-kb)]
    (context-ring! kb n)
    (doall (for [i (range retract-victims)]
             (nanos (v/assert kb (list 'genlCx (pctx "PeA" i) (pctx "PeB" i))
                              'CxUniverse {}))))))

(defn- retract-merge-scaling
  "One `retract!` of a fact naming no merged term, on a KB carrying n standing `sameAs`
  merges.

  The second teardown check beside `retract-nat-scaling`, and it exists for the reason
  that one does: a settle reconciles derived state, and the population that state is
  drawn over is not a fixed small thing.  `sameAs` is one of three relations feeding the
  equality closure (docs/equality.md), `owl:sameAs` is what an RDF import emits in
  quantity, and a reconcile that re-examines every displaced spelling per settle makes
  loading n merges quadratic in n — while every other check in this file, carrying zero
  merges, reads perfectly flat with that cost in place.

  Each of the n merges displaces exactly **one** stored fact: the fact is written under
  the larger spelling and the content-keyed election puts the smaller one on top, so the
  standing displaced set is n and the KB is otherwise inert.  The victims name none of
  them — plain binary facts of fresh individuals — so no timed retraction moves the
  closure, and every reading is the same removal doing the same work."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pMergeBorn (symbol (str "PMHi" i)) 'PMPlace) 'CxPerf {})
        (v/assert kb (list 'sameAs (symbol (str "PMAa" i)) (symbol (str "PMHi" i)))
                  'CxPerf {})))
    (let [victims (mapv (fn [i]
                          (v/assert kb (list 'pMergeVictim (symbol (str "PMV" i)) 'PMVal)
                                    'CxPerf {}))
                        (range retract-victims))]
      (doall (for [h victims] (nanos (v/retract! kb h)))))))

(defn- except-merge-scaling
  "One `except` of an equality asserted and retracted, on a KB carrying n standing
  `sameAs` merges that each displace one fact.

  An `except` moves which equalities a datum's own context sees without any relabel
  saying so, and the settle's supersession reconcile has to re-examine the data it can
  change (docs/equational.md, \"An except of an equation\").  Re-examining every standing
  displaced spelling instead makes each except of a merge linear in the merges the KB
  holds.  Each victim is its own merge over its own displaced fact, disjoint from the n
  standing ones, so the reconcile the except owes is one entry at both sizes."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pMergeBorn (symbol (str "PMHi" i)) 'PMPlace) 'CxPerf {})
        (v/assert kb (list 'sameAs (symbol (str "PMAa" i)) (symbol (str "PMHi" i)))
                  'CxPerf {})))
    (let [victims (mapv (fn [i]
                          (v/assert kb (list 'pMergeBorn (symbol (str "PXHi" i)) 'PMPlace)
                                    'CxPerf {})
                          (v/assert kb (list 'sameAs (symbol (str "PXAa" i)) (symbol (str "PXHi" i)))
                                    'CxPerf {}))
                        (range retract-victims))]
      (doall (for [h victims]
               (nanos (v/retract! kb (v/assert kb (list 'except (list 'sentexHandle h)) 'CxPerf
                                               {:strength :monotonic}))))))))

(defn- irreflexive-mark-arrival
  "One `irreflexive` mark asserted, read through and retracted, over a predicate holding n
  ordinary tuples beside one `:default` self tuple.

  The mark takes the self tuple OUT with no label moving: a reader decides the nogood
  from the candidate index when it reads (docs/nmtms.md, \"Nogoods decided at the
  reader\"), so neither the arrival, its settle nor the first read at the tuple's context
  reads an ordinary tuple."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pIrrMark (symbol (str "PIM" i)) 'PIMHub) 'CxPerf {})))
    (let [self (v/assert kb '(pIrrMark PIMSelf PIMSelf) 'CxPerf {})]
      (doall (for [_ (range retract-victims)]
               (nanos (let [m (v/assert kb '(irreflexive pIrrMark) 'CxPerf {:strength :monotonic})]
                        (v/believed? kb self 'CxPerf)
                        (v/retract! kb m))))))))

(defn- verdict-window-write
  "A self tuple arriving in a context of its own under an `irreflexive` mark, beside n
  consequences of one other convicted self tuple, each stored in a context of its own.

  ```
  CxPerf  (irreflexive pvwNear) (irreflexive pvwFar)
   ├─ CxPVN  (pvwNear PVWA PVWA)
   │   └─ CxPVR0 … each  (pvwNear ?x ?x) => (pvwTag ?x PVWVi)
   └─ CxPVW0 … each timed  (pvwFar PVWFj PVWFj)
  ```

  Every context holding one of the n consequences reads it withdrawn, so each is a reader
  of the published window.  A timed tuple is one nogood read at its own context, and the
  window reads that reader again and no other (docs/nmtms.md, \"The published
  window\"); a settle that read every reader holding a withdrawable handle pays for the n
  readers here."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (v/assert kb '(irreflexive pvwNear) 'CxPerf m)
    (v/assert kb '(irreflexive pvwFar) 'CxPerf m)
    (v/assert kb '(genlCx CxPVN CxPerf) 'CxUniverse m)
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [c (symbol (str "CxPVR" i))]]
        (v/assert kb (list 'genlCx c 'CxPVN) 'CxUniverse m)
        (v/assert kb (list 'set/forwardRule
                           (list 'implies '(pvwNear ?x ?x) (list 'pvwTag '?x (symbol (str "PVWV" i)))))
                  c m))
      (doseq [j (range 60)]
        (v/assert kb (list 'genlCx (symbol (str "CxPVW" j)) 'CxPerf) 'CxUniverse m))
      (v/assert kb '(pvwNear PVWA PVWA) 'CxPVN {}))
    (v/watch kb (fn [_] nil))
    (doall
     (for [j (range 60)
           :let [x (symbol (str "PVWF" j))]]
       (nanos (v/assert kb (list 'pvwFar x x) (symbol (str "CxPVW" j)) {}))))))

(defn- membership-declaration-arrival
  "One `disjoint` declaration asserted, read through and retracted, over n individuals
  holding one type it separates and n holding the other, beside one individual holding
  both, a `:monotonic` membership and a `:default` one.

  The declaration's arrival reads no membership: the candidate index keeps only a term
  holding two memberships, and the separations are read again over the type pairs the
  kept terms hold (`membership/sync-memberships`), so neither the arrival, its settle nor the
  first read at the pair's context reads a filler (docs/nmtms.md, \"Nogoods decided at
  the reader\")."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pmda_t (symbol (str "PMDA" i))) 'CxPerf {})
        (v/assert kb (list 'pmdb_t (symbol (str "PMDB" i))) 'CxPerf {})))
    (v/assert kb '(pmda_t PMDBoth) 'CxPerf {:strength :monotonic})
    (let [weak (v/assert kb '(pmdb_t PMDBoth) 'CxPerf {})]
      (doall (for [_ (range retract-victims)]
               (nanos (let [d (v/assert kb '(disjoint pmda_t pmdb_t) 'CxPerf
                                        {:strength :monotonic})]
                        (v/believed? kb weak 'CxPerf)
                        (v/retract! kb d))))))))

(defn- decided-warm-read
  "A thousand reads of one self tuple's belief at its context, beside n `:default` self
  tuples an `irreflexive` mark convicts, after the first read at that reader.

  The first read decides every nogood the reader sees and memoizes the losers in
  `:withdrawn`, and no write follows it, so each later read is a cache hit
  (docs/nmtms.md, \"Nogoods decided at the reader\")."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(irreflexive pIrrWarm) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [x (symbol (str "PIW" i))]]
        (v/assert kb (list 'pIrrWarm x x) 'CxPerf {})))
    (let [h (v/handle-of kb '(pIrrWarm PIW0 PIW0) 'CxPerf)]
      (v/believed? kb h 'CxPerf)
      (doall (for [_ (range 200)]
               (nanos (dotimes [_ 1000] (v/believed? kb h 'CxPerf))))))))

(defn- held-shape-first-withdrawal
  "A reader's withdrawal computed with the withdrawal cache empty, over 200 `:default` self
  tuples under an `irreflexive` mark, which the reader takes OUT, beside n ternary tuples
  of a predicate bound to three arguments under one bound to two.

  The tuples' shape is an arity candidate, since a length above the functor differs, and
  the reader's binding of the functor is its own, which holds them: the reader reads the
  binding once per shape and no tuple of the shape (docs/nmtms.md, \"Nogoods decided at
  the reader\").  A reader reading every candidate tuple reads here as growth."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}]
    (v/assert kb '(genlCx CxPerfHsR CxPerf) 'CxUniverse M)
    (v/with-deferred-settle kb
      (v/assert kb '(irreflexive pHsSelf) 'CxPerf M)
      (dotimes [i 200]
        (let [x (symbol (str "PHsS" i))] (v/assert kb (list 'pHsSelf x x) 'CxPerf {})))
      (v/assert kb '(arity pHsHi 2) 'CxPerf M)
      (v/assert kb '(arity pHsLo 3) 'CxPerf M)
      (v/assert kb '(genl pHsLo pHsHi) 'CxPerf M)
      (dotimes [i n]
        (v/assert kb (list 'pHsLo (symbol (str "PHsA" i)) 'PHsB 'PHsC) 'CxPerf {})))
    (doall (for [_ (range 100)]
             (do (res/clear-withdrawn! kb)
                 (nanos (res/withdrawal kb 'CxPerfHsR)))))))

(defn- negation-reader-kb
  "A KB holding n negation pairs a reader decides: `(pnr_i PNR_i)` in `CxPNL` and its
  denial in `CxPNR`, both `:default`, which `CxPNJ` sees both of.  Built under one deferred
  settle and read once at `CxPNJ`, so the reader's decision is memoized."
  [n]
  (let [kb (fresh-kb)]
    (doseq [[c up] '[[CxPNL CxUniverse] [CxPNR CxUniverse] [CxPNJ CxPNL] [CxPNJ CxPNR]
                     [CxPNU CxUniverse]]]
      (v/assert kb (list 'genlCx c up) 'CxUniverse {:strength :monotonic}))
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [s (list (symbol (str "pnr" i)) (symbol (str "PNR" i)))]]
        (v/assert kb s 'CxPNL {})
        (v/assert kb (list 'not s) 'CxPNR {})))
    (v/believed? kb (v/handle-of kb '(pnr0 PNR0) 'CxPNL) 'CxPNJ)
    kb))

(defn- negation-reader-write
  "An assert of a fact naming nothing, in a context that sees neither side, beside n
  negation pairs a reader decides (`negation-reader-kb`).

  The settle decides none of the pairs and keeps every reader's memoized decision, since
  the fact moves no pair's member, no index entry and no stamp (docs/nmtms.md, \"Nogoods
  decided at the reader\")."
  [n]
  (let [kb (negation-reader-kb n)]
    (doall (for [i (range 60)]
             (nanos (v/assert kb (list 'pnr_unrel (symbol (str "PNU" i))) 'CxPNU {}))))))

(defn- negation-reader-warm-read
  "A thousand reads of one pair member's belief at the reader that decides it, beside n
  such pairs (`negation-reader-kb`), after the first read at that reader: each is a cache
  hit."
  [n]
  (let [kb (negation-reader-kb n)
        h  (v/handle-of kb '(pnr0 PNR0) 'CxPNL)]
    (doall (for [_ (range 200)]
             (nanos (dotimes [_ 1000] (v/believed? kb h 'CxPNJ)))))))

(defn- tuple-mark-determinant-write
  "100 ternary tuples asserted under `(functionalInArg P 3)`, each on a determinant of its
  own, `(P PTAh PTBh' v)` for hubs h and h' of ten, beside n stored tuples on n other
  determinants: half `(P PTAh PTXi i)` and half `(P PTYi PTBh i)`, so each hub's argument
  root holds n/20 tuples and neither argument of a new determinant narrows the read alone.

  A tuple reads the stored tuples of its own determinant, one trie read of `(P a b ?v)`
  (`tuple/note-tuple!`), and neither argument's posting nor the predicate's extent, so
  the write is flat in n (docs/nmtms.md, \"Nogoods decided at the reader\")."
  [n]
  (let [kb  (fresh-kb)
        hub (fn [c i] (symbol (str c (mod i 10))))]
    (v/assert kb '(functionalInArg pTripleDet 3) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (if (even? i)
                       (list 'pTripleDet (hub "PTA" (quot i 2)) (symbol (str "PTX" i)) i)
                       (list 'pTripleDet (symbol (str "PTY" i)) (hub "PTB" (quot i 2)) i))
                  'CxPerf {})))
    (doall
     (for [i (range 100)]
       (nanos (v/assert kb (list 'pTripleDet (hub "PTA" i) (hub "PTB" (quot i 10)) i)
                        'CxPerf {}))))))

(defn- tuple-mark-warm-read
  "A thousand reads of one functional pair member's belief at the reader that decides it,
  beside n such pairs: `(pTupleAge Si 1)` in `CxTML` and `(pTupleAge Si 2)` in `CxTMR`,
  both `:default`, which `CxTMJ` sees both of.  Built under one deferred settle and read
  once at `CxTMJ`, so every later read is a cache hit."
  [n]
  (let [kb (fresh-kb)]
    (doseq [[c up] '[[CxTML CxUniverse] [CxTMR CxUniverse] [CxTMJ CxTML] [CxTMJ CxTMR]]]
      (v/assert kb (list 'genlCx c up) 'CxUniverse {:strength :monotonic}))
    (v/assert kb '(functional pTupleAge) 'CxUniverse {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [x (symbol (str "PTA" i))]]
        (v/assert kb (list 'pTupleAge x 1) 'CxTML {})
        (v/assert kb (list 'pTupleAge x 2) 'CxTMR {})))
    (let [h (v/handle-of kb '(pTupleAge PTA0 1) 'CxTML)]
      (v/believed? kb h 'CxTMJ)
      (doall (for [_ (range 200)]
               (nanos (dotimes [_ 1000] (v/believed? kb h 'CxTMJ))))))))

(defn- assert-over-standing-excepts
  "One assert of a fact naming nothing, on a KB carrying n believed `(except
  (sentexHandle H))` facts, each hiding a decoy the fact does not name.

  The timed operation is an ordinary assert and its own settle, and that is the arm
  `visibility-reading` does not take: that check times a read, and this one times the
  write, whose settle keeps every reader's withdrawal the assert does not reach
  (docs/nmtms.md, \"The withdrawal cache\").  The population is built under one deferred
  settle, which settles before the first reading."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [h (v/assert kb (list 'pv_decoy (symbol (str "PVD" i))) 'CxPerf
                                {:strength :monotonic})]]
        (v/assert kb (list 'except (sx/sentex-handle h)) 'CxPerf {:strength :monotonic})))
    (doall (for [i (range 60)]
             (nanos (v/assert kb (list 'pStandVictim (symbol (str "PSV" i)) 'PSVal)
                              'CxPerf {}))))))

(def ^:private reads-after-settle
  "Reads of one withdrawal batched into one timed measurement, the same batch at both
  sizes: a cached read costs about 0.15 µs, so a hundred reads land under
  `noise-floor-ns`."
  1000)

(defn- read-after-two-pass-settle
  "The first read of a reader's withdrawal after a settle that ran two passes and wrote a
  nogood the reader decides, on a KB carrying n believed `(except (sentexHandle H))`
  facts visible from the reader, each hiding a decoy.

  Each reading's batch stores a blocker of an `exceptWhen` rule's firing, which runs a
  second pass, and a fresh asymmetric pair at the reader's own context.  The settle reads
  the reader's withdrawal after the pair's handles entered the touched window, and its
  later reconciles read the window since their own mark (`res/reconcile-withdrawn!`), so
  the timed read finds the entry the settle built.  A computed withdrawal walks the n
  excepts.  The timed operation is `reads-after-settle` reads, the first of which finds
  or computes the entry; the batch and its settle are not timed."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (v/assert kb '(binary_predicate prtRel) 'CxPerf {:strength :monotonic})
      (v/assert kb '(asymmetric prtRel) 'CxPerf {:strength :monotonic})
      (v/assert kb '(exceptWhen (prt_skip ?x)
                                (set/forwardRule (implies (prt_probe ?x) (prt_seen ?x))))
                'CxPerf)
      (doseq [i (range n)
              :let [h (v/assert kb (list 'prt_decoy (symbol (str "PRTD" i))) 'CxPerf
                                {:strength :monotonic})]]
        (v/assert kb (list 'except (sx/sentex-handle h)) 'CxPerf {:strength :monotonic})))
    (doall
     (for [i (range 60)
           :let [x (symbol (str "PRTX" i))
                 a (symbol (str "PrtA" i))
                 b (symbol (str "PrtB" i))]]
       (do (v/assert kb (list 'prt_probe x) 'CxPerf)
           (v/with-deferred-settle kb
             (v/assert kb (list 'prt_skip x) 'CxPerf)
             (v/assert kb (list 'prtRel a b) 'CxPerf)
             (v/assert kb (list 'prtRel b a) 'CxPerf))
           (let [passes (:passes (v/settle-stats kb))]
             (when-not (= 2 passes)
               (throw (ex-info "the batch's settle ran other than two passes"
                               {:passes passes :n n}))))
           (nanos (dotimes [_ reads-after-settle] (res/withdrawn-set kb 'CxPerf))))))))

(defn- assert-beside-naf-refusals
  "One assert of a fact naming nothing, on a KB whose 16 `unknown` rules hold n refused
  firings between them in the refusal record.

  Every settle pass asks the record for the lifts, the mints and the argument
  convictions waiting in it (`settle/released-lifts`, `released-mints`,
  `released-constraint-refusals`), and the KB holds none of the three: what the
  unrelated assert owes the record is nothing at both sizes.  The population is built
  under one deferred settle, with each blocking fact stored before the firing it
  refuses."
  [n]
  (let [kb    (fresh-kb)
        rules 16]
    (v/with-deferred-settle kb
      (doseq [r (range rules)
              :let [in  (symbol (str "pnrIn" r))
                    blk (symbol (str "pnrBlock" r))]]
        (v/assert kb (list 'implies (list 'and (list in '?x '?y)
                                          (list 'unknown (list blk '?x '?y)))
                           (list (symbol (str "pnrOut" r)) '?x '?y))
                  'CxPerf {:direction :forward})
        (doseq [i (range (quot n rules))
                :let [x (symbol (str "PNR" r "x" i))]]
          (v/assert kb (list blk x 'PNRVal) 'CxPerf {})
          (v/assert kb (list in x 'PNRVal) 'CxPerf {}))))
    (doall (for [i (range 60)]
             (nanos (v/assert kb (list 'pnrVictim (symbol (str "PNRV" i)) 'PNRVal)
                              'CxPerf {}))))))

(defn- released-refusal-beside-guarded-firings
  "One `retract!` of the fact an `unknown` rule's refused firing waited on, on a KB whose
  `exceptWhen` rule holds n firings.  The released firing places a sentence the exception
  reads, so the pass queues the `exceptWhen` rule for a re-check.

  The re-check is owed to the next pass, which re-decides the rule's firings against the
  queued sentence (`recheck/exception-candidates`); re-joining the rule over its n
  antecedent facts in the pass that queued it would be a second answer to the same
  question (docs/exceptions.md, \"Re-chaining what was released, not what was
  touched\")."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (v/assert kb '(exceptWhen (prr_penguin ?x) (set/forwardRule (implies (prr_bird ?x) (prr_flies ?x))))
                'CxPerf)
      (v/assert kb '(set/forwardRule (implies (and (prr_polar ?x) (unknown (prr_tropic ?x)))
                                              (prr_penguin ?x)))
                'CxPerf)
      (doseq [i (range n)]
        (v/assert kb (list 'prr_bird (symbol (str "PRB" i))) 'CxPerf)))
    (doall
     (for [i (range 60)
           :let [x (symbol (str "PRX" i))]]
       (do (v/assert kb (list 'prr_bird x) 'CxPerf)
           (v/assert kb (list 'prr_tropic x) 'CxPerf)
           (v/assert kb (list 'prr_polar x) 'CxPerf)
           (let [h (v/handle-of kb (list 'prr_tropic x) 'CxPerf)]
             (nanos (v/retract! kb h))))))))

(defn- guarded-firings-read-below
  "The first read, at a context below an `exceptWhen` rule's, of a firing placed after n
  others, where that context sees no fact the exception reads.

  The reader asks each guarded firing placed above it again (docs/naf.md, \"Evaluated
  in the placement context, not the join\"), and the firing just placed drops its
  withdrawal cache entry, so every timed read computes the reader's guard reading.  A
  firing is asked only when a binding of the exception at the reader names it, so a
  reader that sees no blocker asks none of the n."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genlCx CxPerfGR CxPerf) 'CxUniverse {:strength :monotonic})
    (v/with-deferred-settle kb
      (v/assert kb '(exceptWhen (pgr_penguin ?x) (set/forwardRule (implies (pgr_bird ?x) (pgr_flies ?x))))
                'CxPerf)
      (doseq [i (range n)]
        (v/assert kb (list 'pgr_bird (symbol (str "PGRB" i))) 'CxPerf)))
    (v/assert kb '(pgr_other PGRO) 'CxPerfGR)
    (doall
     (for [i (range 60)
           :let [x (symbol (str "PGRX" i))]]
       (do (v/assert kb (list 'pgr_bird x) 'CxPerf)
           (let [h (v/handle-of kb (list 'pgr_flies x) 'CxPerf)]
             (nanos (v/believed? kb h 'CxPerfGR))))))))

(defn- unmerge-over-standing-merges
  "One `retract!` of a `sameAs` merge that displaces one fact of its own, on a KB
  carrying n standing merges that each displace one fact.

  The un-merge moves the equality closure, so its settle gives the displaced spelling
  back.  The n standing merges are disjoint from every victim: what the retraction owes
  is its own class and its own fact at both sizes, and the reading tracks what the
  supersession reconcile walks beyond that."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pMergeBorn (symbol (str "PMHi" i)) 'PMPlace) 'CxPerf {})
        (v/assert kb (list 'sameAs (symbol (str "PMAa" i)) (symbol (str "PMHi" i)))
                  'CxPerf {})))
    (let [victims (mapv (fn [i]
                          (v/assert kb (list 'pMergeBorn (symbol (str "PXHi" i)) 'PMPlace)
                                    'CxPerf {})
                          (v/assert kb (list 'sameAs (symbol (str "PXAa" i)) (symbol (str "PXHi" i)))
                                    'CxPerf {}))
                        (range retract-victims))]
      (doall (for [h victims] (nanos (v/retract! kb h)))))))

(defn- deferred-merge-batch
  "One merging assert inside a `with-deferred-settle` batch, read at the tail of a batch of
  n merges that each displace one fact.

  The batch's touched window spans every write in it, and the write path's supersession
  reconcile examines migration's output and the classes it moved
  (`special/refresh-supersessions`).  A reconcile that read the window per merge would
  re-examine every entry the batch had displaced so far, and the k-th merge would cost
  O(k)."
  [n]
  (let [kb (fresh-kb)
        ts (volatile! [])]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pMergeBorn (symbol (str "PDHi" i)) 'PMPlace) 'CxPerf {})
        (vswap! ts conj (nanos (v/assert kb (list 'sameAs (symbol (str "PDAa" i))
                                                  (symbol (str "PDHi" i)))
                                         'CxPerf {})))))
    @ts))

(def ^:private edge-writes
  "Taxonomy edges written per run, for the same reason `retract-victims` is what it is: an
  edge handle can only be written once, so the timed operation needs a supply of distinct
  edges, and there have to be more of them than `tail-samples` takes.  **The same count at
  both sizes**, so each answer is the mean of the last fifty over windows of equal width,
  and each edge is its own fresh pair of terms — re-asserting an active edge is a no-op
  that bumps no generation and would time nothing."
  60)

(defn- genl-edge-negation-recheck
  "One `genl` edge under a fresh subtype, on a KB whose single excepted rule carries a
  **negated** conjunct and has already fired n times.

  A negated exception conjunct registers in the re-check index under the functor `not`,
  which hides the predicate it is about, so a `genl` edge cannot be keyed on it the way
  every other conjunct is.  Queueing such a rule unconditionally means one level-6
  exception query per firing it ever made, per edge written anywhere in the KB — a cost
  proportional to the rule's history rather than to the edge, and a taxonomy load
  quadratic against a KB carrying one ordinary `(exceptWhen (not …) …)`.

  The edges are the thing measured and the firings are the background: each edge's
  subtype is fresh and nothing is below it, its supertype is named by no exception, and
  the negated conjunct is about a predicate neither of them reaches.  So no edge can
  change what the rule's exception answers at either size, and what the readings differ
  by is only how many firings were re-decided anyway."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(exceptWhen (not (p_neg_skip ?x))
                              (set/defaultRule (implies (and (p_neg_probe ?x)) (p_neg_seen ?x))))
              'CxPerf {})
    (doseq [i (range n)]
      (v/assert kb (list 'p_neg_probe (symbol (str "PNG" i))) 'CxPerf {}))
    (doall (for [i (range edge-writes)]
             (nanos (v/assert kb (list 'genl (symbol (str "pnegv" i "_t")) 'pnegtop_t)
                              'CxPerf {:strength :monotonic}))))))

(defn- genl-edge-under-no-merge-mark
  "One `genl` edge above a type whose spec subtree holds n exact-arity memberships, on a
  KB declaring a `functional` and an `anti_symmetric` mark on predicates the edge does not
  reach.  Each timed edge puts the same type under a fresh supertype.

  The two merge arms (`special/equate-under-edge`, `special/antisym-equate-under-edge`)
  derive over the subtree only when a mark of their family stands over the edge's upper
  end.  An arm gated on the mark being declared anywhere reads every fact of the subtree
  per edge, and the antisymmetric one offers each back to the candidate index, where a
  membership recomputes its predicate's arity candidates.  Written unchained, so the
  reading is the two arms' alone."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (v/assert kb '(functional pgmFn) 'CxPerf m)
    (v/assert kb '(anti_symmetric pgmAnti) 'CxPerf m)
    (v/assert kb '(genl binary_predicate pgm_rel) 'CxPerf m)
    (dotimes [i n]
      (v/assert kb (list 'binary_predicate (symbol (str "pgmRel" i))) 'CxPerf m))
    (doall (for [i (range edge-writes)]
             (nanos (v/assert kb (list 'genl 'pgm_rel (symbol (str "pgm_top" i)))
                              'CxPerf {:strength :monotonic :chain? false}))))))

(defn- genl-edge-under-no-rule-above
  "One `genl` edge above a type holding n members, on a KB whose one forward rule reads a
  type the edge does not reach.  Each timed edge puts the same type under a fresh
  supertype, chained.

  `special/subsumption-seeds` puts the facts below an edge back on the chaining agenda
  only when a rule reads a term at or above the edge's upper end.  Seeding them on every
  edge sends all n to the agenda per edge, each to find no rule it newly reaches."
  [n]
  (let [kb (fresh-kb)
        m  {:strength :monotonic}]
    (v/assert kb '(set/forwardRule (implies (pgr_else ?x) (pgr_seen ?x))) 'CxPerf m)
    (dotimes [i n]
      (v/assert kb (list 'pgr_low (symbol (str "PGR" i))) 'CxPerf m))
    (doall (for [i (range edge-writes)]
             (nanos (v/assert kb (list 'genl 'pgr_low (symbol (str "pgr_top" i))) 'CxPerf m))))))

(defn- edge-stratification-walk
  "The stratification check of one `genl` edge that closes a positive cycle through a
  chain of eight rules, rule i reading `pswlink<i>_t` and concluding `pswlink<i+1>_t`, with
  n spec types under every link.  One excepted rule elsewhere keeps the check walking.

  The check is `checks/edge-stratification-violation`, which asks without writing, so
  every sample asks the same edge.  Its walk (`wff/genl-negation-cycle`) reaches the eight
  rules, and from each reads the upward closure of its consequent and the rule index under
  each predicate in it.  A walk fanning each read predicate's spec closure reads the rule
  index under every one of the n specs per rule (docs/exceptions.md, \"The search\")."
  [n]
  (let [kb    (fresh-kb)
        links (mapv #(symbol (str "pswlink" % "_t")) (range 9))]
    (doseq [t links, j (range n)]
      (v/assert kb (list 'genl (symbol (str (name t) "kind" j "_t")) t)
                'CxPerf {:strength :monotonic}))
    (doseq [[t u] (partition 2 1 links)]
      (v/assert kb (list 'implies (list 'and (list t '?x)) (list u '?x))
                'CxPerf {:direction :forward}))
    (v/assert kb '(exceptWhen (pswexc ?x)
                              (set/defaultRule (implies (and (pswbase ?x)) (pswseen ?x))))
              'CxPerf {})
    (let [edge (list 'genl (peek links) (first links))]
      (doall (for [_ (range edge-writes)]
               (nanos (checks/edge-stratification-violation kb edge)))))))

(defn- edge-stratification-unreached
  "One `genl` edge under `psutop_t`, on a KB holding n excepted rules the edge does not
  reach.

  Eight rules read `psutop_t` and conclude predicates no rule reads.  Eight spokes sit
  under `psuhub_t`, eight rules read the hub and conclude a spoke each, and the n excepted
  rules read the hub too.  The timed edge puts a fresh subtype under `psutop_t`: its
  stratification walk (`wff/genl-negation-cycle`) starts at the eight readers of
  `psutop_t` and reaches nothing else, whatever n is.  A walk from every excepted rule
  expands n + 8 rules per start, n times over."
  [n]
  (let [kb     (fresh-kb)
        spokes (mapv #(symbol (str "psuspoke" % "_t")) (range 8))]
    (doseq [[i t] (map-indexed vector spokes)]
      (v/assert kb (list 'genl t 'psuhub_t) 'CxPerf {:strength :monotonic})
      (v/assert kb (list 'implies (list 'and (list 'psuhub_t '?x)) (list t '?x))
                'CxPerf {:direction :forward})
      (v/assert kb (list 'implies (list 'and (list 'psutop_t '?x))
                         (list (symbol (str "psuout" i "_t")) '?x))
                'CxPerf {:direction :forward}))
    (doseq [i (range n)]
      (v/assert kb (list 'exceptWhen (list (symbol (str "psuexc" i "_t")) '?x)
                         (list 'set/defaultRule
                               (list 'implies (list 'and (list 'psuhub_t '?x))
                                     (list (symbol (str "psuseen" i "_t")) '?x))))
                'CxPerf {}))
    (doall (for [i (range edge-writes)]
             (nanos (v/assert kb (list 'genl (symbol (str "psusub" i "_t")) 'psutop_t)
                              'CxPerf {:strength :monotonic}))))))

(defn- taxonomy-edge-arbitration
  "One `genl` edge — a fresh subtype under a fresh supertype, with nothing above it,
  nothing below it and no separation anywhere near it — written on a KB carrying n
  standing definitional dilemmas.

  `clash-arbitration` builds that standing set and then never writes a taxonomy edge, so
  the whole of its run reads one clash vocabulary and the memo's staleness test is never
  asked a question.  This is the workload that asks it.  Every edge activation bumps the
  relation's generation, and a memo retired on that generation abandons its whole carry
  per edge: two `checks/arbitrable-violations` calls per standing pair, on a KB where the
  edge separates nothing and reaches no instance.

  Ω(standing) is the floor here as it is there — a settle republishes the whole standing
  clash set either way — so the bound is the same claim in the same shape: the per-pair
  term must stay bookkeeping rather than a re-derivation of the checks.

  The KB also carries a `sibling_disjoint` mark with nothing under it.  A sibling
  separation reads the `genl` edges between two supertypes, and a memo that re-derived
  every standing pair while such a mark stands would read the retired-memo shape here.

  The dilemmas are built under one deferred settle: the standing set is the KB this
  measures against and not the thing being measured, and building it an assert at a time
  is the Ω(standing)-per-settle cost paid n times over."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(disjoint pea_t peb_t) 'CxPerf {:strength :monotonic})
    (v/assert kb '(sibling_disjoint pesib_t) 'CxPerf {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [x (symbol (str "PEX" i))]]
        (v/assert kb (list 'pea_t x) 'CxPerf {})
        (v/assert kb (list 'peb_t x) 'CxPerf {})))
    (doall
     (for [i (range edge-writes)]
       (nanos (v/assert kb (list 'genl (symbol (str "pev" i "_t"))
                                 (symbol (str "peu" i "_t")))
                        'CxPerf {:strength :monotonic}))))))

(defn- arity-binding-arrival
  "One `binary_predicate` membership asserted, read through and retracted, over a
  predicate holding n binary tuples beside one `:default` ternary tuple.

  The membership takes the ternary tuple OUT with no label moving: the arrival recomputes
  the candidate shapes of the predicate from the tracked shapes, and a reader decides the
  one-member nogood from the candidate index when it reads (docs/nmtms.md, \"Nogoods
  decided at the reader\"), so neither the arrival, its settle nor the first read at the
  tuple's context reads a binary tuple."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pArrBind (symbol (str "PAB" i)) 'PABHub) 'CxPerf {})))
    (let [long-tuple (v/assert kb '(pArrBind PABx PABy PABz) 'CxPerf {})]
      (doall (for [_ (range retract-victims)]
               (nanos (let [m (v/assert kb '(binary_predicate pArrBind) 'CxPerf {:strength :monotonic})]
                        (v/believed? kb long-tuple 'CxPerf)
                        (v/retract! kb m))))))))

(defn- bound-type-load
  "n types in eight levels under one root, each below three types of the level above,
  then every type bound to one argument, the bottom level first, each binding timed.

  A length arriving at a type reaches only the types below it that do not already hold
  it (docs/nmtms.md, \"Nogoods decided at the reader\").  Bottom level first makes the
  last bindings the top level's, whose subtypes are most of the load and all bound
  already, so the readings are what an arrival costs where nothing below it moves: the
  walk stops at each child.  A recompute of every subtype per binding reads here as
  growth with the load."
  [n]
  (let [kb     (fresh-kb)
        levels 8
        width  (max 1 (quot n levels))
        rnd    (java.util.Random. 57)
        ty     (fn [l i] (symbol (str "btl" l "i" i "_t")))]
    (v/with-deferred-settle kb
      (doseq [l (range levels), i (range width)]
        (if (zero? l)
          (v/assert kb (list 'genl (ty 0 i) 'btroot_t) 'CxPerf {})
          (dotimes [_ 3]
            (v/assert kb (list 'genl (ty l i) (ty (dec l) (.nextInt rnd width))) 'CxPerf {})))))
    (doall
     (for [l (range (dec levels) -1 -1), i (range width)]
       (nanos (v/assert kb (list 'arity (ty l i) 1) 'CxPerf {:strength :monotonic}))))))

(defn- declaration-rebuild
  "n types in a chain under `thing`, one `arg` declaration naming each, then
  `special/rebuild-pending!` timed whole and read per hundred declarations (one is
  under the noise floor).

  The rebuild answers whether a declared type reaches `thing` from one walk down from
  `thing` (`checks/mintable-types`), so a declaration costs a record read and a set
  lookup.  A walk up from each declaration's type costs its position in the chain, and
  reads here as growth with n."
  [n]
  (let [kb (fresh-kb)
        ty (fn [i] (symbol (str "pdr" i "_t")))]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genl (ty i) (if (zero? i) 'thing (ty (dec i)))) 'CxPerf
                  {:strength :monotonic})
        (v/assert kb (list 'arg (symbol (str "pdrRel" i)) 1 (ty i)) 'CxPerf
                  {:strength :monotonic})))
    (doall (for [_ (range 4)]
             (/ (nanos (special/rebuild-pending! kb)) (/ n 100.0))))))

(defn- mint-release-after-genl-move
  "n types in a chain with no path to `thing`, one `arg` declaration naming each, so n
  declarations wait on a mintable type; then a `genl` edge between two other types, timed
  through the settle that re-asks every waiting declaration, read per hundred
  declarations.

  The settle answers each declaration from one walk down from `thing`
  (`checks/mintable-types`).  A walk up from each declaration's type costs its position
  in the chain, and reads here as growth with n."
  [n]
  (let [kb (fresh-kb)
        ty (fn [i] (symbol (str "pmr" i "_t")))]
    (v/with-deferred-settle kb
      ;; `thing` a node, so a walk up from the chain is not refused on depth alone
      (v/assert kb '(genl pmr_anchor_t thing) 'CxPerf {:strength :monotonic})
      (doseq [i (range n)]
        (when (pos? i)
          (v/assert kb (list 'genl (ty i) (ty (dec i))) 'CxPerf {:strength :monotonic}))
        (v/assert kb (list 'arg (symbol (str "pmrRel" i)) 1 (ty i)) 'CxPerf
                  {:strength :monotonic})))
    (doall (for [k (range 4)]
             (/ (nanos (v/assert kb (list 'genl (symbol (str "pmr_sub" k "_t"))
                                          (symbol (str "pmr_top" k "_t")))
                                 'CxPerf {:strength :monotonic}))
                (/ n 100.0))))))

(def ^:private lift-rebuild-facts
  "The facts of a decontextualized predicate `lift-rebuild` states in its deepest context."
  2000)

(defn- lift-rebuild
  "A chain of n contexts under CxPerf, an `except` of the chain's first `genlCx` edge from
  a side context (so a scoped `sees?` reads each edge supporter's visibility), and
  `lift-rebuild-facts` facts of a decontextualized predicate stated in the deepest
  context; then `special/rebuild-pending!` timed whole and read per hundred facts.

  The lift walk asks whether a stating context sees CxUniverse once per context
  (`special/lift-statements`).  Asking it per fact walks the chain per fact, and reads
  here as growth with n."
  [n]
  (let [kb (fresh-kb)
        cx (fn [i] (symbol (str "CxPlr" i)))]
    (v/with-deferred-settle kb
      (v/assert kb '(genlCx CxPerf CxUniverse) 'CxUniverse {:strength :monotonic})
      (v/assert kb '(genlCx CxPlrSide CxPerf) 'CxUniverse {:strength :monotonic})
      (v/assert kb '(decontextualized_predicate pLiftRebuild) 'CxUniverse {:strength :monotonic})
      (doseq [i (range 1 (inc n))]
        (let [h (v/assert kb (list 'genlCx (cx i) (if (= 1 i) 'CxPerf (cx (dec i))))
                          'CxUniverse {:strength :monotonic})]
          (when (= 1 i)
            (v/assert kb (list 'except (list 'sentexHandle h)) 'CxPlrSide
                      {:strength :monotonic}))))
      (doseq [j (range lift-rebuild-facts)]
        (v/assert kb (list 'pLiftRebuild (symbol (str "PLR" j)) 'PLRHub) (cx n) {})))
    (doall (for [_ (range 4)]
             (/ (nanos (special/rebuild-pending! kb)) (/ lift-rebuild-facts 100.0))))))

(defn- constraint-genl-edge
  "A `genl` edge flipped in and out of belief above a predicate holding n facts, on a KB
  declaring `functional` — either **on** the predicate above the edge or on one the edge
  cannot reach.  `budget` is what `*exposure-instance-budget*` is bound to.

  The cross-context constraint report reaches out of the moved region for two edges, and
  this is the second of them: a `functional` or `asymmetric` mark standing on a
  super-predicate descends a new `(genl sub super)` edge to a subtree that never carried
  one, so a pair of `sub` facts either side of a visibility edge starts clashing without
  any context moving.  What that implicates is the subtree's facts, and `genl` is the
  commonest edge an ontology writes — so the arm is gated on a mark actually being at or
  above `sub`, which costs a `props-over` read on an edge under nothing marked.

  The flip is what isolates the settle's own reading.  A `genl` edge on the way *in* also
  walks the same subtree at `special/equate-under-edge` under the mark, so an edge
  written once measures both passes and can separate neither; a
  revival puts the edge back in the moved region without going through that path, and the
  reading is the settle's two budgeted walks: the constraint pass and the merge sweep a
  revived edge under a mark runs (`special/revived-edge-sweep`).  The mark is declared either way, so the report's
  vocabulary gate is open in both shapes and the only difference is the one being measured.
  The predicates are spelled bare lowercase, which `checks/forced-monotonic?` takes as a
  type spelling, so the edge is not a `genl` between predicates, which the forced-monotonic
  roster holds and no denial defeats (docs/nmtms.md)."
  [marked? budget]
  (fn [n]
    (binding [tax/*exposure-instance-budget* budget]
      (let [kb (fresh-kb)]
        (v/assert kb (list 'functional (if marked? 'pcegtop 'pcegelse))
                  'CxPerf {:strength :monotonic})
        (v/with-deferred-settle kb
          (v/assert kb '(genl pcegmid pcegtop) 'CxPerf {})
          (v/assert kb '(genl pcegsub pcegmid) 'CxPerf {})
          (doseq [i (range n)]
            (v/assert kb (list 'pcegsub (symbol (str "PCEG" i)) 'PCEGval) 'CxPerf {})))
        (let [edge '(not (genl pcegmid pcegtop))]
          (doall
           (for [_ (range edge-writes)]
             (nanos (let [h (v/assert kb edge 'CxPerf {:strength :monotonic})]
                      (v/retract! kb h))))))))))

(defn- context-edge-arbitration
  "One `genlCx` edge — a fresh context under `CxUniverse`, with nothing below
  it — written on a KB carrying n standing P/¬P dilemmas, every one of them stated in a
  context the edge does not reach.

  The negation twin of the check above, and the same blind spot in the same place:
  `negation-arbitration` builds its standing set and writes no context edge afterwards.
  Joint visibility is read through the `genlCx` closure, so a memo retired on that
  relation's generation re-derives every opposed body per edge — two belief-filtered
  reads and a cross product apiece — for an edge no contradiction in the KB is stated
  anywhere near.

  No separation anywhere, so the clash memo short-circuits and this is the negation
  pairing alone."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [pr (symbol (str "pceg" i))
                    x  (symbol (str "PCE" i))]]
        (v/assert kb (list pr x) 'CxPerf {})
        (v/assert kb (list 'not (list pr x)) 'CxPerf {})))
    (doall
     (for [i (range edge-writes)]
       (nanos (v/assert kb (list 'genlCx (symbol (str "CxPCtx" i))
                                 'CxUniverse)
                        'CxPerf {:strength :monotonic}))))))

(def ^:private reads-per-visibility-reading
  "Reads batched into one timed measurement, the same batch at both sizes so it cancels
  out of the ratio — `reads-per-clash-reading`'s idiom, for its reason."
  20)

(defn- visibility-reading
  "A scoped read on a KB carrying n believed `(except (sentexHandle H))` facts, all
  visible from the reading context.

  The claim is that the read costs **what it returns**, not what the KB hides. Every
  scoped retrieval filters by visibility removal (`res/without-excepted`), and the answer
  that filter needs is *which handles are hidden from here* — a question whose intended
  shape is a lookup per match and whose lazy shape is a walk over every `except` in the
  KB, per call. The excepts here hide **decoys** the read never returns, so n moves the
  filter's input while leaving its output alone, and a reading that grows with n is the
  filter re-deriving what the store already knows.

  **The literal cache is bound off**, and that is the point rather than a distortion.
  A repeat read under an unmoved clock is served whole from `literal-cache`, so leaving
  it on would measure the cache and report the filter as free at both sizes. The caller
  this check exists for is forward chaining, which moves the clock per placement and so
  meets this read cold every time (`literal-cache/lookup` states that directly).

  Built under one deferred settle: the excepts are the KB this measures against, not the
  thing measured."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [h (v/assert kb (list 'pv_decoy (symbol (str "PVD" i))) 'CxPerf
                                {:strength :monotonic})]]
        (v/assert kb (list 'except (sx/sentex-handle h)) 'CxPerf
                  {:strength :monotonic})))
    (v/assert kb '(pv_seen PVOne) 'CxPerf {:strength :monotonic})
    (binding [lc/*enabled* false]
      (doall
       (for [_ (range 60)]
         (nanos (dotimes [_ reads-per-visibility-reading]
                  (count (v/sentexes-matching kb '(pv_seen ?x) 'CxPerf)))))))))

(def ^:private readings-per-reader-fan
  "Timed readings.  Above `tail-samples`, so the answer is a mean over the last 50 and the
  first reading — the only one that still has merges to derive — is outside it."
  60)

(defn- genlcx-edge-reader-fan
  "One `(genlCx sub super)` edge joining two branches of a KB carrying n **bystander**
  reader contexts — contexts that read the candidates' own branch and sit under no `sub`,
  so the edge leaves every one of their ancestor sets exactly as it found them.

  The claim is that the edge costs the readers it **widened**.  When the edge lands,
  `special/equate-under-context-edge` re-derives the functional equalities over the facts
  the widened ancestor set newly exposes, and each derivation sweeps a set of reader
  contexts: the required set is `context-down(sub)`, which here is `sub` alone, and the lazy
  one is every reader below each candidate's own storage context, which every bystander
  is.  So n moves the reader fan and leaves the widened set and the candidate set alone,
  and an edge that grows with n is the sweep re-asking readers a question already answered
  when the fact arrived.

  **This is the growth that shipped**: as the starter grew from 1,668 to 2,435 sentexes
  one edge over it went from 23 ms to 145 ms and `starter/load-into` from 0.87 s to
  2.50 s.  `genlcx_sweep_cost_test` counts the same fan in the suite; this reads it as a
  duration, which is what also catches a per-call cost growing inside a fan of the right
  size.

  **One `sub` exists at a time, and the reading retracts its own edge.**  That is what
  keeps the baseline out of the measurement, and getting it wrong once is why it is
  written down: a `sub` per reading has to be wired somewhere it can see the candidates,
  which makes each one a bystander of every later reading — 60 of them, so the n=8 fan is
  really 68 and the n=512 fan 572, and a ratio the sweep should have made ~57x reads
  2.0x.  That is the header's own warning about a baseline that already carries the cost,
  met in the setup rather than in the sizes.  Retracting the joining edge leaves the merge
  standing (`equate-under-context-edge` says why), so every reading after the first pays
  the sweep and not the merge — which is the fan, and is the quantity this is about."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(functional gefParent) 'CxUniverse {:strength :monotonic})
    (v/assert kb '(genlCx CxGefLeft CxUniverse) 'CxCore {:strength :monotonic})
    (v/assert kb '(genlCx CxGefRight CxUniverse) 'CxCore {:strength :monotonic})
    (v/with-deferred-settle kb
      ;; readers of the candidates' branch, under no `sub`: the joining edge changes no
      ;; ancestor set of theirs, so none of them is entitled to cost it anything
      (doseq [i (range n)]
        (v/assert kb (list 'genlCx (symbol (str "CxGefBy" i)) 'CxGefLeft) 'CxCore
                  {:strength :monotonic}))
      ;; the one sub, and the clashing pairs the sweep enumerates
      (v/assert kb '(genlCx CxGefSub CxGefLeft) 'CxCore {:strength :monotonic})
      (doseq [i (range 8)]
        (v/assert kb (list 'gefParent (symbol (str "GefK" i)) (symbol (str "GefA" i)))
                  'CxGefLeft {:strength :monotonic})
        (v/assert kb (list 'gefParent (symbol (str "GefK" i)) (symbol (str "GefB" i)))
                  'CxGefRight {:strength :monotonic})))
    (doall
     (for [_ (range readings-per-reader-fan)]
       (let [t (nanos (v/assert kb '(genlCx CxGefSub CxGefRight) 'CxCore
                                {:strength :monotonic}))]
         (v/retract! kb (v/handle-of kb '(genlCx CxGefSub CxGefRight) 'CxCore))
         t)))))

(def ^:private reads-per-clash-reading
  "Readings of the standing set batched into one timed measurement, and **the same batch
  at both sizes**, so it cancels out of the ratio.  A single read at the small size lands
  around `noise-floor-ns`, where a ratio is jitter; a fixed batch is what lifts the
  measurement clear of the floor without changing what it measures, exactly as
  `arg-root-retrieval` times a hundred matches rather than one."
  10)

(defn- standing-clash-reading
  "`core/contradictions` on a KB carrying n standing P/¬P dilemmas — the **read** side of
  the standing set whose write side `negation-arbitration` measures, over the same KB
  shape.

  A reading is `clashes/ranked` over what `clashes/read-clashes` answers.  Those vectors
  are in the order the candidate index answers in, so putting them in content order is
  what makes `(first (contradictions kb))` an answer about the knowledge rather than about
  which pair was typed first — and it is done at the read because a KB is written to far
  more often than it is read.  That moves the cost onto a path with no other check on it,
  which is what this is.

  `contradictions` rather than `conflicts` because a default/default pair is a dilemma;
  the two are one call, and `core/preview`'s standing filter is a third caller of it.

  The dilemmas are built under one deferred settle: they are the KB this measures
  against, not the thing being measured, and building them an assert at a time is the
  Ω(standing)-per-settle cost `negation-arbitration` is for."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [pr (symbol (str "pread" i))
                    x  (symbol (str "PRD" i))]]
        (v/assert kb (list pr x) 'CxPerf {})
        (v/assert kb (list 'not (list pr x)) 'CxPerf {})))
    (doall
     (for [_ (range 60)]
       (nanos (dotimes [_ reads-per-clash-reading]
                (count (v/contradictions kb))))))))

(def ^:private inherit-chain-depth
  "How far above the claim-holders the preserved relation runs, so that **one reach walk
  is a real cost** rather than a lookup: `fact-reach` reads the store once per node it
  walks, and a reach thirty-three nodes long is what puts the walking above the comparing
  in the reading below.  With a one-node reach the cross-product would dominate at both
  sizes and the check would read the same number whether the memo was there or not."
  32)

(defn- inherit-reach-memo
  "`ask?` on a preserved goal about a term that n incomparable claims reach, each of them
  holding a reach thirty-two hops long.

  `undercut?` compares every claim against every other and each comparison asks for a
  claim's reach, so the **walks** are quadratic in the claims unless something remembers
  them.  `inherit/*memo*` is what does, for the length of one question: n distinct reaches
  are walked once each, and the n² comparisons that follow are set lookups.  So the cost
  is the walking — linear in the claims — plus a cross-product that stays cheap, and 8x
  the claims must land near 8x rather than near the 64x a lost memo reads.

  The counted companion is `inherit_test/the-reach-walk-is-linear-in-the-claims-and-not
  -quadratic`, which reads the same claim off `matches-visible` call counts rather than off
  a clock, and can see it at any depth."
  [n]
  (let [kb    (fresh-kb)
        base  'PiPart
        above (mapv #(symbol (str "PiAbove" %)) (range inherit-chain-depth))]
    (v/with-deferred-settle kb
      (v/assert kb '(transitive piPartOf) 'CxPerf {:strength :monotonic})
      (v/assert kb '(transitiveInArgInverse pi_needs_work 1 piPartOf) 'CxPerf {:strength :monotonic})
      ;; the shared chain every claim-holder's reach runs up
      (doseq [[a b] (partition 2 1 above)]
        (v/assert kb (list 'piPartOf a b) 'CxPerf {}))
      (doseq [i (range n)
              :let [o (symbol (str "PiWhole" i))]]
        (v/assert kb (list 'piPartOf base o) 'CxPerf {})
        (v/assert kb (list 'piPartOf o (first above)) 'CxPerf {})
        (v/assert kb (list 'pi_needs_work o) 'CxPerf {})))
    (let [goal (list 'pi_needs_work base)]
      (doall (for [_ (range 60)]
               (nanos (v/ask? kb goal 'CxPerf)))))))

(defn- witness-route-search
  "One preservation support for a goal whose claim is reached by n **alternative routes**
  between the same two terms.

  The support names the routes no other route covers, and which ones decide where a
  firing over the claim is placed, so the search keeps the routes stated in the most
  general contexts (`taxonomy/general-reach-supports`).  A search that answered that by enumerating
  the routes and comparing them would be quadratic in n; the walk that ships settles each
  node once and reads each edge once, so 8x the routes is near 8x the search and nowhere
  near 64x.

  Every route is two hops through its own middle term and every edge is asserted in one
  context, so the routes tie on generality and the search is doing the work the bound is
  about rather than short-circuiting on the first general route it sees."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (v/assert kb '(transitiveInArgInverse pwNeeds 1 genl) 'CxPerf {:strength :monotonic})
      (v/assert kb '(pwNeeds pw_dog PwVal) 'CxPerf {})
      (doseq [i (range n)
              :let [m (symbol (str "pw_mid" i))]]
        (v/assert kb (list 'genl 'pw_chi m) 'CxPerf {})
        (v/assert kb (list 'genl m 'pw_dog) 'CxPerf {})))
    (let [goal '(pwNeeds pw_chi PwVal)]
      (doall (for [_ (range 60)]
               (nanos (inherit/solve-with-support kb goal 'CxPerf)))))))

(defn- lost-firing-scan
  "The settle's scan for firings a reader below a scoped defeat reads as withdrawn while it
  still reaches over a second route (`reroute/lost-firing-seeds`), on a KB holding n
  standing scoped defeats every one of which that scan has already re-derived.

  Each chain is two routes between `pl_c<i>` and `pl_a<i>` — a long one in CxPerf, a short
  one in CxPerfShort below it — a preserved claim fired over the long one, and a monotonic
  denial of a long-route edge in CxPerfShort.  The scan runs on every settle pass while a
  scoped defeat stands, and here it finds each withdrawn firing already believed through
  the one it re-derived, so what it costs is the reading: one withdrawal per reader below
  a vantage and one check per withdrawn firing, linear in n.  The withdrawal cache is
  emptied before each reading, as a settle pass that moves a reader's entry empties it,
  so each reading scans every reader again."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genlCx CxPerfShort CxPerf) 'CxUniverse {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [t  #(symbol (str "pl_" % i))
                    pr (symbol (str "plRel" i))]]
        (doseq [x [(t "a") (t "b") (t "c")]] (v/assert kb (list 'genl x 'thing) 'CxPerf {}))
        (v/assert kb (list 'genl (t "b") (t "a")) 'CxPerf {})
        (v/assert kb (list 'genl (t "c") (t "b")) 'CxPerf {})
        (v/assert kb (list 'genl (t "c") (t "a")) 'CxPerfShort {})
        (v/assert kb (list 'transitiveInArgInverse pr 1 'genl) 'CxPerf {:strength :monotonic})
        (v/assert kb (list pr (t "a") 'PlVal) 'CxPerf {})
        (v/assert kb (list 'set/forwardRule (list 'implies (list pr '?x '?y) (list 'plNoted '?x '?y)))
                  'CxPerf {})))
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'not (list 'genl (symbol (str "pl_c" i)) (symbol (str "pl_b" i))))
                  'CxPerfShort {:strength :monotonic})))
    (doall (for [_ (range 60)]
             (do (res/clear-withdrawn! kb)
                 (nanos (reroute/lost-firing-seeds kb #{} (delay #{}))))))))

(defn- genl-defeat-rejoin
  "One arriving `(not (genl …))`'s own chaining, on a KB holding n predicates each preserved
  along `genl` with a claim and a forward rule over it, and one chain of types per
  predicate that no other predicate's claim reaches.

  Every declaration here preserves along the same relation, so a `genl` edge that
  re-joined each of their rules made the arrival linear in n and n arrivals quadratic.
  `inherit/crossing-claim?` keeps the predicate whose claim sits on the edge's chain.
  Timed inside a deferred block, so each sample is the arrival's chaining and none of it
  is a settle; the narrowing reads the slot roster once per term of the edge's four-term
  closure."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [t  #(symbol (str "gd_" % i))
                    pr (symbol (str "gdRel" i))]]
        (doseq [x [(t "a") (t "b") (t "c")]] (v/assert kb (list 'genl x 'thing) 'CxPerf {}))
        (v/assert kb (list 'genl (t "b") (t "a")) 'CxPerf {})
        (v/assert kb (list 'genl (t "c") (t "b")) 'CxPerf {})
        (v/assert kb (list 'transitiveInArgInverse pr 1 'genl) 'CxPerf {:strength :monotonic})
        (v/assert kb (list pr (t "a") 'thing) 'CxPerf {})
        (v/assert kb (list 'set/forwardRule (list 'implies (list pr '?x '?y) (list 'gdNoted '?x '?y)))
                  'CxPerf {})))
    (let [samples (volatile! [])]
      (v/with-deferred-settle kb
        (doseq [i (range n)]
          (vswap! samples conj
                  (nanos (v/assert kb (list 'not (list 'genl (symbol (str "gd_c" i)) (symbol (str "gd_b" i))))
                                   'CxPerf {:strength :monotonic})))))
      @samples)))

(defn- genl-crossing-many
  "The narrowing one `genl` denial pays, on the `genl-defeat-rejoin` corpus with n
  predicates preserved along `genl`: a batch of `inherit/moved-predicates` calls, the
  same batch at both sizes, each on a denial of a different chain's edge.

  `genl-defeat-rejoin` times whole arrivals, where the re-join dominates at its sizes;
  this times the selection alone at sizes where it would dominate.  An arrival asks it
  once from the chainer and once from the re-check triggers, and the settle asks it again
  per region member.  The narrowing reads the slot roster once per closure term and looks
  the declarations up by relation, so nothing here grows with n."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)
              :let [t  #(symbol (str "gm_" % i))
                    pr (symbol (str "gmRel" i))]]
        (doseq [x [(t "a") (t "b") (t "c")]] (v/assert kb (list 'genl x 'thing) 'CxPerf {}))
        (v/assert kb (list 'genl (t "b") (t "a")) 'CxPerf {})
        (v/assert kb (list 'genl (t "c") (t "b")) 'CxPerf {})
        (v/assert kb (list 'transitiveInArgInverse pr 1 'genl) 'CxPerf {:strength :monotonic})
        (v/assert kb (list pr (t "a") 'thing) 'CxPerf {})
        (v/assert kb (list 'set/forwardRule (list 'implies (list pr '?x '?y) (list 'gmNoted '?x '?y)))
                  'CxPerf {})))
    (let [denials (mapv #(list 'not (list 'genl (symbol (str "gm_c" %)) (symbol (str "gm_b" %))))
                        (range n))]
      (doall (for [i (range 100)]
               (nanos (dotimes [j 20]
                        (inherit/moved-predicates kb (nth denials (mod (+ i j) n))))))))))

(defn- genl-crossing-wide
  "The narrowing one `(genl gw_root gw_top)` pays, on a KB holding n subtypes of `gw_root`
  and fifty predicates preserved along `genl`, each with a claim on one of the subtypes
  and a forward rule over it: a batch of `inherit/moved-predicates` calls, the same batch
  at both sizes.

  Every claim sits below the edge, so each predicate is moved whatever the narrowing
  reads; the question is what the reading costs.  The closure below `gw_root` holds n
  terms, and past `inherit/crossing-closure-cap` the edge is not narrowed: the walk stops
  one term past the cap and every predicate preserved along `genl` is moved off the
  declarations' relation index, with no read per term.  The selection is timed alone
  because the arrival around it re-joins fifty rules, which is the same work at both
  sizes and would dilute the growth."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genl (symbol (str "gw_leaf" i)) 'gw_root) 'CxPerf {}))
      (v/assert kb '(genl gw_root thing) 'CxPerf {})
      (v/assert kb '(genl gw_top thing) 'CxPerf {})
      (doseq [j (range 50) :let [pr (symbol (str "gwRel" j))]]
        (v/assert kb (list 'transitiveInArgInverse pr 1 'genl) 'CxPerf {:strength :monotonic})
        (v/assert kb (list pr (symbol (str "gw_leaf" j)) 'thing) 'CxPerf {})
        (v/assert kb (list 'set/forwardRule (list 'implies (list pr '?x '?y) (list 'gwNoted '?x '?y)))
                  'CxPerf {})))
    (doall (for [_ (range 60)]
             (nanos (dotimes [_ 10]
                      (inherit/moved-predicates kb '(genl gw_root gw_top))))))))

(defn- qcn-network-residency
  "A `possible-relations` call on a fixed six-region containment chain, asked repeatedly,
  on a KB holding n *more* facts of the same spatial predicate in a context the asker
  cannot see.

  The network the call reads is the same size at both n — six regions, one closure — so
  what the reading tracks is the **read**, never the pass.  A resident network is taken
  off the KB's `:qcn` atom and rebuilt only when the change clock moves
  (`observe/cached`), so a repeat costs a map lookup; reading the KB again per call would
  walk the predicate's whole extent, which is exactly the n that grows here.
  docs/qcn.md counts that difference as seventeen thousand reads against thirty-nine
  asserts, taken down to seventy-eight.

  **The extra facts sit in a sibling context on purpose.**  A check whose visible network
  grew with n would be measuring the path-consistency pass, which is superquadratic by
  design and is nobody's claim to hold flat — the growth would swamp the read and the
  bound would have to be loose enough to see nothing.  A sibling context is invisible from
  the asking one, so the pass is identical at both sizes and the extent a rebuild would
  walk is the only thing that moved.

  The counted companion is `qcn_chain_test/network-reads-grow-with-the-calls-and-not-with
  -the-asserts`, which holds the *number* of builds where this holds their cost."
  [n]
  (let [kb    (fresh-kb)
        chain (mapv #(symbol (str "PqRegion" %)) (range 6))]
    (v/add-prover kb (space/spatial-prover))
    (v/assert kb '(genlCx CxPerfQcn CxUniverse) 'CxUniverse {:strength :monotonic})
    (v/assert kb '(genlCx CxPerfQcnSide CxUniverse) 'CxUniverse {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [[a b] (partition 2 1 chain)]
        (v/assert kb (list 'nonTangentialProperPart a b) 'CxPerfQcn {:strength :monotonic}))
      (doseq [i (range n)]
        (v/assert kb (list 'nonTangentialProperPart
                           (symbol (str "PqOtherA" i)) (symbol (str "PqOtherB" i)))
                  'CxPerfQcnSide {:strength :monotonic})))
    ;; build and close once, outside the loop: the first read is the pass, and timing it
    ;; would gate the closure's cost instead of the repeat's
    (v/possible-relations kb :rcc8 'CxPerfQcn (first chain) (peek chain))
    (doall
     (for [_ (range 60)]
       (nanos (dotimes [_ 200]
                (v/possible-relations kb :rcc8 'CxPerfQcn (first chain) (peek chain))))))))

(defn- qcn-chain-load
  "Each assert of a containment chain of n regions loaded one fact at a time, with the
  spatial prover registered and one forward rule over a calculus predicate — the
  `lein bench-qcnchain` prover + rule column, read per fact.

  Every pair of a chain composes, so each arriving fact tightens pairs network-wide.
  docs/qcn.md, \"Cost at load, measured\", says where that cost goes: the plain pass
  warm-starts and the join is semi-naive, and the support-carrying pass runs whole once
  per arriving fact."
  [n]
  (let [kb   (fresh-kb)
        node #(symbol (str "PqcReg" %))]
    (v/add-prover kb (space/spatial-prover))
    (v/assert-rule kb ['(properPartOfRegion ?x ?y)] '(pqc_contained ?x) 'CxPerf
                   {:direction :forward})
    (doall (for [i (range 1 n)]
             (nanos (v/assert kb (list 'nonTangentialProperPart (node i) (node (dec i)))
                              'CxPerf {}))))))

(defn- qcn-arrival-over-standing-firings
  "One assert of a spatial fact in a context of its own, on a KB whose forward rule over
  the calculus stands on the n(n-1)/2 firings a containment chain of n regions entails
  in a sibling context.

  The arrival moves the calculus, so every rule joining on it is queued for the settle's
  re-check; what the re-check owes a standing firing is whether a network it rests on
  turned unsatisfiable (`chain/entailment-withdrawable?`), and none did.  The sibling
  keeps the chain's network unmoved, so no pass over it runs again; the join still reads
  it, which is the growth the bound leaves room for."
  [n]
  (let [kb   (fresh-kb)
        node #(symbol (str "PqsReg" %))]
    (v/add-prover kb (space/spatial-prover))
    (doseq [c '[CxPerfQsChain CxPerfQsSide]]
      (v/assert kb (list 'genlCx c 'CxPerf) 'CxUniverse {:strength :monotonic}))
    (v/assert-rule kb ['(properPartOfRegion ?x ?y)] '(pqsIn ?x ?y) 'CxPerf
                   {:direction :forward})
    (doseq [i (range 1 n)]
      (v/assert kb (list 'nonTangentialProperPart (node i) (node (dec i))) 'CxPerfQsChain {}))
    (doall (for [i (range 60)]
             (nanos (v/assert kb (list 'nonTangentialProperPart (symbol (str "PqsA" i))
                                       (symbol (str "PqsB" i)))
                              'CxPerfQsSide {}))))))

(defn- qcn-arrival-over-composed-exceptions
  "One assert of a spatial fact in a context of its own, on a KB whose forward rule stands
  on n firings and carries an exception on a relation the spatial calculus answers by
  composition.

  The arrival moves the calculus, so the rule is queued and every firing's exception is
  asked again (`special/composed-exception-rules`): the re-check takes the whole rule on
  every arrival, not the firings whose pair moved.  What grows is those n level-6 asks."
  [n]
  (let [kb   (fresh-kb)
        bird #(symbol (str "PqeBird" %))]
    (v/add-prover kb (space/spatial-prover))
    (v/assert kb '(genlCx CxPerfQeSide CxPerf) 'CxUniverse {:strength :monotonic})
    (v/assert kb '(exceptWhen (spatiallyDisconnected ?x PqeRoom)
                              (set/forwardRule (implies (and (pqe_bird ?x)) (pqe_flies ?x))))
              'CxPerf {})
    (v/assert kb '(spatiallyDisconnected PqeCage PqeRoom) 'CxPerf {})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pqe_bird (bird i)) 'CxPerf {})))
    (doall (for [i (range 60)]
             (nanos (v/assert kb (list 'nonTangentialProperPart (symbol (str "PqeA" i))
                                       (symbol (str "PqeB" i)))
                              'CxPerfQeSide {}))))))

(defn- qcn-arrival-beside-an-unmoved-network
  "One assert of a spatial fact in a context of its own, on a KB holding a containment
  chain of n regions in a sibling context and a forward rule over a relation the chain
  entails nowhere, so no firing stands on it.

  The arrival moves the change clock, so the chain's network is read again for the
  re-join's delta; the read equals the resident value, which stays
  (`qcn-kb/read-network`), and the delta compares no pair.  What grows is the read,
  linear in the chain's facts.  A delta compared pair by pair reads the n(n-1) pairs
  the chain closes to.  The chain is loaded under one settle, because loading it a
  fact at a time costs a pass per fact."
  [n]
  (let [kb   (fresh-kb)
        node #(symbol (str "PquReg" %))]
    (v/add-prover kb (space/spatial-prover))
    (doseq [c '[CxPerfQuChain CxPerfQuSide]]
      (v/assert kb (list 'genlCx c 'CxPerf) 'CxUniverse {:strength :monotonic}))
    (v/assert-rule kb ['(externallyConnected ?x ?y)] '(pquTouch ?x ?y) 'CxPerf
                   {:direction :forward})
    (v/with-deferred-settle kb
      (doseq [i (range 1 n)]
        (v/assert kb (list 'nonTangentialProperPart (node i) (node (dec i))) 'CxPerfQuChain {})))
    (doall (for [i (range 60)]
             (nanos (v/assert kb (list 'nonTangentialProperPart (symbol (str "PquA" i))
                                       (symbol (str "PquB" i)))
                              'CxPerfQuSide {}))))))

(def ^:private metric-arrivals
  "How many constraints arrive one at a time in `metric-closure-warm-start` — the same
  count at both sizes, since the reading is per arrival."
  25)

(defn- metric-closure-warm-start
  "A chain of n instants, closed, and then 25 more instants arriving one constraint at a
  time with the gap back to the head of the chain read after each — a timeline being
  loaded, which is the structure that puts a closure in front of every fact.

  **Pure data, and deliberately.**  `stp/close-state-from` knows nothing about a KB, so
  what this measures is the algorithm and not the belief read in front of it; that the
  engine actually reaches it is `stp_test/an-arriving-constraint-is-relaxed-into-the-answer
  -already-held`, which counts the two routes through `stp/closure`. Splitting them is what
  keeps the ratio a claim about the pass — a KB read is linear in the stated constraints
  and would sit in the denominator at both sizes flattering neither.

  **Not a flat claim, and the bound says which claim it is instead.**  A closure is a
  bound between every pair of instants, so an arriving constraint costs at least the pairs
  it moves and is quadratic in the instant count however it is reached.  What the warm
  start removes is the *pass*, and the bound is where the two shapes separate."
  [n]
  (let [inst  #(symbol (str "Pmt" %))
        base  (reduce (fn [net i] (stp/narrow net (inst i) (inst (inc i)) 8 12))
                      {} (range (dec n)))
        head  (inst 0)]
    (loop [net base, state (stp/close-state base (stp/nodes base)), i 0, acc []]
      (if (= i metric-arrivals)
        acc
        (let [p     (inst (+ n i -1))
              q     (inst (+ n i))
              net'  (stp/narrow net p q 8 12)
              nodes (stp/nodes net')
              box   (volatile! nil)
              t     (nanos (vreset! box (stp/close-state-from net' state nodes)))]
          (stp/constraint (:net @box) head q)
          (recur net' @box (inc i) (conj acc t)))))))

;; ---- a context NAT, a sign chain, a brave ask, a marked clique ------------

(defn- context-nat-existing-context
  "Facts written into n sibling day contexts of one context function that
  `contextArgSubrelation` orders, each context already minted: the sixty timed asserts
  go round the existing days.  A mint orders the new context against its siblings
  (`context-nat/reconcile-genlCx`); a fact into a context already minted creates no
  sibling pair, so what it costs does not depend on how many siblings there are.

  The contexts are built under one deferred settle: they are the KB this measures
  against, not the thing measured."
  [n]
  (let [kb  (fresh-kb)
        M   {:strength :monotonic}
        day #(list 'CxPcnDayFn 'CxMonad
                   (list 'DatetimeFn (str (.plusDays (java.time.LocalDate/of 2000 1 1) (long %)))))]
    (v/assert kb '(context_denoting_function CxPcnDayFn) 'CxUniverse M)
    (v/assert kb '(unreifiable_function DatetimeFn) 'CxUniverse M)
    (v/assert kb '(contextArgSubrelation CxPcnDayFn 2 subintervalOf) 'CxUniverse M)
    (v/assert kb '(pcnNote PcnYear PcnVal) '(CxPcnDayFn CxMonad (DatetimeFn "2000")) M)
    (v/with-deferred-settle kb
      (doseq [i (range n)] (v/assert kb '(pcnNote PcnDay PcnVal) (day i) M)))
    (doall (for [i (range 60)]
             (nanos (v/assert kb (list 'pcnNote (symbol (str "Pcn" i)) 'PcnVal)
                              (day (mod i n)) M))))))

(defn- sign-chain-rebuild
  "A `qualitativeSum` chain grown one link at a time, and after each of the last sixty
  links the ask of the new tail's sign.  The write moves the change clock, so each ask
  rebuilds the sign reading (`sign/build-reading`), which reads every sign fact: linear in
  the chain by design.  What the check catches is a fixpoint that re-applies every
  constraint per pass while the chain moves one link per pass, or a narrowing that copies
  the growing support set along the chain: both are quadratic."
  [n]
  (let [kb (fresh-kb)
        M  {:strength :monotonic}
        q  #(symbol (str "PsQ" %))]
    (v/add-reasoner kb :sign)
    (v/assert kb '(signOf PsQ0 SignPositive) 'CxPerf M)
    (into []
          (keep (fn [i]
                  (v/assert kb (list 'signOf (symbol (str "PsP" i)) 'SignPositive) 'CxPerf M)
                  (v/assert kb (list 'qualitativeSum (q (dec i)) (symbol (str "PsP" i)) (q i))
                            'CxPerf M)
                  (when (> i (- n 60))
                    (nanos (count (v/ask kb (list 'signOf (q i) '?s) 'CxPerf))))))
          (range 1 (inc n)))))

(def ^:private asks-per-brave-reading
  "Asks batched into one timed reading, the same batch at both sizes so it cancels out of
  the ratio: a single ask answered from the held classification sits under the noise
  floor."
  10)

(defn- brave-ask-between-writes
  "`(bravely S)` and `(cautiously S)` asked of one Nixon diamond's side on a KB holding n
  independent diamonds, with no write between the asks.  Belief does not move between
  two asks, so the classification the first one computes answers the rest
  (`label/classify-datum`); a classification per ask is linear in the dilemmas.

  The solve-free path, forced by hiding the backend, so the reading does not depend on a
  solver being installed: with one, a classification over every dilemma at once is
  exponential in the independent dilemmas and would not finish at the large size.  Built
  under one deferred settle."
  [n]
  (with-redefs [solver/available? (constantly false)]
    (let [kb   (fresh-kb)
          rule (fn [ante conseq]
                 (list 'set/defaultRule
                       (list 'set/forwardRule (rules/rule-sentence [ante] conseq))))]
      (v/add-reasoner kb :brave-cautious)
      (v/assert kb (rule '(pb_quaker ?x) '(pb_pacifist ?x)) 'CxPerf)
      (v/assert kb (rule '(pb_republican ?x) '(not (pb_pacifist ?x))) 'CxPerf)
      (v/with-deferred-settle kb
        (doseq [i (range n) :let [x (symbol (str "PbX" i))]]
          (v/assert kb (list 'pb_quaker x) 'CxPerf)
          (v/assert kb (list 'pb_republican x) 'CxPerf)))
      (doall (for [_ (range 60)]
               (nanos (dotimes [_ asks-per-brave-reading]
                        (v/ask? kb '(bravely (pb_pacifist PbX0)) 'CxPerf)
                        (v/ask? kb '(cautiously (pb_pacifist PbX0)) 'CxPerf))))))))

(defn- sibling-disjoint-new-spec
  "A `sibling_disjoint` clique of n specializations, then sixty more added one at a time,
  member first: each new type already holds an instance (which also holds a type outside
  the clique), and the timed write is the `(genl s root)` edge that puts it in the clique.
  Whether a type sits under the marked parent is read off the type's own supertype
  closure; the parent's spec closure holds the whole clique and is rebuilt after every
  `genl` edge.  The clique is built under one deferred settle."
  [n]
  (let [kb  (fresh-kb)
        M   {:strength :monotonic}
        add (fn [i]
              (let [t (symbol (str "psd_s" i "_t")) x (symbol (str "PsdX" i))]
                (v/assert kb (list 'psd_benign x) 'CxPerf M)
                (v/assert kb (list t x) 'CxPerf M)
                (list 'genl t 'psd_root)))]
    (v/assert kb '(genl psd_benign thing) 'CxPerf M)
    (v/assert kb '(genl psd_root thing) 'CxPerf M)
    (v/assert kb '(sibling_disjoint psd_root) 'CxPerf M)
    (v/with-deferred-settle kb
      (doseq [i (range n)] (v/assert kb (add i) 'CxPerf M)))
    (doall (for [i (range n (+ n 60))
                 :let [edge (add i)]]
             (nanos (v/assert kb edge 'CxPerf M))))))

;; ---- the one check that writes to a disk ---------------------------------
;;
;; Every check above runs on `fresh-kb`, which is `:backend :memory`, so nothing in this
;; file has ever priced the durable stores — and `assert_cost_test`, the counted gate
;; beside it, is pinned to the memory backend for its own reason.  The write-ahead logs,
;; the idx slots and the batching between them are gated by neither.

(defn- delete-tree!
  [^java.io.File file]
  (when (.isDirectory file)
    (doseq [child (.listFiles file)] (delete-tree! child)))
  (.delete file))

(defn- perf-disk-dir ^java.io.File []
  (java.io.File. (str (System/getProperty "java.io.tmpdir") "/vaelii-perf-disk")))

(defn- fresh-disk-kb
  "An empty `:backend :disk-log` KB in a directory of its own — `fresh-kb`'s durable twin.
  Wiped **before** the open as well as after the close, so a run interrupted part way
  leaves nothing for the next one to measure against."
  []
  (let [dir (doto (perf-disk-dir) (delete-tree!) (.mkdirs))]
    (v/open-kb {:backend :disk-log :dir (.getAbsolutePath dir) :recover? false})))

(defn- installed-image-reads
  "n `disjoint` declarations over 2n types, and one term a member of the first pair, in a
  `:disk-snapshot` KB closed and opened again, so the open installs its reasoning image.
  Each reading is 1,000 asks of `decide/live?`, which every scoped read's visibility
  callback asks, each comparing the membership candidates' separation stamp with the
  taxonomy's rosters."
  [n]
  (let [dir  (doto (perf-disk-dir) (delete-tree!) (.mkdirs))
        path (.getAbsolutePath dir)
        U    'CxUniverse
        t    (fn [s i] (symbol (str s i)))]
    (try
      (let [kb (v/open-kb {:backend :disk-snapshot :dir path})]
        (v/with-deferred-settle kb
          (doseq [i (range n)]
            (v/assert kb (list 'disjoint (t "isa_" i) (t "isb_" i)) U)))
        (v/assert kb '(isa_0 ImagePair) U)
        (v/assert kb '(isb_0 ImagePair) U)
        (v/close! kb))
      (let [kb (v/open-kb {:backend :disk-snapshot :dir path})]
        (try
          (doall (for [_ (range 5)] (nanos (dotimes [_ 1000] (decide/live? kb)))))
          (finally (v/close! kb))))
      (finally (delete-tree! dir)))))

(defn- durable-fact-append
  "n facts of one predicate onto a disk-backed KB, timed per assert.

  Every quantity the durable write path spends per record is fixed by construction — one
  log frame and one idx slot per record, one packed WAL append for the whole batch of
  index ops a sentex generates — so the reading should not move between the two sizes at
  all.  What can move it is the **set** behind the predicate root, which grows to n: the
  index WAL logs the op (`[:add-to-set k m]`, one member) rather than the resulting value,
  and a frame carrying the grown set instead would make a linear load quadratic.
  `vaelii.impl.disk.kv` records that shape as the reason for logical logging, and this is
  the check that would notice it coming back.

  One predicate throughout, so that root is the hot one; distinct subjects, so no
  cross-context or partner pass has anything to reach for and what is measured is
  storage.  `:chain? false` for the same reason — no rule exists to fire, and the KB is
  built by the very operation being timed.

  Closed on the way out, and the directory removed after it: the file lock and the
  durability daemon's registration both belong to the directory, and a check that left
  them would have every later check's wall-clock crossed by an fsync of a store nothing
  is using — and the gate would leave a few megabytes of log behind every time it ran."
  [n]
  (let [kb (fresh-disk-kb)]
    (try
      (doall
       (for [i (range n)]
         (nanos (v/assert kb (list 'pdFact (symbol (str "PdA" i)) i) 'CxPerf
                          {:chain? false}))))
      (finally
        (v/close! kb)
        (delete-tree! (perf-disk-dir))))))

(def checks
  ;; The one bound here that is not *flat*, and deliberately.  A settle republishes the
  ;; whole standing clash set, so its cost is Ω(standing) by construction and no memo
  ;; makes an assert free of what is standing.  What the gate defends is that the per-pair
  ;; term stays **bookkeeping** rather than a re-derivation of the checks, and the
  ;; measured separation says it does: 9.5x with both memos in place, 12.3x with the
  ;; report memo removed, 46.5x with the carry-forward removed as well — the structure that
  ;; actually shipped.  15x catches that with three times over on the big one.
  ;;
  ;; The baseline is 25 rather than 100 because it has to be a size at which almost
  ;; nothing is standing.  At 100 the baseline already carried a hundred pairs' worth of
  ;; the very per-pair cost being measured, which divided out of the ratio and left the
  ;; three variants reading 6.1 / 7.5 / 9.2 — a 12x difference in what matters, compressed
  ;; into a 1.5x spread the bound could not have separated.
  [{:name      :clash-arbitration
    :claim     "32x the standing clashes costs under 15x per assert — bookkeeping, not a re-derivation each"
    :sizes     [25 800]
    :max-ratio 15.0
    :run       clash-arbitration}

   {:name      :constraint-exposure-shared-arg
    :claim     "asserting into a declared-asymmetric slot costs what the region holds, not what the KB does"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       constraint-exposure-shared-arg}

   ;; **Both ends measured, on full runs.**  Above: 0.74x and 1.01x, flat — the read is
   ;; the term's memberships, and n moves only the facts that state none.  Below: the
   ;; same workload with `kb/types-of` reading `sentexes-with-arg` at position 1, which
   ;; is what it read before `unary-sentexes-with-arg` existed, reads **4.77x** (0.094
   ;; against 0.450 ms/op) — a record fetch per fact naming the term, to find the two
   ;; types it holds.  The bound is the file's standing 2.0 for a flat claim: twice the
   ;; worse healthy reading, and under half the defective one at this size step.  The gap
   ;; is a claim about the 8x step and grows with it — the defective shape is linear in n
   ;; and this is not — so a wider pair would separate further and none is needed to
   ;; fail it.
   {:name      :membership-read-under-busy-term
    :claim     "a membership question is flat in the facts that name the term but state no type"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       membership-read-under-busy-term}

   ;; **Both ends measured, on a loaded machine.**  Above: 0.27x, 0.49x and 0.80x.  Below,
   ;; the trigger reading every record that names the term and filtering them on the
   ;; network, which it did before the mint roster existed, reads 3.06x, 3.95x and 6.91x:
   ;; the step is 32x rather than the file's usual 8x because at 8x the two shapes
   ;; overlapped under that load (1.74x–2.08x against 2.14x–3.83x).
   {:name      :mint-withdrawal-under-busy-term
    :claim     "with subsumed mints pruned, a membership is flat in the facts that name its term"
    :sizes     [250 8000]
    :max-ratio 2.0
    :run       mint-withdrawal-under-busy-term}

   ;; **Both ends measured, in one warm JVM under a load average of 21.**  Above: 0.68x,
   ;; 0.32x and 0.20x (0.35 ms against 0.24).  Below, the settle re-reading every withheld
   ;; mint kept in the refusal record on each pass, rather than reading a release off the
   ;; departing record's term, reads 10.83x and 17.47x (0.88 ms against 15.31).
   ;; The small size is 32 because at 250 the re-read already dominates the baseline and
   ;; the defective shape read 3.44x against a healthy 2.56x.
   {:name      :settle-beside-withheld-mints
    :claim     "with subsumed mints pruned, a settle that moves no membership is flat in the mints the KB withholds"
    :sizes     [32 4096]
    :max-ratio 2.0
    :run       settle-beside-withheld-mints}

   ;; **Both ends measured, on full runs.**  Above: 1.39x, 0.90x and 1.03x.  Below, two
   ;; shapes, each implemented and run: the readers taken as every common descendant,
   ;; which is what `discovery/group-vantages` read before `tax/ground-contexts` existed,
   ;; reads **6.28x** (1.39 against 8.72 ms/op); the readers narrowed but the maxima
   ;; found by filtering the whole intersection, which `maximal-common-descendant-contexts`
   ;; did before it walked, reads **2.86x** (1.23 against 3.51).  The bound is the file's
   ;; standing 2.0 for a flat claim, under both.
   {:name      :per-reading-vantages
    :claim     "a vantage below a maximum that reads less of the grounds costs the contexts below a ground it lacks, not the lattice below the members"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       per-reading-vantages}

   ;; **Both ends measured, on full runs.**  Above: 1.11x and 0.90x, and 0.84x and 0.67x
   ;; on two trees whose join is this one.  Below: the join reading every believed step
   ;; of the functor and filtering on the term, where it reads the term's postings, reads
   ;; **3.65x** (1.72 against 6.26 ms/op).  The bound is the standing 2.0.
   {:name      :chain-join
    :claim     "an anti_transitive chain split across three contexts is joined on its own terms, flat in the open chains beside it"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       chain-join}

   {:name      :constraint-exposure-context-edge
    :claim     "past the instance cap, 8x the facts behind a genlCx edge costs the same"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       constraint-exposure-context-edge}

   {:name      :unrelated-fact-under-marked-kb-fanout
    :claim     "an unrelated predicate's assert is flat in the genlCx fanout below its context, however many other predicates elsewhere carry a functional mark"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       unrelated-fact-under-marked-kb-fanout}

   {:name      :functional-in-arg-empty-determinant-sweep
    :claim     "past the instance cap, 8x the facts under an empty-determinant functionalInArg mark costs the same per assert"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       functional-in-arg-empty-determinant-sweep}

   {:name      :defeasible-load
    :claim     "a fact arriving through a defeasible rule costs the same at 2000 as at 250"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       defeasible-load}

   {:name      :taxonomy-depth
    :claim     "a genl edge costs the same 2000 deep in a chain as 250 deep"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       taxonomy-depth}

   {:name      :taxonomy-belief-flip
    :claim     "defeating and reviving one genl edge costs the same in a 4000-edge taxonomy as in a 500-edge one"
    :sizes     [500 4000]
    :max-ratio 2.0
    :run       taxonomy-belief-flip}

   ;; 2026-09-30: 0.65x-0.77x healthy.  With the withdrawal stamp comparing the flat caches'
   ;; supporting contexts by `=`, every settle's compare walked the declarations: 1.26x-1.41x
   ;; alone, 2.49x in a full run.
   {:name      :flat-cache-belief-flip
    :claim     "defeating and reviving one inverse declaration costs the same in a KB declaring 4000 disjoint pairs as in one declaring 500"
    :sizes     [500 4000]
    :max-ratio 2.0
    :run       flat-cache-belief-flip}

   {:name      :arg-root-retrieval
    :claim     "100 patterns pinning an argument after a variable are flat in the extent"
    :sizes     [400 3200]
    :max-ratio 2.0
    :run       arg-root-retrieval}

   {:name      :closure-membership
    :claim     "one pair's membership in a closure already asked is flat in the chain's length"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       closure-membership}

   {:name      :membership-check
    :claim     "asserting a type membership is flat in how many the KB already holds"
    :sizes     [200 1600]
    :max-ratio 2.0
    :run       membership-check}

   {:name      :membership-under-depth
    :claim     "32x the hierarchy above a predicate costs under 12x per membership assert — one retrieval per super, so it grows with the depth and must stay well under it"
    :sizes     [8 256]
    :max-ratio 12.0
    :run       membership-under-depth}

   {:name      :disjoint-enumeration
    :claim     "an open disjointness goal is flat in the vocabulary it is not about"
    :sizes     [500 4000]
    :max-ratio 2.0
    :run       disjoint-enumeration}

   {:name      :disjoint-clique-membership
    :claim     "a membership assert whose type sits in a sibling-disjoint clique is flat in the clique size"
    :sizes     [500 4000]
    :max-ratio 2.0
    :run       disjoint-clique-membership}

   {:name      :disjoint-metatype-membership
    :claim     "a membership assert whose type belongs to a disjoint_metatype is at most linear in the member count, never quadratic"
    :sizes     [500 4000]
    :max-ratio 12.0
    :run       disjoint-metatype-membership}

   {:name      :compound-probe
    :claim     "100 find-sentexes on a compound are flat in the extent of the hot atom it names"
    :sizes     [1000 32000]
    :max-ratio 2.0
    :run       compound-probe}

   ;; The negation twin of `clash-arbitration`, and the same reasoning picks its numbers:
   ;; Ω(standing) is the floor (a settle republishes the whole set), the baseline is
   ;; small enough that almost nothing is standing at it, and the bound separates
   ;; bookkeeping-per-pair from re-derivation-per-pair.  Re-deriving every standing pair
   ;; per settle round measured 38.9x here — the structure that shipped, and the one `:opposed`
   ;; was believed to have removed.  It removed a different one: the *scan of every stored
   ;; negation*, which is the commoner workload and is what `negation-load` below still
   ;; holds flat.  Neither check subsumes the other, and only both together say the pass is
   ;; not paying for the standing set (see docs/nmtms.md).
   ;;
   ;; **The baseline is 100 and not 25, and the bound sits above the size ratio, because
   ;; that combination is the only one a constant-term win cannot break.**  Reading
   ;; `a + b·n`, the ratio is `(a + 800b) / (a + 100b)`, which is strictly *below* 8 for
   ;; every positive `a` and approaches 8 as `a` falls.  So no improvement to the fixed cost
   ;; of a settle can walk this check upward, however far that cost falls: what is left to
   ;; cross the bound is the per-pair term going super-linear, which is what the claim is
   ;; about.  That argument bounds the *constant's* contribution and not the whole reading,
   ;; so the bound is set from measurement rather than from the model: four full runs read
   ;; 6.63x, 7.58x, 7.74x and 8.36x, the last of them above the model's own ceiling.  The
   ;; spread is the large end — n=800 moves ten percent and more between runs where n=100
   ;; moves one — so 11 is the worst of those with room, and a re-derivation regression
   ;; reads several times it rather than a few percent over.
   ;;
   ;; A baseline of 25 gave the ratio an asymptote of 32 against a bound of 12, which is
   ;; 20x of room for a constant-term win to spend: the fixed cost is ~0.04 ms against
   ;; ~0.0017 ms a pair, so at 25 pairs the reading is mostly constant, and shaving it walks
   ;; the ratio from 10x toward 17x while every absolute number improves.  A check that
   ;; reddens *because* the code got faster is measuring the wrong thing.
   ;;
   ;; Still the check most exposed to the header's cold/warm gap, though a narrower one at
   ;; this baseline: 5.70x under `--only` against 6.63x in place, the split being in the
   ;; denominator as it is everywhere.  Read a passing `--only` here as a cold reading and
   ;; nothing more.
   {:name      :negation-arbitration
    :claim     "8x the standing P/¬P dilemmas costs under 11x per assert — linear in the set, not a re-derivation of it each"
    :sizes     [100 800]
    :max-ratio 11.0
    :run       negation-arbitration}

   ;; The inherited twins of `clash-arbitration`, and Ω(standing) for its reason: a settle
   ;; republishes, weighs and reports every standing clash.  **Both ends measured.**
   ;; Above, one context: 1.90x alone and 5.45x in a full run, 2.6 against 14.2 ms/op, of
   ;; which `preserving-nogoods` is a quarter and the weighing and the reports the rest.
   ;; Below, the pass that asked every standing clash each settle and the whole extent for
   ;; every claim written: **12.27x** (53.7 against 659 ms/op), the better of two
   ;; attempts.  The baseline carries that pass's extent sweep over the 60 timed facts
   ;; themselves, which is what holds the defective ratio near 12.  The bound is about
   ;; twice the healthy reading, and under the defective one.
   {:name      :inherited-clash-arbitration
    :claim     "32x the standing inherited dilemmas costs under 10x per assert — carried, not asked again"
    :sizes     [16 512]
    :max-ratio 10.0
    :run       (partial inherited-clash-arbitration false)}

   ;; The split twin.  Each settle empties the withdrawal cache while an inherited clash
   ;; is held (`discovery/clear-inherited!`), so the next read at `CxPW` decides every
   ;; standing clash again (`decide/losers`), because belief is computed from current
   ;; state (docs/nmtms.md, "Where the scaling arguments hold").  So this cost grows with
   ;; n by design.  The memo carries every clash's question: `inherit/clashing-claim` runs
   ;; twice per assert at both sizes.
   ;;
   ;; **Why the timed fact is `unrelP` and the baseline one clash.**  Healthy and defective
   ;; are both `a + b·n` per assert, and the ratio separates them only by `a/b`.  Timing a
   ;; `bigP` fact puts both near 30: the defective pass asks the whole stored `bigP`
   ;; extent, the timed facts included, for each fact written, and that sweep lands in its
   ;; `a`.  At [16 512] that shape read 11.2x to 11.6x healthy in full runs against 20.0x
   ;; defective, a separation under the 2x slack a bound needs.  A fact of `unrelP` reaches
   ;; no preserved predicate, so the defective `a` is the assert alone and its `b` the
   ;; question of every clash, and one clash keeps the healthy `b·n` out of the denominator.
   ;;
   ;; Healthy: 9.6x, 11.8x and 13.6x alone at load 23 to 34, 20.4x and 30.9x alone at load
   ;; 16, 21.9x to 43.1x in a JVM that had run the shape before (n=1 at 0.23 to 0.42 ms
   ;; against 0.45 to 1.15 cold), and 46.1x in a full run at load 9 (0.185 against 8.51
   ;; ms).  Defective, with `discovery/*incremental-preserving*` bound false: 149x, 249x and
   ;; 441x, 373 to 395 ms/op at n=512, the 149x a first run whose n=1 read 2.5 ms.  90 is
   ;; about twice the worst healthy reading and under the defective ones.
   {:name      :inherited-clash-arbitration-split
    :claim     "512x the standing inherited clashes split across contexts costs under 90x per unrelated assert — the memo carries each clash, and `CxPW` decides them again from current state"
    :sizes     [1 512]
    :max-ratio 90.0
    :run       (partial inherited-clash-arbitration true)}

   ;; The stored claims keep entries with no nogood, so a settle publishes nothing for
   ;; them and the healthy reading is the carry's map walk: 2.37x and 2.12x alone, 0.28
   ;; to 0.32 against 0.67 ms/op.  Asking every entry again when the region holds a
   ;; handle with no record reads 26.71x alone, 4.18 against 111 ms/op.  The bound is
   ;; about four times the healthy reading, and under the defective one.
   {:name      :inherited-entry-retraction
    :claim     "32x the carried inherited-clash entries costs under 10x per unrelated retract — a retraction asks only what it moved"
    :sizes     [16 512]
    :max-ratio 10.0
    :run       inherited-entry-retraction}

   ;; Both ends measured.  Healthy: 1.00x (0.147 against 0.147 ms per claim), each question
   ;; reading the rows its reach names through the memo's extent index.  Defective, every
   ;; question filtering the whole `bigP` extent row by row: 6.98x (1.520 against 10.605
   ;; ms).  2.0 is the file's bound for a flat claim, about twice the healthy reading.
   {:name      :recover-inherited-discovery
    :claim     "8x the claims of one preserved predicate costs under 2x per claim at recover — a question reads the stored rows its reach names, not the predicate's extent"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       recover-inherited-discovery}

   ;; Both ends measured.  Healthy: 0.56x (0.261 against 0.146 ms per claim), the
   ;; discovery syncing its own candidate index once under the copy.  Defective, the copy
   ;; and the live taxonomy re-stamping one shared index at each question: 5.60x (1.004
   ;; against 5.620 ms).  2.0 is the file's bound for a flat claim.
   {:name      :recover-discovery-own-out
    :claim     "8x the preserved claims and separated members costs under 2x per claim at recover — a discovery over a detached taxonomy syncs its own candidate index once"
    :sizes     [50 400]
    :max-ratio 2.0
    :run       recover-discovery-own-out}

   ;; Both ends measured.  Healthy: 1.06x (0.164 against 0.174 ms per nogood), each
   ;; member's violations read once per re-read.  Defective, each nogood re-asking its
   ;; members' violations, `p` disjointness tests each: 2.85x (0.407 against 1.160 ms).
   ;; 2.0 is the file's bound for a flat claim.
   {:name      :recover-discovery-separated-term
    :claim     "4x the types one term holds, each pair separated, costs under 2x per nogood at recover — a re-read asks each member's violations once"
    :sizes     [12 48]
    :max-ratio 2.0
    :run       recover-discovery-separated-term}

   ;; Both ends measured.  Healthy: 0.89x (1.857 against 1.658 ms per thousand asks), the
   ;; first ask taking the taxonomy's rosters and the rest comparing by identity.
   ;; Defective, each ask comparing the image's two copies of the `disjoint` roster entry
   ;; by entry: 27.44x (5.996 against 164.528 ms).  2.0 is the file's bound for a flat claim.
   {:name      :installed-image-reads
    :claim     "32x the disjoint declarations costs under 2x per thousand candidate-index asks after an image install — the separation stamp compares by identity"
    :sizes     [50 1600]
    :max-ratio 2.0
    :run       installed-image-reads}

   {:name      :negation-load
    :claim     "a negative fact with no positive twin costs the same at 2000 as at 250"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       negation-load}

   {:name      :feed-listener-scaling
    :claim     "an assert watched by a listener costs the same at 2000 as at 250 — per region, not per store"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       feed-listener-scaling}

   ;; The bound is the file's standing 2x for a *flat* claim, and it is set from the
   ;; claim rather than from a reading.  A teardown can only orphan a constant one of the
   ;; removed sentexes named, so the candidates are a property of what was removed and the
   ;; two readings here differ by the retraction's own cost and nothing else.  A
   ;; population term is the whole thing being gated, and a bound wide enough to admit one
   ;; would be a bound admitting it.
   ;;
   ;; The baseline is 32 for `clash-arbitration`'s reason.  A retraction has a fixed cost
   ;; of its own — the storage teardown, the settle, the feed event — and the small size
   ;; has to be one where that still dominates, or a baseline already carrying a hundred
   ;; NATs' worth of the per-NAT term divides it back out and compresses the spread the
   ;; bound has to separate.
   {:name      :retract-nat-scaling
    :claim     "retracting a fact that names no NAT is flat in the reified-NAT population it is not about"
    :sizes     [32 1024]
    :max-ratio 2.0
    :run       retract-nat-scaling}

   {:name      :columnar-fanout
    :claim     "an insert into the columnar trie is flat in the fan-out of the node it lands on"
    :sizes     [4000 64000]
    :max-ratio 2.0
    :run       columnar-fanout}

   {:name      :exception-roster-gate
    :claim     "exception-rule? is flat in how many rules carry an exception"
    :sizes     [64 2048]
    :max-ratio 2.0
    :run       exception-roster-gate}

   {:name      :overlay-selectivity
    :claim     "a fork's count-with-functor is flat in the size of the base posting it inherits"
    :sizes     [1000 32000]
    :max-ratio 2.0
    :run       overlay-selectivity}

   {:name      :intersect-selectivity
    :claim     "narrowing a rare argument root against a hot one is flat in the hot posting's extent"
    :sizes     [1000 32000]
    :max-ratio 2.0
    :run       intersect-selectivity}

   {:name      :arity-reach-trigger
    :claim     "a fact of a predicate whose arity is declared is flat in that predicate's extent"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       arity-reach-trigger}

   ;; Both ends measured in one warm JVM, 2026-09-29.  Above: 1.14x (0.20 ms against
   ;; 0.23).  Below, the arrival sweeping the bound predicate's extent, the retroactive
   ;; arity report a reader deciding the nogood replaced, reads 8.58x (1.59 ms against
   ;; 13.66).  3x is `irreflexive-mark-arrival`'s bound, for its reason.
   {:name      :arity-binding-arrival
    :claim     "32x the conforming tuples of a predicate costs under 3x per arity binding arriving over them and read through — no tuple is swept"
    :sizes     [256 8192]
    :max-ratio 3.0
    :run       arity-binding-arrival}

   ;; Both ends measured 2026-09-30.  Healthy 0.84x (0.133 ms against 0.111).  With each
   ;; binding recomputing every functor below it and rebuilding the exact lengths of every
   ;; binding, the reading is 7.00x (1.93 ms against 13.47).  2x sits between.
   {:name      :bound-type-load
    :claim     "8x the types, every one bound to a length, costs under 2x per binding arriving above bound types"
    :sizes     [400 3200]
    :max-ratio 2.0
    :run       bound-type-load}

   ;; Both ends measured 2026-10-01.  Healthy 0.95x and 0.97x (0.130 ms against 0.124,
   ;; 0.131 against 0.127).  With a walk up from each declaration's type, the reading is
   ;; 14.44x (4.56 ms against 65.86).  2x sits between.
   {:name      :declaration-rebuild
    :claim     "16x the declarations over a 16x deeper hierarchy costs under 2x per hundred declarations the recover rebuild re-reads"
    :sizes     [200 3200]
    :max-ratio 2.0
    :run       declaration-rebuild}

   ;; Both ends measured 2026-10-01.  Healthy 0.52x and 0.13x (0.267 ms against 0.512,
   ;; 0.291 against 2.160).  With a walk up from each waiting declaration's type, the
   ;; reading is 13.04x (5.40 ms against 70.40).  2x sits between.
   {:name      :mint-release-after-genl-move
    :claim     "16x the declarations waiting over a 16x deeper hierarchy costs under 2x per hundred declarations the settle after a genl edge re-asks"
    :sizes     [200 3200]
    :max-ratio 2.0
    :run       mint-release-after-genl-move}

   ;; Both ends measured 2026-10-01.  Healthy 1.32x and 1.09x (0.498 ms against 0.658,
   ;; 0.545 against 0.596).  With a `sees?` per fact, the reading is 7.67x (1.764 ms
   ;; against 13.529).  2x sits between.
   {:name      :lift-rebuild
    :claim     "16x the contexts above the stating context costs under 2x per hundred facts the recover lift rebuild re-reads"
    :sizes     [4 64]
    :max-ratio 2.0
    :run       lift-rebuild}

   {:name      :plan-scaling
    :claim     "planning one fixed conjunction is flat in the size of the KB it is planned against"
    :sizes     [1000 32000]
    :max-ratio 2.0
    :run       plan-scaling}

   {:name      :solve-rule-grounding
    :claim     "grounding a recursive solve rule costs the same per derived atom at any chain length"
    :sizes     [500 8000]
    :max-ratio 2.0
    :run       solve-rule-grounding}

   ;; Healthy 0.79x.  Walking the base's extent for the rules reads 24.80x (0.70 ms
   ;; against 17.25 a grounding).
   {:name      :label-beside-unrelated-facts
    :claim     "32x the facts beside a do/label program costs under 2x per grounding"
    :sizes     [1000 32000]
    :max-ratio 2.0
    :run       label-beside-unrelated-facts}

   ;; The bound is 4x rather than 2x because the vocabulary itself grows here — 8x the
   ;; sentexes is 2.8x the terms, and the report is entitled to that much.  What it
   ;; separates is 2.8x from the 8x a record scan reads, and 4x sits between them with
   ;; room on both sides.
   ;;
   ;; **Four of the census's seven readings**, and the claim says so.  This KB declares no
   ;; `arg`, `genlArg` or `interArg`, so the declarations reading walks an empty list
   ;; at both sizes and nothing here is a claim about it — the two checks below are.  It
   ;; stores no rule either, so the two rule-hygiene readings pair an empty set at both
   ;; sizes: their cost is the rule count and this workload holds it at zero.
   {:name      :quality-report-scaling
    :claim     "the rules, extents, chains and taxonomy readings of kb-quality grow with the vocabulary, not with what the KB stores"
    :sizes     [4000 32000]
    :max-ratio 4.0
    :run       quality-report-scaling}

   ;; **The fifth reading, first factor.**  Ω(declarations) is the floor — the census reads
   ;; each one — so 8x the declarations is at least 8x the walk, and the bound is a claim
   ;; about what sits above the floor.  Healthy it reads **7.56x and 7.71x** on full runs and 7.14x
   ;; alone, and the vocabulary is fixed at both sizes, so 97% of the reading is the walk
   ;; itself: the same KB with the declarations left out costs 0.051 ms against 1.756 at
   ;; n=250.  Below it, the form the arity table exists to replace — `checks/tabled-arity`
   ;; answered off the index rather than off the taxonomy, a walk of the argument-1 posting
   ;; these very declarations fill, so a census of n costs n² — reads **59.62x**,
   ;; implemented and measured on a full run rather than supposed.  15x is about twice the
   ;; healthy reading and under a third of the defective one, which is the slack the
   ;; arbitration bounds carry.
   {:name      :quality-declaration-census
    :claim     "the declarations census costs one arity reading per declaration, not one per declaration per declaration"
    :sizes     [250 2000]
    :max-ratio 15.0
    :run       quality-declaration-census}

   ;; **The fifth reading, second factor**, and the bound is read the same way.  The walk is
   ;; per super-predicate, so Ω(depth) is the floor here and 32x the hierarchy is at least
   ;; 32x — until the constant cost of the other four readings divides into it, which is
   ;; what puts a healthy reading under the span rather than over it: **22.78x, 24.26x and 26.11x** on
   ;; full runs and 20.29x alone, of which the declaration walk is nine parts in ten — the same KB with the
   ;; declarations left out costs 4.964 ms against 41.856 at n=256.  Below it, a
   ;; release asked of every super's own ancestry instead of every super — the square of the
   ;; depth per declaration — reads **74.75x** on a full run.  45x sits between them, and it is
   ;; placed differently from every other bound here: the floor is nearly the span, so
   ;; the healthy reading starts high and twice it is 52x, which is close enough to the
   ;; defect to be a bound that admits it on a bad run.  45x is the midpoint of the measured
   ;; pair instead — 1.7x above the worst healthy reading and 1.7x under the defective one.
   {:name      :quality-declaration-depth
    :claim     "the declarations census costs one arity reading per super-predicate, not one per super's own ancestry"
    :sizes     [8 256]
    :max-ratio 45.0
    :run       quality-declaration-depth}

   ;; The baseline is 64 for `clash-arbitration`'s reason: a retraction's own fixed cost
   ;; — the storage teardown, the settle, the feed event — has to still dominate at the
   ;; small size, or a baseline already carrying the whole-relation pass divides it back
   ;; out.  64 unrelated contexts is a graph such a pass crosses in well under that.
   {:name      :retract-context-cycle-scaling
    :claim     "retracting an edge of a context cycle is flat in the context graph it is not about"
    :sizes     [64 2048]
    :max-ratio 2.0
    :run       retract-context-cycle-scaling}

   ;; The same retraction with the n contexts in one cycle, and an insert beside that
   ;; cycle: the two edits that repair a component, against a component map of n entries
   ;; they are not about.  Each repair reads its own component's members off
   ;; `:scc-members`; with the members found by inverting the whole `:scc` map instead,
   ;; `--only` read 8.90x (retract) and 6.88x (assert) at 8192 on 2026-09-28, against
   ;; 0.41x and 0.92x.  The large size is 8192 because the inversion costs about 0.25 µs
   ;; an entry (2.20 against 0.26 ms/op for the assert at 8192), and at 2048 the
   ;; inverting assert read 1.74x on one run, under the bound.
   {:name      :retract-context-cycle-beside-cycle
    :claim     "retracting an edge of a context cycle is flat in the context cycles it is not about"
    :sizes     [64 8192]
    :max-ratio 2.0
    :run       (partial retract-context-cycle-scaling context-ring!)}

   {:name      :assert-context-edge-beside-cycle
    :claim     "asserting a context edge is flat in the context cycles it is not about"
    :sizes     [64 8192]
    :max-ratio 2.0
    :run       assert-context-edge-beside-cycle}

   ;; The baseline is 32 for `retract-nat-scaling`'s reason, which is `clash-arbitration`'s:
   ;; a retraction has a fixed cost of its own — the storage teardown, the settle, the feed
   ;; event — and the small size has to be one where that still dominates, or a baseline
   ;; already carrying a hundred merges' worth of the per-merge term divides it back out.
   ;;
   ;; The settle reconciles the taxonomy caches over the region and the data whose
   ;; supersession entry changed since the last settle (`settle/settle-finish`), so a
   ;; retraction naming no merged term carries no per-merge term: `--only` read 0.774 ->
   ;; 0.199 ms/op (0.26x) on 2026-09-28, against 5.66x with every superseded handle
   ;; handed to that reconcile.  **The bound is read off FULL runs**, where a warm JVM
   ;; halves the small size's reading and the ratio inflates from the denominator alone
   ;; (5.66x alone against 11.22x in place, same tree): 11.22x with the superseded set
   ;; re-read each settle, against 32.12x with its reconcile re-examining every entry.
   ;; 18x sits between those two readings: it bounds re-examination, and the flat
   ;; reading sits far under it.
   {:name      :retract-merge-scaling
    :claim     "retracting a fact naming no merged term costs under 18x per 32x the standing merges — bookkeeping, not a re-examination each"
    :sizes     [32 1024]
    :max-ratio 18.0
    :run       retract-merge-scaling}

   ;; Read off full runs both ways, not tuned until green: **17.73x** and **17.86x**
   ;; (0.718 -> 12.734 and 0.676 -> 12.082 ms/op) with the reconcile narrowed to the data
   ;; the except reaches, against **43.80x** (2.415 -> 105.776 ms/op) with it re-examining
   ;; every standing displaced spelling.  Those full-run readings carried the standing
   ;; superseded map on every settle, which `settle-finish` no longer reads: `--only` read
   ;; 1.609 -> 1.070 ms/op (0.66x) on 2026-09-28, against 2.48x with the map carried and
   ;; 27.93x with the full pass.  At [32 1024] the two full-run readings sit too
   ;; close to separate, which is why the large size is 4096.  28x sits between them.
   {:name      :except-merge-scaling
    :claim     "an except of a merge, asserted and retracted, costs under 28x per 128x the standing merges — the data it reaches, not every displaced spelling"
    :sizes     [32 4096]
    :max-ratio 28.0
    :run       except-merge-scaling}

   ;; Read off both ends under `--only`, 2026-09-28: 0.328 -> 10.018 ms/op (30.52x, load
   ;; average 13) and 0.355 -> 14.672 (41.33x, load average 47) with every settle emptying
   ;; the `:withdrawn` cache, so the next read recomputed each reader's withdrawal and the
   ;; roster; 0.259 -> 0.192 (0.74x) and 0.258 -> 0.201 (0.78x, load average 12) with the
   ;; settle keeping the entries no move reaches (`res/reconcile-withdrawn!`).  3x sits
   ;; between them, with room for a full run's warmer small size.
   {:name      :assert-over-standing-excepts
    :claim     "an assert naming nothing costs under 3x per 128x the believed excepts the KB stores — no reader's withdrawal is recomputed"
    :sizes     [32 4096]
    :max-ratio 3.0
    :run       assert-over-standing-excepts}

   ;; Read off both ends under `--only`, 2026-10-01: 0.540 -> 8.617 ms/op (15.96x) with
   ;; every reconcile of the settle reading its whole touched window, so the next
   ;; reconcile dropped the entry the settle built, against 0.132 -> 0.135 (1.02x) with
   ;; each reconcile reading the window since the cache's mark.
   {:name      :read-after-two-pass-settle
    :claim     "the first read of a reader's withdrawal after a two-pass settle costs under 3x per 128x the excepts it sees — the settle kept the entry it built"
    :sizes     [32 4096]
    :max-ratio 3.0
    :run       read-after-two-pass-settle}

   ;; Read off both ends under `--only`, 2026-09-29: 0.294 -> 8.964 ms/op (30.48x) with
   ;; each pass walking every rule's whole refusal set for the lift, mint and constraint
   ;; entries, against 0.201 -> 0.181 (0.90x) with the passes reading the kind roster.
   {:name      :assert-beside-naf-refusals
    :claim     "an assert naming nothing costs under 2x per 100x the refused firings the record holds — no pass walks a rule's refusals for a lift or a mint"
    :sizes     [320 32000]
    :max-ratio 2.0
    :run       assert-beside-naf-refusals}

   ;; Read off both ends under `--only`, 2026-09-30: 0.137 -> 0.091 ms/op (0.66x).  A
   ;; reader asking every firing of the rule read 0.13 -> 1.03 ms across 200 -> 12800.
   {:name      :guarded-firings-read-below
    :claim     "a first read below an exceptWhen rule's context costs under 2x per 16x the rule's firings when the reader sees no blocker — no firing is asked again"
    :sizes     [200 3200]
    :max-ratio 2.0
    :run       guarded-firings-read-below}

   ;; Read off both ends under `--only`, 2026-09-30: 13.065 -> 129.743 ms/op (9.93x) with
   ;; the pass re-joining the rule its seed re-chain queued, against 5.573 -> 5.960
   ;; (1.07x) with the queue read right after the sweep.  What stays is the next pass's
   ;; narrowing, a record read per firing, so 4x leaves it room.
   {:name      :released-refusal-beside-guarded-firings
    :claim     "a retraction releasing a firing that places a blocker costs under 4x per 16x the firings the blocked rule holds — no pass re-joins the rule over its whole extent"
    :sizes     [200 3200]
    :max-ratio 4.0
    :run       released-refusal-beside-guarded-firings}

   ;; Read off both ends under `--only`, 2026-09-28: 1.402 -> 12.857 ms/op (9.17x) with
   ;; an un-merge re-examining every displaced spelling, against 0.542 -> 0.359 (0.66x)
   ;; with the reconcile narrowed to the sentexes naming a term of the class that moved
   ;; (`special/reconcile-removed-supersession!`).  3x sits between them, with room for a
   ;; full run's warmer small size.
   {:name      :unmerge-over-standing-merges
    :claim     "an un-merge of one class costs under 3x per 32x the standing merges it does not touch — its own class, not every displaced spelling"
    :sizes     [32 1024]
    :max-ratio 3.0
    :run       unmerge-over-standing-merges}

   ;; Read off both ends under `--only`, 2026-09-28: 1.515 -> 11.591 ms/op (7.65x) with
   ;; each merge's reconcile reading the batch's whole window, against 0.328 -> 0.212
   ;; (0.65x) with the write path leaving the window to the batch's settle.  3x sits
   ;; between them.
   {:name      :deferred-merge-batch
    :claim     "a merging assert in a deferred batch costs under 3x per 8x the merges the batch holds — its own migration, not every entry the batch displaced"
    :sizes     [128 1024]
    :max-ratio 3.0
    :run       deferred-merge-batch}

   ;; Flat at the file's standing 2x, and the claim is exact: an edge that reaches no
   ;; exception must cost the same whether the KB's excepted rule has fired 32 times or
   ;; 1024.  The baseline is small for the usual reason — at 32 firings the per-firing
   ;; term has barely started, so it is not sitting in the denominator.
   {:name      :genl-edge-negation-recheck
    :claim     "a genl edge is flat in the firing history of a negated exception it cannot reach"
    :sizes     [32 1024]
    :max-ratio 2.0
    :run       genl-edge-negation-recheck}

   ;; Flat at the file's standing 2x.  Alone, 0.53x healthy, and 7.96x with both merge
   ;; arms gated on a mark declared anywhere in the KB.
   {:name      :genl-edge-under-no-merge-mark
    :claim     "a genl edge no merge mark stands above is flat in the facts below it"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       genl-edge-under-no-merge-mark}

   {:name      :genl-edge-under-no-rule-above
    :claim     "a genl edge no rule reads above is flat in the facts below it"
    :sizes     [64 1024]
    :max-ratio 2.0
    :run       genl-edge-under-no-rule-above}

   {:name      :edge-stratification-walk
    :claim     "a genl edge's stratification walk is flat in the spec closures its rules read"
    :sizes     [4 64]
    :max-ratio 2.0
    :run       edge-stratification-walk}

   {:name      :edge-stratification-unreached
    :claim     "a genl edge's stratification walk is flat in the excepted rules it does not reach"
    :sizes     [8 128]
    :max-ratio 2.0
    :run       edge-stratification-unreached}

   ;; The two taxonomy-edge checks, and their bounds are `clash-arbitration`'s reasoning
   ;; applied to the workload that file could not see: Ω(standing) is the floor —
   ;; a settle republishes the whole standing set whatever moved it — and what the bound
   ;; separates is *bookkeeping per standing pair* from *a re-derivation per standing
   ;; pair*.
   ;;
   ;; The baseline is **8**, and that is the header's own advice taken twice.  At 25 the
   ;; baseline of the `genlCx` check already carried 25 pairs' worth of the
   ;; re-derivation being measured, which divided out and left a defective engine reading
   ;; between 10.9x and 21.2x depending on which way the small reading bounced — a gate
   ;; that would have passed the very shape it exists to catch, roughly one run in four.
   ;; Eight is a size at which the re-derivation has barely started.
   ;;
   ;; **These two bounds are set from a full run, not from an isolated one, and the gap is
   ;; large enough to be stated here.**  Everything here is Ω(standing) by construction,
   ;; so the reading is `a + b·n` and the *ratio* is decided by how big the fixed term `a`
   ;; is at the baseline — which is JIT warmth, and by the twentieth check of a run the
   ;; JVM is much warmer than it is on `--only`.  The large reading barely moves (it is
   ;; real per-pair work, which no amount of warmth removes) and the small one drops by a
   ;; third, so the ratio climbs: the `genl` check reads 5.6x to 28x alone as the small
   ;; reading bounces, and a median of 26.6x in place.  Bounds read off an `--only` run
   ;; would fail every full one, which is the mirror image of the warming bias `measure`
   ;; describes and lands on the same rule: judge a check where it runs.
   ;;
   ;; Measured at 100x the standing set.  Most of the per-pair term is each reader deciding
   ;; every standing pair it sees again once the edge moves `res/withdrawal-stamp`
   ;; (docs/nmtms.md, "Where the scaling arguments hold").  A `genl` edge at n=800 costs
   ;; 3.3-4.1 ms a write, and a `genlCx` edge 2.2-2.8 ms.
   ;; Healthy, the `genl` check reads 17.1-22.7x alone and 17.0x and 23.9x in two full
   ;; runs; the `genlCx` check reads 14.9-28.9x alone and 21.4x and 28.5x in full runs,
   ;; under load averages of 10 to 31.  With every standing pair re-derived on the `genl`
   ;; generation the `genl` check reads 54.2x, 69.2x and 96.1x, 50 to 76 ms a write.
   ;; The defect's small reading already carries eight pairs' re-derivation, which is why
   ;; its ratio is a fifth of its ten-fold absolute cost.  35x sits half again above the
   ;; worst healthy `genl` reading and under every defective one; 32x sits above the
   ;; worst healthy `genlCx` reading (28.9x).  A ratio near 1x needs a settle that
   ;; keeps each standing pair's decision, which this file does not measure yet.
   {:name      :taxonomy-edge-arbitration
    :claim     "a genl edge separating nothing costs under 35x per write at 100x the standing clashes"
    :sizes     [8 800]
    :max-ratio 35.0
    :run       taxonomy-edge-arbitration}

   {:name      :context-edge-arbitration
    :claim     "a genlCx edge reaching nothing costs under 32x per write at 100x the standing P/¬P dilemmas"
    :sizes     [8 800]
    :max-ratio 32.0
    :run       context-edge-arbitration}

   ;; **The gate, and the sweep it gates, as two rows.**  A `functional` mark descends a
   ;; `genl` edge to the subtree below it, so the edge implicates that subtree's facts;
   ;; `genl` is the commonest edge an ontology writes, so the arm is gated on a mark being
   ;; at or above the edge's own `sub`.
   ;;
   ;; Gated: the gate removed — opened on this workload's own predicate, implemented and
   ;; measured rather than supposed — reads **4.33x** on a full run.  Healthy is flat, and
   ;; **the bound is 2.5x rather than the flat claim's 2.0x because of the spread rather
   ;; than the claim**: the readings here are a few tenths of a millisecond, which is where
   ;; run-to-run warmth moves a ratio more than the cost does.  Three isolated runs land
   ;; between 0.83x and 0.90x and two full runs read 1.09x apiece, and on a busier box the same tree
   ;; has read 1.85x — the difference being a baseline the gate measures warm.  2.5x sits above that spread and
   ;; at 1.6x under the defect; `--tolerance` is the answer to a red run on a busy box, and
   ;; the runner's re-measure already gives a bounced baseline a second look.
   {:name      :constraint-genl-edge-gate
    :claim     "a genl edge under no functional or asymmetric mark is flat in the subtree it does not walk"
    :sizes     [250 2000]
    :max-ratio 2.5
    :run       (constraint-genl-edge false 4096)}

   ;; ...and the sweep the gate lets through, which is budgeted rather than free: healthy
   ;; 0.98x and 1.03x on full runs, 0.76x alone, with the cap at 100, against **7.01x** with
   ;; the cap above n, as the shipped 8192 is, where 2,000 facts sit under the cap and the reading is the subtree instead — the same reading
   ;; `constraint-exposure-context-edge` records for its own budget, and the same argument.
   ;; The two rows fail for opposite reasons: this one if the sweep stops being bounded,
   ;; the one above it if the sweep stops being gated.  The bound is the flat claim's 2.0x,
   ;; which this one can carry: the capped sweep is a constant few tenths of a millisecond
   ;; on top of the flip, and a reading with more in it bounces less.
   {:name      :constraint-genl-mark-descent
    :claim     "past the instance cap, 8x the facts a descending mark reaches costs the same"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       (constraint-genl-edge true 100)}

   ;; **The bound is 175x, and here is what it was read off.**  Two healthy full-run
   ;; readings, 85.4x and 80.9x, against a floor near 66x — so a healthy reading sits
   ;; about 1.25x above the floor and the spread between runs is a few percent.  Below it,
   ;; the form the claim rules out: `contradictions` filtering the standing set by cross
   ;; product before ranking it reads **937.8x**, which is the square arriving exactly
   ;; where the paragraph below says it does.  175x is 2.05x above the worse healthy
   ;; reading and 5.4x below the defective one, which is the same slack the arbitration
   ;; bounds beside it carry.  Both numbers come off a **full** run rather than an
   ;; `--only` one, for the reason the namespace docstring gives.
   ;;
   ;; That the defective shape read 937.8x is also why a placeholder is not a gate: it
   ;; passed, silently, under the 1000x that meant "nobody has measured this".
   ;;
   ;; The read path of the standing set, and one of the two workloads here whose reading
   ;; grows with n by construction (`quality-report-scaling` is the other): a reading
   ;; returns every standing pair, so it costs the answer's own size and 32x the
   ;; dilemmas is at least 32x the reading.  Ordering them adds the
   ;; log term, which puts the floor between these two sizes near 66x rather than
   ;; 32x — so the bound is a claim about what sits **above** the floor.  A read that
   ;; re-derives the pairing, filters the standing set by cross product, or rebuilds each
   ;; report from the store per call is super-linear, and separates from the floor by the
   ;; square rather than by a constant.
   ;;
   ;; The sizes are `negation-arbitration`'s over the identical KB shape, so the two are
   ;; the write cost and the read cost of one standing set and can be quoted against each
   ;; other — the comparison the ordering's placement rests on.  The header's advice about
   ;; a small baseline lands differently here and is still followed: what a large baseline
   ;; would divide out of this ratio is not a per-pair term (the per-pair term is the whole
   ;; reading) but the fixed cost of the call, and at 25 pairs that is already small.
   ;;
   ;; **What a ratio cannot see here**, since a green run should not be read as more than
   ;; it is: `nm/sort-by-content-key` builds the key once per report, a *constant*
   ;; factor over building it per comparison, and both shapes are n log n, so this is
   ;; blind to losing it.  And the regression that
   ;; puts the ordering back on the settle path is a **write**-path cost: it lands on
   ;; `negation-arbitration` and not here.
   {:name      :standing-clash-reading
    :claim     "a reading of the standing dilemmas costs what it returns — an ordering of the standing set, not a re-derivation of it"
    :sizes     [25 800]
    :max-ratio 175.0
    :run       standing-clash-reading}

   ;; **Flat, and calibrated from both ends** as the header requires. Healthy it reads
   ;; **0.91x and 0.90x** on full runs (0.74x under `--only`): the answer set is one fact
   ;; at both sizes and a roster lookup does not care how much the roster holds. The shape
   ;; this exists to catch — the filter re-deriving the hidden set per call, a walk over
   ;; every stored `except` — reads **27.33x**, measured by running this check against a
   ;; tree that has it rather than by supposing a number for it.
   ;;
   ;; The bound is the flat claim's own 2.0x, which is where the header puts a cost that
   ;; should not move with n at all, and it sits an order of magnitude under the defect
   ;; and twice the healthy spread. The defect's reading is an `--only` one and so if
   ;; anything understates it: a full run's warmer baseline divides a smaller number into
   ;; the same large one.
   ;;
   ;; The small size is 8 rather than 25 for the header's reason: at 25 excepts a walk is
   ;; already carrying enough per-except cost to divide some of itself out of the ratio.
   {:name      :visibility-reading
    :claim     "a scoped read costs what it returns, not what the KB's excepts hide"
    :sizes     [8 1024]
    :max-ratio 2.0
    :run       visibility-reading}

   ;; The reader fan a `genlCx` edge sweeps.  Flat by construction: the bystanders read
   ;; the candidates' branch and sit under no `sub`, so the edge changes no ancestor set
   ;; of theirs and the widened set is the same size at both n.  The shape this exists to
   ;; catch is the one that shipped — the sweep taking `context-down` of each candidate's
   ;; own storage context rather than of `sub`, which put every bystander in the fan at
   ;; one derivation per candidate apiece.
   ;;
   ;; **Calibrated from both ends**, at the two readings that bracket it.  Healthy it
   ;; reads **1.02x** under `--only` (2.012 ms/op against 2.048) and **1.52x** on a full
   ;; run (1.370 against 2.088) — the header's warmer-baseline gap, which shows here
   ;; because the small size's own reading is small.  Against the defect, measured on a
   ;; worktree at the parent commit, it reads **15.51x** (2.996 ms/op against 46.456).  So
   ;; 3.0 is twice the healthy spread and five times under the defect, which is
   ;; `visibility-reading`'s rule for the same shape.  A bound at 2.0 would sit 24% over
   ;; a full run's healthy reading, which is the margin `inherit-reach-memo` lives on and
   ;; the reason it is the one check here that flakes.
   ;;
   ;; `genlcx_sweep_cost_test` counts the same fan in the suite, exactly and with no
   ;; tolerance, and `genlcx_sweep_test` holds what the sweep must still derive.
   {:name      :genlcx-edge-reader-fan
    :claim     "a genlCx edge costs the readers it widened, not every reader below its candidates"
    :sizes     [8 512]
    :max-ratio 3.0
    :run       genlcx-edge-reader-fan}

   ;; **The only check here that writes to a disk**, and the first thing in this file to
   ;; measure the durable stores at all.  Flat, and calibrated from both ends.  Healthy it
   ;; reads **1.06x** on a full run (0.113 ms/op against 0.120) and 0.94x, 0.97x, 0.82x,
   ;; 0.87x and 1.00x across five isolated ones: the per-record cost is fixed by
   ;; construction — one log frame and one idx slot per record, one packed append for a
   ;; whole WAL batch — so nothing about it is entitled to grow with what the log already
   ;; holds, and the header's warning about a warmer baseline in the full run barely
   ;; applies to a reading with no n-dependent term in it.  Below it, the form the check
   ;; exists to catch: the index WAL logging the resulting **value** instead of the op, so
   ;; an `:add-to-set` frame carries the grown set rather than the one added member and a
   ;; linear load writes a quadratic number of bytes.  Implemented against this very
   ;; workload rather than supposed for it, it reads **6.38x** (0.442 ms/op against
   ;; 2.816).  2.0x is the flat claim's own bound, at twice the worst healthy reading and
   ;; a third of the defect.
   ;;
   ;; **What the span does not separate**, since the readings are tenths of a millisecond
   ;; and a green run should not be read as more than it is: an append that finds the
   ;; log's end by walking the frame-length chain instead of asking the file its length
   ;; reads **1.77x** over this 8x span — a real linear term, but one whose per-record
   ;; share at 8,000 frames is still small next to the frame write, so it passes.  The
   ;; span is 8x rather than 32x because 32,000 durable asserts is half a minute of the
   ;; gate's five, which is a large price for widening one bound.
   ;;
   ;; The counted companion is `test/vaelii/disk_write_cost_test.clj`, and it is the half
   ;; that holds the *constant* — how many file operations a record costs — for the reason
   ;; the header gives about `assert_cost_test`: the syscall packing this path was built
   ;; for is a constant, and a constant divides out of every ratio in this file.
   {:name      :durable-fact-append
    :claim     "a fact reaching the durable log is flat in what the log already holds — the index WAL logs the op, not the grown value"
    :sizes     [1000 8000]
    :max-ratio 2.0
    :run       durable-fact-append}

   ;; The pair of claims docs/qcn.md's cost section opens with, and the one this file can
   ;; hold: **the read is not the pass**.  The pass is superquadratic and says so; what
   ;; residency promises is that a *repeat* consultation costs what the answer costs and
   ;; not what the KB holds.  8x the stored extent of the calculus predicate, none of it
   ;; visible from the asking context, and the reading may not follow it.
   {:name      :qcn-network-residency
    :claim     "a repeated qualitative consultation is flat in the stored extent of the calculus it is not about"
    :sizes     [250 2000]
    :max-ratio 2.0
    :run       qcn-network-residency}

   ;; A baseline, no bound: the load is super-quadratic by design today (docs/qcn.md,
   ;; "Cost at load, measured").  Measured 2026-09-28 under a load average near 14: 2.471
   ;; -> 23.116 ms a fact under `--only` (9.35x), and 2.739 / 3.453 / 20.155 ms over 20 /
   ;; 40 / 80 regions in a warm JVM.  The change that flattens the per-fact curve gives
   ;; this check a bound read off both ends.
   {:name      :qcn-chain-load
    :claim     "an arriving fact of a containment chain, with a forward rule over the calculus, per 4x the regions"
    :sizes     [20 80]
    :run       qcn-chain-load}

   ;; What grows here is the join's own read of the chain's network, linear in its facts,
   ;; and not the firings.  Measured 2026-09-28 under a load average near 14: 1.868 /
   ;; 1.878 / 1.786 -> 3.898 / 4.641 / 4.157 ms (2.09x, 2.47x, 2.33x) with the delta
   ;; comparing the chain's closed pairs, 1.53x and 1.40x with the equal read kept
   ;; resident, where a settle re-deciding every standing firing reads 4.027 -> 22.379 ms
   ;; (5.56x), about 2.3 µs a firing.  3.5x sits between the firings and the rest.
   {:name      :qcn-arrival-over-standing-firings
    :claim     "an arriving spatial fact over a satisfiable network, per 68x the standing firings of a rule on the calculus"
    :sizes     [16 128]
    :max-ratio 3.5
    :run       qcn-arrival-over-standing-firings}

   ;; A baseline, no bound: the re-check an exception answered by composition owes takes
   ;; every firing of its rule on every arrival that moves the calculus (docs/exceptions.md,
   ;; "Five channels"), so the arrival is linear in the firings and a load of such facts
   ;; beside such a rule quadratic.  Measured 2026-09-28 under a load average near 25:
   ;; 1.515 -> 3.205 and 1.257 -> 2.756 ms (2.12x, 2.19x), where an arrival that queued
   ;; the rule for nothing read 0.453 -> 0.741 ms.  About 13 µs a firing.
   {:name      :qcn-arrival-over-composed-exceptions
    :claim     "an arriving spatial fact, per 8x the standing firings of a rule excepted on a relation the calculus composes"
    :sizes     [16 128]
    :run       qcn-arrival-over-composed-exceptions}

   ;; The pair-by-pair delta against the read.  Measured 2026-09-28 under a load average
   ;; near 20: 1.550 -> 2.797 ms (1.80x) with the equal read kept resident, 1.677 ->
   ;; 7.176 ms (4.28x) with the delta comparing the n(n-1) closed pairs.
   {:name      :qcn-arrival-beside-an-unmoved-network
    :claim     "an arriving spatial fact in a sibling context, per 6x the regions of a standing network it does not move"
    :sizes     [32 192]
    :max-ratio 2.5
    :run       qcn-arrival-beside-an-unmoved-network}

   ;; Not a flat claim, and the bound says which claim it is instead.  `undercut?` is a
   ;; cross-product over the claims however the reaches are answered, so the comparing is
   ;; quadratic in n whatever happens — what the memo makes linear is the *walking*, and 8x
   ;; the claims at 64x the cost is what a lost memo reads.  12x sits between the two, the
   ;; same reasoning `membership-under-depth` picks its bound by.
   {:name      :inherit-reach-memo
    :claim     "8x the claims reaching one term costs under 12x per ask — one reach walk per question, not one per pair of claims"
    :sizes     [8 64]
    :max-ratio 12.0
    :run       inherit-reach-memo}

   ;; The route search beside the reach walk above.  `undercut?`'s cross-product is not in
   ;; this one — the goal carries a single claim — so what n grows is the number of routes
   ;; the witness search chooses between, and a search that compared whole routes rather
   ;; than settling each node once reads 8x the routes at 64x the cost.  12x sits between
   ;; the two, for the reason the check above picks the same number.
   {:name      :witness-route-search
    :claim     "8x the routes between two terms costs under 12x per preservation support — each node settled once, not each route compared"
    :sizes     [8 64]
    :max-ratio 12.0
    :run       witness-route-search}

   ;; The re-derivation a withdrawn edge owes a reader that still reaches is read on every
   ;; settle pass while the edge stays withdrawn, so its cost is paid per write rather than
   ;; per withdrawal.  Linear in the withdrawn edges is the claim: 8x of them at 8x the scan is
   ;; one check per withdrawn firing, and 64x is a scan that compares them pairwise or
   ;; re-derives what it already re-derived.  20x sits between the two, as the bounds
   ;; above sit between their linear and quadratic readings.
   {:name      :lost-firing-scan
    :claim     "8x the edges a reader below their context takes OUT costs under 20x per settle's lost-firing scan — one check per withdrawn firing, nothing re-derived twice"
    :sizes     [8 64]
    :max-ratio 20.0
    :run       lost-firing-scan}

   ;; The metric twin of the qualitative residency check above, and the bound is calibrated
   ;; the way `membership-under-depth` and `inherit-reach-memo` are: from both ends, on full
   ;; runs.  A closure bounds every pair of instants, so an arriving constraint is quadratic
   ;; in the instant count whatever route it takes and no memo makes it flat — what the gate
   ;; defends is that the route is a **relaxation** and not a fresh cubic pass.  At 8x the
   ;; instants it reads 12.6x-13.4x over three full runs, and 99.5x with the same check
   ;; driving `stp/close-state` instead, which is the form the bound exists to catch.
   ;; 35x sits between, and the absolute readings say it louder: 1.9 ms an arrival
   ;; against 101 ms.
   ;; Without `inherit/crossing-claim?` every `genl` edge re-joins the rule of every
   ;; predicate preserved along `genl`: 6.7x here, 2.3 ms against 15.3 ms an arrival.
   ;; With it an arrival re-joins its own chain's rule and reads the slot roster once per
   ;; closure term, and reads 0.99x.  4x sits between.
   {:name      :genl-defeat-rejoin
    :claim     "8x the predicates preserved along genl costs under 4x per arriving genl denial — it re-joins the rules whose claims cross the edge, not every one"
    :sizes     [8 64]
    :max-ratio 4.0
    :run       genl-defeat-rejoin}

   ;; Calibrated from both ends, as `genl-defeat-rejoin` is.  With the narrowing reading
   ;; one argument root per declaration per closure term it grows 8.1x here, 2.9 ms against
   ;; 23.4 ms a batch of twenty; read from the closure's terms, with the declarations
   ;; looked up by relation, it reads 0.57x.  3x sits between.
   {:name      :genl-crossing-many
    :claim     "8x the predicates preserved along genl costs under 3x per genl denial's narrowing — the reads start from the edge's closure, not from the declarations"
    :sizes     [64 512]
    :max-ratio 3.0
    :run       genl-crossing-many}

   ;; The same narrowing with no cap on the closure grows 11.2x, 65 ms against 727 ms a
   ;; batch of ten; past `inherit/crossing-closure-cap` it reads 0.72x, 1.1 ms against
   ;; 0.8 ms.  3x sits between.
   {:name      :genl-crossing-wide
    :claim     "8x the subtypes below a genl edge costs under 3x per edge's narrowing — a closure past the cap moves every predicate off the declarations, with no read per term"
    :sizes     [600 4800]
    :max-ratio 3.0
    :run       genl-crossing-wide}

   {:name      :metric-closure-warm-start
    :claim     "8x the instants costs under 35x per arriving constraint — the closure is relaxed into, not run again"
    :sizes     [50 400]
    :max-ratio 35.0
    :run       metric-closure-warm-start}

   ;; The four below are calibrated from both ends in one warm JVM per revision, under a
   ;; load average of 10 to 17 from other suites; a full run is the reading to hold them to.
   ;;
   ;; Healthy 0.86x warm and 2.28x as the first check of a fresh JVM (0.63 ms against
   ;; 1.44).  With every assert re-ordering every sibling pair it reads 154.51x (4.16 ms
   ;; against 642.07).  3x is the reader fan's bound for the same reason.
   {:name      :context-nat-existing-context
    :claim     "16x the sibling contexts costs under 3x per fact written into an existing context NAT"
    :sizes     [16 256]
    :max-ratio 3.0
    :run       context-nat-existing-context}

   ;; Not flat: a rebuild reads every sign fact, so the reading grows with the chain.
   ;; Healthy 23.94x, 37.75x, 40.74x and 49.98x for 32x the links.  A round-robin fixpoint
   ;; with a copied support set reads 331.39x (0.25 ms against 83.12).  100x is twice the
   ;; worst healthy reading and a third of the defective one.
   {:name      :sign-chain-rebuild
    :claim     "32x the links of a sign chain costs under 100x per ask after a write — the rebuild is linear in the sign facts, not quadratic"
    :sizes     [25 800]
    :max-ratio 100.0
    :run       sign-chain-rebuild}

   ;; Healthy 0.82x warm and 1.74x cold.  Classifying every dilemma per ask reads 11.98x
   ;; (31.29 ms against 374.93 a batch).
   {:name      :brave-ask-between-writes
    :claim     "10x the standing dilemmas costs under 3x per brave/cautious ask with no write between"
    :sizes     [100 1000]
    :max-ratio 3.0
    :run       brave-ask-between-writes}

   ;; Healthy 0.84x and 0.98x.  Reading the parent's spec closure per edge reads 3.11x
   ;; (0.60 ms against 1.86); the separation is narrower than the others' because the
   ;; closure walk is cheap per member, and the claim is the ordinary flat bound.
   {:name      :sibling-disjoint-new-spec
    :claim     "16x the members of a sibling_disjoint clique costs under 2x per genl edge into it"
    :sizes     [256 4096]
    :max-ratio 2.0
    :run       sibling-disjoint-new-spec}

   ;; Both ends measured in one warm JVM, 2026-09-29.  Above: 1.37x and 1.12x (0.23 ms
   ;; against 0.26).  Below, the arrival reading the marked predicate's extent, the sweep
   ;; the late-mark report took before a reader decided the nogood, reads 25.12x (1.02 ms
   ;; against 25.71).  3x is about twice the worse healthy reading.
   {:name      :irreflexive-mark-arrival
    :claim     "32x the ordinary tuples of a predicate costs under 3x per irreflexive mark arriving over it and read through — no tuple is swept"
    :sizes     [256 8192]
    :max-ratio 3.0
    :run       irreflexive-mark-arrival}

   ;; Measured 2026-09-30 under a load average of 6 to 11.  Above: 0.84x, 0.82x and 0.76x
   ;; (0.33 ms per write at 1024).  Below, every reader holding a withdrawn handle read
   ;; again on each write, the window reads 16.6 ms at 64 and 224 ms at 256 (13.46x for 4x
   ;; the readers), and did not finish the 1024 end in 28 minutes.
   {:name      :verdict-window-write
    :claim     "8x the readers holding a withdrawn consequence costs under 2x per tuple a reader convicts at its own context"
    :sizes     [128 1024]
    :max-ratio 2.0
    :run       verdict-window-write}

   {:name      :membership-declaration-arrival
    :claim     "32x the memberships under the two types a disjoint declaration separates costs under 2x per declaration arriving over them and read through — no membership is swept"
    :sizes     [256 8192]
    :max-ratio 2.0
    :run       membership-declaration-arrival}

   ;; Both ends measured in one warm JVM, 2026-09-29.  Above: 1.00x and 1.03x (0.38 ms per
   ;; thousand reads).  Below, the reader's losers recomputed on every read, the cache
   ;; emptied before each, reads 36.48x.
   {:name      :decided-warm-read
    :claim     "32x the self tuples a mark convicts costs under 2x per warm read of one at its reader"
    :sizes     [64 2048]
    :max-ratio 2.0
    :run       decided-warm-read}

   ;; Both ends measured 2026-10-01.  Healthy 0.89x (1.076 ms against 0.954).  With every
   ;; candidate tuple's record read and its functor's binding asked per tuple, 3.86x
   ;; (1.269 ms against 4.894).  2.0 is the file's bound for a flat claim.
   {:name      :held-shape-first-withdrawal
    :claim     "16x the candidate tuples a reader's own binding holds, beside 200 decided self tuples, costs under 2x per reader's first withdrawal"
    :sizes     [400 6400]
    :max-ratio 2.0
    :run       held-shape-first-withdrawal}

   ;; Both ends measured 2026-09-30 under a load average of 10 to 14.  Healthy 0.68x (0.44
   ;; ms against 0.30).  With every pair in two contexts found and recorded as standing by
   ;; each settle, the reading is 3.01x (3.67 ms against 11.06).  2x sits between the two.
   ;; With the lost-firing scan reading every candidate on each settle pass, 1.6x-1.85x
   ;; (0.45 ms against 0.80); scoped to the readers a move reaches, 0.72x-0.91x.
   {:name      :negation-reader-write
    :claim     "8x the negation pairs a reader decides costs under 2x per unrelated assert"
    :sizes     [100 800]
    :max-ratio 2.0
    :run       negation-reader-write}

   ;; Healthy 1.05x (0.29 ms per thousand reads); the standing-pair shape reads 1.01x too,
   ;; so this holds the claim and separates nothing from the write check above.
   {:name      :negation-reader-warm-read
    :claim     "8x the negation pairs a reader decides costs under 2x per warm read of a member at that reader"
    :sizes     [100 800]
    :max-ratio 2.0
    :run       negation-reader-warm-read}

   ;; Both ends measured 2026-09-30.  Healthy 0.81x-1.01x (0.24 ms against 0.21-0.24),
   ;; the unmarked twin's 0.22-0.24 ms at 32768.  With the functional checks reading the
   ;; slot `(P a b ?v)` by intersecting the two hubs' argument roots it reads 2.78x-3.05x
   ;; (0.23 ms against 0.65-0.74), and with the determinant read scanning one argument
   ;; root 7.53x.  Before the determinant read, a tuple swept the marked predicate's
   ;; extent to the instance budget, and a run at 32768 does not finish in 15 minutes.
   {:name      :tuple-mark-determinant-write
    :claim     "32x the tuples under a last-position functionalInArg mark costs under 2x per tuple arriving on a determinant of its own"
    :sizes     [1024 32768]
    :max-ratio 2.0
    :run       tuple-mark-determinant-write}

   ;; Healthy 1.12x (0.75 ms per thousand reads); the standing-pair shape reads 1.03x too,
   ;; so this holds the claim and separates nothing from the write check above.
   {:name      :tuple-mark-warm-read
    :claim     "8x the functional pairs a reader decides costs under 2x per warm read of a member at that reader"
    :sizes     [100 800]
    :max-ratio 2.0
    :run       tuple-mark-warm-read}])

;; ---- the runner ---------------------------------------------------------

(def ^:private quick-slack
  "How much `--quick` widens each bound.  One attempt over the real pair is noisier
  than the gate's re-measured best-of-two, so the bound gives that noise room — a
  borderline reading passes where the full gate would look twice, and a genuine
  regression still fails."
  1.5)

(defn- run-check
  "Measure one check at both sizes and judge the growth.  A check over its bound is
  measured again from scratch and the *better* ratio stands: a GC pause or a scheduler
  hiccup landing in one window is not a regression, and an algorithmic one survives being
  looked at twice.  A baseline (no `:max-ratio`) is measured once and not judged."
  [{:keys [sizes max-ratio run]} tolerance quick?]
  (let [[small large] sizes
        ;; the *large* size is what both warm to: it is the one whose reading the bound
        ;; is a claim about, so it is the one that must not be measured warmer than its
        ;; baseline was
        attempt (fn [] (let [a (measure run small large)
                             b (measure run large large)]
                         {:small a :large b :ratio (/ b (max a 1.0))}))]
    (if (nil? max-ratio)
      (assoc (attempt) :sizes [small large] :status :baseline)
      (let [;; quick widens the bound instead of shrinking the pair: one attempt over the
            ;; real sizes is a coarse verdict, where measuring one size twice is six runs
            ;; and no possible failure — a gate that cannot fail is decoration
            bound     (* (double max-ratio) (double tolerance) (if quick? quick-slack 1.0))
            first-try (attempt)
            best      (if (or quick? (<= (:ratio first-try) bound))
                        first-try
                        (min-key :ratio first-try (attempt)))]
        (assoc best
               :bound  bound
               :sizes  [small large]
               :status (cond (< (:small best) noise-floor-ns) :noise
                             (<= (:ratio best) bound)         :pass
                             :else                            :fail))))))

(defn- report [{:keys [name claim]} {:keys [small large ratio bound sizes status]}]
  (let [[s l] sizes]
    (println (format "  %-20s %s" (clojure.core/name name)
                     (case status
                       :pass     "PASS"
                       :fail     "FAIL"
                       :noise    "noise — below the gating floor, not judged"
                       :baseline "baseline — measured, not judged")))
    (println (format "    %s" claim))
    (println (format "    n=%-6d %8.3f ms/op        n=%-6d %8.3f ms/op"
                     s (/ small 1e6) l (/ large 1e6)))
    (case status
      :noise    nil
      :baseline (println (format "    growth %.2fx  (no bound)" ratio))
      (println (format "    growth %.2fx  (bound %.2fx)" ratio bound)))
    (println)))

(defn- usage-exit [msg]
  (binding [*out* *err*]
    (println msg)
    (println "usage: lein perf [--only <name>] [--tolerance <x>] [--quick] | --list"))
  (System/exit 2))

(defn- parse-args [args]
  ;; refused, not guessed: `--only` with no value would run the WHOLE gate while
  ;; reading as a single-check run, a dropped unknown flag gates at the default
  ;; tolerance (`--tolerence 1.5` at 1.0), and a bare `--tolerance` NPEs — which
  ;; gate.sh reports exactly like a regression
  (loop [m {:tolerance 1.0 :quick? false :only nil :list? false} [a & more] args]
    (case a
      nil          m
      "--list"     (recur (assoc m :list? true) more)
      "--quick"    (recur (assoc m :quick? true) more)
      "--only"     (if-some [v (first more)]
                     (recur (assoc m :only (keyword v)) (rest more))
                     (usage-exit "--only needs a check name"))
      "--tolerance" (if-some [v (first more)]
                      (let [x (try (Double/parseDouble v)
                                   (catch NumberFormatException _
                                     (usage-exit (str "--tolerance: not a number: " v))))]
                        (recur (assoc m :tolerance x) (rest more)))
                      (usage-exit "--tolerance needs a number"))
      (usage-exit (str "unknown flag: " a)))))

(defn -main [& args]
  (let [{:keys [tolerance quick? only list?]} (parse-args args)
        selected (cond->> checks only (filter #(= only (:name %))))]
    ;; `--list` prints each check's name and claim and measures nothing
    (when list?
      (doseq [{:keys [name claim]} checks]
        (println (format "%-40s %s" (clojure.core/name name) claim)))
      (System/exit 0))
    (when (empty? selected)
      (println "no such check:" only "— have:" (mapv :name checks))
      (System/exit 2))
    (println (format "\nvaelii performance gate — %d check(s), tolerance %.2fx%s\n"
                     (count selected) (double tolerance) (if quick? ", quick" "")))
    (let [total   (count selected)
          ;; Every verdict is reported together at the end (below), so the run itself
          ;; emits nothing per check — a `perf-progress k/total name` marker on *err*
          ;; as each finishes gives `lein gate` something to poll into a live bar
          ;; (scripts/gate.sh) without touching the clean stdout verdict stream.
          results (doall
                   (map-indexed
                    (fn [i c]
                      (let [r (run-check c tolerance quick?)]
                        (binding [*out* *err*]
                          (println (format "perf-progress %d/%d %s"
                                           (inc i) total (name (:name c))))
                          (flush))
                        [c r]))
                    selected))]
      (doseq [[c r] results] (report c r))
      (let [failed (filter (fn [[_ r]] (= :fail (:status r))) results)]
        (if (seq failed)
          (do (println (format "%d of %d checks REGRESSED: %s"
                               (count failed) (count results)
                               (mapv (comp :name first) failed)))
              (shutdown-agents)
              (System/exit 1))
          (let [named (fn [st] (into [] (comp (filter (fn [[_ r]] (= st (:status r))))
                                              (map (comp :name first)))
                                     results))
                noisy (named :noise)
                bases (named :baseline)]
            ;; the floor's whole point: a check too fast to gate says so instead of
            ;; turning into a green light nobody notices has stopped meaning anything
            (println (format "%d check(s) ok%s%s"
                             (- (count results) (count noisy) (count bases))
                             (if (seq noisy)
                               (format ", %d below the gating floor — not judged: %s"
                                       (count noisy) noisy)
                               "")
                             (if (seq bases)
                               (format ", %d baseline(s) — not judged: %s"
                                       (count bases) bases)
                               "")))
            (shutdown-agents)
            (System/exit 0)))))))

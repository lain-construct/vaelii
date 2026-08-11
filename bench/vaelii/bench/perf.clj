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
  warmer than it is on the first.  `negation-arbitration` reads **5.40x under `--only`
  and 10.02x in the full run** on the same tree, and the split is entirely in the
  denominator — its n=25 baseline is 0.224 ms alone against 0.123 in place, while n=800
  barely moves (1.212 against 1.234).  So
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
            [vaelii.impl.checks :as checks]
            [vaelii.impl.columnar :as columnar]
            [vaelii.impl.dense-kv :as dense]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.overlay.frozen :as frozen]
            [vaelii.impl.overlay.kv :as okv]
            [vaelii.impl.plan :as plan]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]))

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

(defn- clash-arbitration
  "n individuals each holding two separated types, so the KB carries n standing dilemmas,
  and every assert settles against all of them.

  Runs under `checks/*arbitrate-constraints?*` because that is how a *standing* clash is
  built through `assert` at all — with it off the second membership is refused and the
  pair never exists.  The discovery it gates is the same one the derivation path runs
  unconditionally, so this measures the shipped default too."
  [n]
  (binding [checks/*arbitrate-constraints?* true]
    (let [kb (fresh-kb)]
      (v/assert kb '(disjoint pa_t pb_t) 'PerfContext {:strength :monotonic})
      (doall
       (for [i (range n)
             :let [x (symbol (str "PX" i))]]
         (do (v/assert kb (list 'pa_t x) 'PerfContext {})
             (nanos (v/assert kb (list 'pb_t x) 'PerfContext {}))))))))

(defn- defeasible-load
  "n facts arriving through one defeasible forward rule.  The rule fires per fact and the
  conclusion is placed at `:default`; what must not happen is the whole rule set — or the
  whole KB — being rescanned to decide that."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb (list 'set/defaultRule
                       (rules/rule-sentence ['(pbird ?x)] '(pflies ?x)))
              'PerfContext {:strength :monotonic})
    (doall
     (for [i (range n)]
       (nanos (v/assert kb (list 'pbird (symbol (str "PB" i))) 'PerfContext {}))))))

(defn- taxonomy-depth
  "n `genl` edges arriving parent-before-child down one chain.  Every edge pays a `wff`
  cycle check, and what keeps that flat is the topological depth potential — a check
  walking the closure instead would be linear in the chain already built."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(genl pt0_t thing) 'PerfContext {:strength :monotonic})
    (doall
     (for [i (range 1 (inc n))]
       (nanos (v/assert kb (list 'genl
                                 (symbol (str "pt" i "_t"))
                                 (symbol (str "pt" (dec i) "_t")))
                        'PerfContext {:strength :monotonic}))))))

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
        (v/assert kb (list 'genl (symbol (str "pfl" i "_t")) 'thing) 'PerfContext {})))
    (let [edge (list 'not (list 'genl (symbol (str "pfl" (quot n 2) "_t")) 'thing))]
      (doall
       (for [_ (range 120)]
         (nanos (let [h (v/assert kb edge 'PerfContext {:strength :monotonic})]
                  (v/retract! kb h))))))))

(defn- flat-cache-belief-flip
  "One `(disjoint a b)` declaration defeated and revived over and over, in a KB carrying n
  of them.

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
                  'PerfContext {})))
    (let [k    (quot n 2)
          decl (list 'not (list 'disjoint (symbol (str "pfd" k "a_t")) (symbol (str "pfd" k "b_t"))))]
      (doall
       (for [_ (range 120)]
         (nanos (let [h (v/assert kb decl 'PerfContext {:strength :monotonic})]
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
                  'PerfContext {:strength :monotonic})))
    ;; a hundred matches per reading: one is a few microseconds whatever n is, which is
    ;; the very result being gated — and a ratio between two readings that small is
    ;; timer jitter.  Batching moves the reading above the floor without changing what
    ;; it measures.
    (let [goal (list 'pRelOf '?x (symbol (str "PT" (quot n 2))))]
      (doall (for [_ (range 40)]
               (nanos (dotimes [_ 100] (doall (res/match-pattern kb goal 'PerfContext)))))))))

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
    (v/assert kb '(genl pdj_left thing)  'PerfContext {:strength :monotonic})
    (v/assert kb '(genl pdj_right thing) 'PerfContext {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range separated-types)]
        (v/assert kb (list 'genl (symbol (str "pdj_l" i)) 'pdj_left)
                  'PerfContext {:strength :monotonic})
        (v/assert kb (list 'genl (symbol (str "pdj_r" i)) 'pdj_right)
                  'PerfContext {:strength :monotonic}))
      (doseq [i (range n)]
        (v/assert kb (list 'genl (symbol (str "pdj_o" i "_t")) 'thing)
                  'PerfContext {:strength :monotonic})))
    (v/assert kb '(disjoint pdj_left pdj_right) 'PerfContext {:strength :monotonic})
    (doall (for [_ (range 60)]
             (nanos (dotimes [_ 10] (count (v/ask kb '(disjoint pdj_l0 ?t) 'PerfContext))))))))

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
    (v/assert kb '(transitive pBefore) 'PerfContext {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range 1 n)]
        (v/assert kb (list 'pBefore (nd (dec i)) (nd i)) 'PerfContext {:strength :monotonic})))
    (dorun (v/ask kb (list 'pBefore (nd 0) '?y) 'PerfContext))
    (let [goal (list 'pBefore (nd 0) (nd (dec n)))]
      (doall (for [_ (range 60)]
               (nanos (dotimes [_ 200] (v/ask? kb goal 'PerfContext))))))))

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
    (v/assert kb '(genl pm_a_t thing) 'PerfContext {:strength :monotonic})
    (v/assert kb '(genl pm_b_t thing) 'PerfContext {:strength :monotonic})
    (doall
     (for [i (range n)
           :let [x (symbol (str "PM" i))]]
       (do (v/assert kb (list 'pm_a_t x) 'PerfContext {:strength :monotonic})
           (nanos (v/assert kb (list 'pm_b_t x) 'PerfContext {:strength :monotonic})))))))

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

  Nothing here is a *definitional* clash, so `checks/*arbitrate-constraints?*` is
  irrelevant and the pairs are pure `negation-nogoods` business."
  [n]
  (let [kb (fresh-kb)]
    (doall
     (for [i (range n)
           :let [pr (symbol (str "pneg" i))
                 x  (symbol (str "PN" i))]]
       (do (v/assert kb (list pr x) 'PerfContext {})
           (nanos (v/assert kb (list 'not (list pr x)) 'PerfContext {})))))))

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
                        'PerfContext {}))))))

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
     kb (for [i (range n)] (list 'pcmp (symbol (str "PI" i)) 'PTHot)) 'PerfContext)
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
    (v/assert kb '(reifiableFunction PNatFn) 'UniverseContext {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'pNatUse (symbol (str "PNU" i))
                           (list 'PNatFn (symbol (str "PNA" i))))
                  'PerfContext {})))
    (let [victims (mapv (fn [i]
                          (v/assert kb (list 'pRetVictim (symbol (str "PRV" i)) 'PRVal)
                                    'PerfContext {}))
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
        sxs (mapv (fn [i] (sx/sentex (list 'pfan (symbol (str "PF" i))) 'PerfContext {}))
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
    (kv/kv-clear! base)
    (doseq [i (range n)] (kv/kv-add-to-set base [:functor-root 'povl] i))
    (let [own (mem/memory-kv-backend {:space [::ovfork]})
          _   (kv/kv-clear! own)
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
  positions are the shape that exercises `kv-intersect`.

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
    (kv/kv-clear! b)
    (doseq [i (range n)] (kv/kv-add-to-set b [:argument-root 'pint 2 'PIB] i))
    (doseq [i (range 4)] (kv/kv-add-to-set b [:argument-root 'pint 1 'PIA] (* 7 i)))
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

  The relations are 1:1 chains beside a small disconnected one, which is the shape that
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
                   'UniverseContext {:chain? false})
    (doall
     (for [_ (range 200)]
       (nanos (dotimes [_ 20] (plan/order kb q 'UniverseContext {})))))))

(defn- arity-reach-trigger
  "n **conforming** facts of a predicate whose arity was declared before any of them.

  `settle/report-arity-reach!` sweeps a predicate's whole extent, and the only thing that
  keeps that affordable is *what triggers it*: a declaration entering the moved region,
  never a fact.  So an ordinary fact arriving must cost the same at 2,000 as at 250, and
  mis-gating the pass to run on every settle — the easy mistake, since every other pass in
  `settle-finish` does — turns a linear load quadratic here and in no test.

  Conforming on purpose.  A load of *violating* facts would sweep once, at the
  declaration, and then measure the ordinary assert path anyway; what this has to separate
  is a pass that runs per fact from one that runs per declaration, and a conforming extent
  makes any sweep at all visible as growth rather than hiding inside a report."
  [n]
  (let [kb (fresh-kb)]
    (v/assert kb '(arity pReach 2) 'PerfContext {:strength :monotonic})
    (doall
     (for [i (range n)]
       (nanos (v/assert kb (list 'pReach (symbol (str "PR" i)) 'PRval) 'PerfContext {}))))))

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
  included because it is the shape that would re-run something: it has to filter the
  region rather than ask the KB again, and only a load says which it did."
  [n]
  (let [kb (fresh-kb)]
    (v/watch kb (fn [_] nil))
    (v/watch kb '(pFeed ?x ?y) 'PerfContext (fn [_] nil))
    (doall
     (for [i (range n)]
       (nanos (v/assert kb (list 'pFeed (symbol (str "PF" i)) 'PFval) 'PerfContext {}))))))

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
    (v/assert kb '(genl qual_thing thing) 'PerfContext {:strength :monotonic})
    (v/with-deferred-settle kb
      (doseq [i (range side), j (range side)]
        (v/assert kb (list 'pQual (symbol (str "QA" i)) (symbol (str "QB" j)))
                  'PerfContext {})))
    (doall (for [_ (range 60)] (nanos (v/kb-quality kb))))))

(defn- pctx [prefix i] (symbol (str prefix i "Context")))

(defn- retract-context-cycle-scaling
  "One `retract!` of a `genlContext` edge **inside a two-context cycle**, on a KB whose
  context graph holds n unrelated contexts beside it.

  Mutual visibility is a claim `genlContext` admits — two contexts see each other, and
  OpenCyc states it — so a context sits in a strongly connected component, and a
  deletion inside one can split it.  A split is the only edit that invalidates the
  component map, and the map is what `sees?` reads for its O(1) same-component answer,
  so it may not be left stale.  What the repair may cost is that component; what it may
  not cost is the graph around it, which is the claim measured here.

  `genl` cycles are refused by `wff`, so this reaches `genlContext` only — and no other
  check in this file builds a context cycle at all, which is exactly how a whole-relation
  repair per deleted cycle edge stayed invisible.

  One cycle per victim, because a handle can only be retracted once and a broken cycle
  cannot be broken again.  The unrelated contexts are the population held fixed: none of
  them is in any cycle, none is named by any retraction, and the count is the same at the
  last reading as at the first."
  [n]
  (let [kb (fresh-kb)]
    (v/with-deferred-settle kb
      (doseq [i (range n)]
        (v/assert kb (list 'genlContext (pctx "PcBg" i) 'PcTopContext) 'UniverseContext {}))
      (doseq [i (range retract-victims)]
        (v/assert kb (list 'genlContext (pctx "PcA" i) 'PcTopContext) 'UniverseContext {})
        (v/assert kb (list 'genlContext (pctx "PcB" i) (pctx "PcA" i)) 'UniverseContext {})))
    ;; the closing edges last and outside the batch: each settles, so the component map
    ;; is built and the relation is ranked before a single reading is taken
    (let [victims (mapv (fn [i]
                          (v/assert kb (list 'genlContext (pctx "PcA" i) (pctx "PcB" i))
                                    'UniverseContext {}))
                        (range retract-victims))]
      (doall (for [h victims] (nanos (v/retract! kb h)))))))


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
        (v/assert kb (list 'pMergeBorn (symbol (str "PMHi" i)) 'PMPlace) 'PerfContext {})
        (v/assert kb (list 'sameAs (symbol (str "PMAa" i)) (symbol (str "PMHi" i)))
                  'PerfContext {})))
    (let [victims (mapv (fn [i]
                          (v/assert kb (list 'pMergeVictim (symbol (str "PMV" i)) 'PMVal)
                                    'PerfContext {}))
                        (range retract-victims))]
      (doall (for [h victims] (nanos (v/retract! kb h)))))))

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
    (v/assert kb '(exceptWhen (not (pNegSkip ?x))
                              (set/defaultRule (implies (and (pNegProbe ?x)) (pNegSeen ?x))))
              'PerfContext {})
    (doseq [i (range n)]
      (v/assert kb (list 'pNegProbe (symbol (str "PNG" i))) 'PerfContext {}))
    (doall (for [i (range edge-writes)]
             (nanos (v/assert kb (list 'genl (symbol (str "pnegv" i "_t")) 'pnegtop_t)
                              'PerfContext {:strength :monotonic}))))))

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

  The dilemmas are built under one deferred settle: the standing set is the KB this
  measures against and not the thing being measured, and building it an assert at a time
  is the Ω(standing)-per-settle cost paid n times over."
  [n]
  (binding [checks/*arbitrate-constraints?* true]
    (let [kb (fresh-kb)]
      (v/assert kb '(disjoint pea_t peb_t) 'PerfContext {:strength :monotonic})
      (v/with-deferred-settle kb
        (doseq [i (range n)
                :let [x (symbol (str "PEX" i))]]
          (v/assert kb (list 'pea_t x) 'PerfContext {})
          (v/assert kb (list 'peb_t x) 'PerfContext {})))
      (doall
       (for [i (range edge-writes)]
         (nanos (v/assert kb (list 'genl (symbol (str "pev" i "_t"))
                                   (symbol (str "peu" i "_t")))
                          'PerfContext {:strength :monotonic})))))))

(defn- context-edge-arbitration
  "One `genlContext` edge — a fresh context under `UniverseContext`, with nothing below
  it — written on a KB carrying n standing P/¬P dilemmas, every one of them stated in a
  context the edge does not reach.

  The negation twin of the check above, and the same blind spot in the same place:
  `negation-arbitration` builds its standing set and writes no context edge afterwards.
  Joint visibility is read through the `genlContext` closure, so a memo retired on that
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
        (v/assert kb (list pr x) 'PerfContext {})
        (v/assert kb (list 'not (list pr x)) 'PerfContext {})))
    (doall
     (for [i (range edge-writes)]
       (nanos (v/assert kb (list 'genlContext (symbol (str "PCtx" i "Context"))
                                 'UniverseContext)
                        'PerfContext {:strength :monotonic}))))))

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

  A reading is `settle/ranked` over what the last settle published.  The stored vectors
  are in arrival order, so putting them in content order is what makes
  `(first (contradictions kb))` an answer about the knowledge rather than about which
  pair was typed first — and it is done at the read because a KB is written to far more
  often than it is read (`settle/record-clashes!` carries that measurement).  That moves
  the cost onto a path with no other check on it, which is what this is.

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
        (v/assert kb (list pr x) 'PerfContext {})
        (v/assert kb (list 'not (list pr x)) 'PerfContext {})))
    (doall
     (for [_ (range 60)]
       (nanos (dotimes [_ reads-per-clash-reading]
                (count (v/contradictions kb))))))))

(def checks
  ;; The one bound here that is not *flat*, and deliberately.  A settle republishes the
  ;; whole standing clash set, so its cost is Ω(standing) by construction and no memo
  ;; makes an assert free of what is standing.  What the gate defends is that the per-pair
  ;; term stays **bookkeeping** rather than a re-derivation of the checks, and the
  ;; measured separation says it does: 9.5x with both memos in place, 12.3x with the
  ;; report memo removed, 46.5x with the carry-forward removed as well — the shape that
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

   {:name      :flat-cache-belief-flip
    :claim     "defeating and reviving one disjoint declaration costs the same in a KB declaring 4000 of them as in one declaring 500"
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

   {:name      :disjoint-enumeration
    :claim     "an open disjointness goal is flat in the vocabulary it is not about"
    :sizes     [500 4000]
    :max-ratio 2.0
    :run       disjoint-enumeration}

   {:name      :compound-probe
    :claim     "100 find-sentexes on a compound are flat in the extent of the hot atom it names"
    :sizes     [1000 32000]
    :max-ratio 2.0
    :run       compound-probe}

   ;; The negation twin of `clash-arbitration`, and the same reasoning picks its numbers:
   ;; Ω(standing) is the honest floor (a settle republishes the whole set), the baseline is
   ;; small enough that almost nothing is standing at it, and the bound separates
   ;; bookkeeping-per-pair from re-derivation-per-pair.  Re-deriving every standing pair
   ;; per settle round measured 38.9x here — the shape that shipped, and the one `:opposed`
   ;; was believed to have removed.  It removed a different one: the *scan of every stored
   ;; negation*, which is the commoner workload and is what `negation-load` below still
   ;; holds flat.  Neither check subsumes the other, and only both together say the pass is
   ;; not paying for the standing set (see docs/nmtms.md).
   ;;
   ;; This is the check the header's cold/warm gap was measured on, and the one most
   ;; exposed to it: 25 standing dilemmas is ~0.02 ms of per-pair cost under ~0.10 ms of
   ;; constant, so the baseline is four-fifths a reading of the constant.  Read a passing
   ;; `--only` here as a cold reading and nothing more.
   {:name      :negation-arbitration
    :claim     "32x the standing P/¬P dilemmas costs under 12x per assert — bookkeeping, not a re-derivation each"
    :sizes     [25 800]
    :max-ratio 12.0
    :run       negation-arbitration}

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

   {:name      :plan-scaling
    :claim     "planning one fixed conjunction is flat in the size of the KB it is planned against"
    :sizes     [1000 32000]
    :max-ratio 2.0
    :run       plan-scaling}

   ;; The bound is 4x rather than 2x because the vocabulary itself grows here — 8x the
   ;; sentexes is 2.8x the terms, and the report is entitled to that much.  What it
   ;; separates is 2.8x from the 8x a record scan reads, and 4x sits between them with
   ;; room on both sides.
   {:name      :quality-report-scaling
    :claim     "kb-quality grows with the vocabulary, not with what the KB stores"
    :sizes     [4000 32000]
    :max-ratio 4.0
    :run       quality-report-scaling}

   ;; The baseline is 64 for `clash-arbitration`'s reason: a retraction's own fixed cost
   ;; — the storage teardown, the settle, the feed event — has to still dominate at the
   ;; small size, or a baseline already carrying the whole-relation pass divides it back
   ;; out.  64 unrelated contexts is a graph such a pass crosses in well under that.
   {:name      :retract-context-cycle-scaling
    :claim     "retracting an edge of a context cycle is flat in the context graph it is not about"
    :sizes     [64 2048]
    :max-ratio 2.0
    :run       retract-context-cycle-scaling}


   ;; The baseline is 32 for `retract-nat-scaling`'s reason, which is `clash-arbitration`'s:
   ;; a retraction has a fixed cost of its own — the storage teardown, the settle, the feed
   ;; event — and the small size has to be one where that still dominates, or a baseline
   ;; already carrying a hundred merges' worth of the per-merge term divides it back out.
   ;;
   ;; **This is the third bound in the file that is not *flat*, and for the same kind of
   ;; reason as the other two.**  A settle with any supersession in play reconciles the
   ;; taxonomy caches against a moved set that includes every superseded handle, old and
   ;; new, because a supersession flip leaves no relabel to record it
   ;; (`settle/settle-finish`).  So Ω(merged) per settle is here by construction and is not
   ;; what this check is about; what it is about is whether the **reconcile of the
   ;; superseded set itself** re-examines every displaced spelling, which costs a record
   ;; fetch, a rewrite through the closure and a store probe apiece.
   ;; **The bound is read off a FULL run.**  This check's large reading barely moves
   ;; between `--only` and the gate (0.733 against 0.747 ms), while its *baseline* halves
   ;; (0.129 against 0.067), because by the twentieth check the JVM is warm and this
   ;; check's baseline is dominated by the n-independent constant.  The ratio inflates
   ;; from a faster denominator and nothing else: 5.66x alone against 11.22x in place,
   ;; same tree, same commit.  It bites here rather than on a flat check because
   ;; Ω(merged) leaves a real per-merge term in the numerator for the warm baseline to
   ;; divide into.  A bound read off `--only` fails every full run, so this one is not:
   ;; it is measured in a full run both ways rather than tuned until green — **11.22x**
   ;; narrowed against **32.12x** with the reconcile re-examining every standing entry,
   ;; and the absolute large readings say the same without a ratio at all — 0.747 ms/op
   ;; against 13.742.  18x sits between them.  Healthy full runs read 10.49-14.42x, so
   ;; the headroom on a loaded box is nearer 1.25x than the spread above suggests; this
   ;; check and the two taxonomy-edge ones are the file's tightest, and `--tolerance`
   ;; is the answer to a red run on a busy machine rather than a wider bound here.
   {:name      :retract-merge-scaling
    :claim     "retracting a fact naming no merged term costs under 18x per 32x the standing merges — bookkeeping, not a re-examination each"
    :sizes     [32 1024]
    :max-ratio 18.0
    :run       retract-merge-scaling}

   ;; Flat at the file's standing 2x, and the claim is exact: an edge that reaches no
   ;; exception must cost the same whether the KB's excepted rule has fired 32 times or
   ;; 1024.  The baseline is small for the usual reason — at 32 firings the per-firing
   ;; term has barely started, so it is not sitting in the denominator.
   {:name      :genl-edge-negation-recheck
    :claim     "a genl edge is flat in the firing history of a negated exception it cannot reach"
    :sizes     [32 1024]
    :max-ratio 2.0
    :run       genl-edge-negation-recheck}

   ;; The two taxonomy-edge checks, and their bounds are `clash-arbitration`'s reasoning
   ;; applied to the workload that file could not see: Ω(standing) is the honest floor —
   ;; a settle republishes the whole standing set whatever moved it — and what the bound
   ;; separates is *bookkeeping per standing pair* from *a re-derivation per standing
   ;; pair*.
   ;;
   ;; The baseline is **8**, and that is the header's own advice taken twice.  At 25 the
   ;; baseline of the `genlContext` check already carried 25 pairs' worth of the
   ;; re-derivation being measured, which divided out and left a defective engine reading
   ;; between 10.9x and 21.2x depending on which way the small reading bounced — a gate
   ;; that would have passed the very shape it exists to catch, roughly one run in four.
   ;; Eight is a size at which the re-derivation has barely started.
   ;;
   ;; **These two bounds are set from a full run, not from an isolated one, and the gap is
   ;; large enough to be worth stating.**  Everything here is Ω(standing) by construction,
   ;; so the reading is `a + b·n` and the *ratio* is decided by how big the fixed term `a`
   ;; is at the baseline — which is JIT warmth, and by the twentieth check of a run the
   ;; JVM is much warmer than it is on `--only`.  The large reading barely moves (it is
   ;; real per-pair work, which no amount of warmth removes) and the small one drops by a
   ;; third, so the ratio climbs: the `genl` check reads 9.8-13.2x alone and 17.3-22.7x in
   ;; place, the `genlContext` one 9.1-9.8x alone and 15.8-21.4x in place.  Bounds read off
   ;; an `--only` run would fail every full one, which is the mirror image of the warming
   ;; bias `measure` describes and lands on the same rule: judge a check where it runs.
   ;;
   ;; Measured at 100x the standing set, both engines, full runs: a `genl` edge reads at
   ;; worst 22.7x with the carry weighed per pair and 106.6x with it retired on the
   ;; relation's generation; a `genlContext` edge reads 21.4x against 65.6x.  So each
   ;; bound sits half again above the worst healthy reading and at a third to a half of
   ;; the defective one.
   {:name      :taxonomy-edge-arbitration
    :claim     "a genl edge separating nothing costs under 35x per write at 100x the standing clashes"
    :sizes     [8 800]
    :max-ratio 35.0
    :run       taxonomy-edge-arbitration}

   {:name      :context-edge-arbitration
    :claim     "a genlContext edge reaching nothing costs under 32x per write at 100x the standing P/¬P dilemmas"
    :sizes     [8 800]
    :max-ratio 32.0
    :run       context-edge-arbitration}

   ;; **The bound is 175x, and here is what it was read off.**  Two healthy full-run
   ;; readings, 85.4x and 80.9x, against a floor near 66x — so the honest reading sits
   ;; about 1.25x above the floor and the spread between runs is a few percent.  Below it,
   ;; the shape the claim rules out: `contradictions` filtering the standing set by cross
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
   ;; log term, which puts the honest floor between these two sizes near 66x rather than
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
   ;; it is: the `::order` key `settle/record-clashes!` attaches per report buys a
   ;; *constant* factor — one metadata read per comparison in place of four `pr-str`s —
   ;; and both shapes are n log n, so this is blind to losing it.  And the regression that
   ;; puts the ordering back on the settle path is a **write**-path cost: it lands on
   ;; `negation-arbitration`, whose 12x bound it exceeds, and not here.
   {:name      :standing-clash-reading
    :claim     "a reading of the standing dilemmas costs what it returns — an ordering of the standing set, not a re-derivation of it"
    :sizes     [25 800]
    :max-ratio 175.0
    :run       standing-clash-reading}])

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
  looked at twice."
  [{:keys [sizes max-ratio run]} tolerance quick?]
  (let [[small large] sizes
        ;; quick widens the bound instead of shrinking the pair: one attempt over the
        ;; real sizes is a coarse verdict, where measuring one size twice is six runs
        ;; and no possible failure — a gate that cannot fail is decoration
        bound   (* (double max-ratio) (double tolerance) (if quick? quick-slack 1.0))
        ;; the *large* size is what both warm to: it is the one whose reading the bound
        ;; is a claim about, so it is the one that must not be measured warmer than its
        ;; baseline was
        attempt (fn [] (let [a (measure run small large)
                             b (measure run large large)]
                         {:small a :large b :ratio (/ b (max a 1.0))}))
        first-try (attempt)
        best      (if (or quick? (<= (:ratio first-try) bound))
                    first-try
                    (min-key :ratio first-try (attempt)))]
    (assoc best
           :bound  bound
           :sizes  [small large]
           :status (cond (< (:small best) noise-floor-ns) :noise
                         (<= (:ratio best) bound)         :pass
                         :else                            :fail))))

(defn- report [{:keys [name claim]} {:keys [small large ratio bound sizes status]}]
  (let [[s l] sizes]
    (println (format "  %-20s %s" (clojure.core/name name)
                     (case status
                       :pass  "PASS"
                       :fail  "FAIL"
                       :noise "noise — below the gating floor, not judged")))
    (println (format "    %s" claim))
    (println (format "    n=%-6d %8.3f ms/op        n=%-6d %8.3f ms/op"
                     s (/ small 1e6) l (/ large 1e6)))
    (when-not (= :noise status)
      (println (format "    growth %.2fx  (bound %.2fx)" ratio bound)))
    (println)))

(defn- usage-exit [msg]
  (binding [*out* *err*]
    (println msg)
    (println "usage: lein perf [--only <name>] [--tolerance <x>] [--quick]"))
  (System/exit 2))

(defn- parse-args [args]
  ;; refused, not guessed: `--only` with no value would run the WHOLE gate while
  ;; reading as a single-check run, a dropped unknown flag gates at the default
  ;; tolerance (`--tolerence 1.5` at 1.0), and a bare `--tolerance` NPEs — which
  ;; gate.sh reports exactly like a regression
  (loop [m {:tolerance 1.0 :quick? false :only nil} [a & more] args]
    (case a
      nil          m
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
  (let [{:keys [tolerance quick? only]} (parse-args args)
        selected (cond->> checks only (filter #(= only (:name %))))]
    (when (empty? selected)
      (println "no such check:" only "— have:" (mapv :name checks))
      (System/exit 2))
    (println (format "\nvaelii performance gate — %d check(s), tolerance %.2fx%s\n"
                     (count selected) (double tolerance) (if quick? ", quick" "")))
    (let [results (doall (for [c selected] [c (run-check c tolerance quick?)]))]
      (doseq [[c r] results] (report c r))
      (let [failed (filter (fn [[_ r]] (= :fail (:status r))) results)]
        (if (seq failed)
          (do (println (format "%d of %d checks REGRESSED: %s"
                               (count failed) (count results)
                               (mapv (comp :name first) failed)))
              (shutdown-agents)
              (System/exit 1))
          (let [noisy (filterv (fn [[_ r]] (= :noise (:status r))) results)]
            ;; the floor's whole point: a check too fast to gate says so instead of
            ;; turning into a green light nobody notices has stopped meaning anything
            (println (format "%d check(s) ok%s"
                             (- (count results) (count noisy))
                             (if (seq noisy)
                               (format ", %d below the gating floor — not judged: %s"
                                       (count noisy) (mapv (comp :name first) noisy))
                               "")))
            (shutdown-agents)
            (System/exit 0)))))))

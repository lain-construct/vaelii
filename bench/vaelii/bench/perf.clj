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

  **What a ratio cannot see, and it is worth knowing before trusting a green run.**  A
  *constant* per-operation cost added to every write moves both readings by the same
  amount and leaves every ratio here alone — so a new unconditional retrieval on the
  assert path passes this gate untouched.  One has already shipped that way: a third
  argument-constraint declaration read, ~11% on every assert of a declaration-carrying
  predicate, invisible to all of these and found only by timing the absolute cost against
  the previous commit.  When a change adds work to a path every write takes, a ratio is
  the wrong instrument; measure the milliseconds against a worktree at the parent, where
  a constant shows up as a constant.

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

   {:name      :arg-root-retrieval
    :claim     "100 patterns pinning an argument after a variable are flat in the extent"
    :sizes     [400 3200]
    :max-ratio 2.0
    :run       arg-root-retrieval}

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
    :run       arity-reach-trigger}])

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

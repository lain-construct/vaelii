# Changelog

## 0.5.1 — 2026-08-11

What a write pays, and what an instrument can see. A run of costs that grew with what the
KB *holds* rather than with what the write *touched* — the taxonomy reconcile, the five flat
caches, the reified-NAT orphan sweep, a retraction's teardown, the standing-clash ordering, a
context-cycle repair, a repeated closure ask and a query plan's child count — each now reads
forward off the region a settle moved, and each has a `lein perf` check standing where the
claim is. Four places where **arrival order decided an answer** are closed: a predicate's
second declared inverse, `kb-quality`'s capped lists, the standing clash reports, and a
preview's capped diff. Beside them the process gained instruments for the rest — the change
feed crosses the process boundary as a subscription with a cursor, long work is a job registry
with a screen that watches it, `kb-quality` reads the knowledge where every other instrument
reads the engine, and the conjunctive planner costs a join rather than a column of literals.

**No entry is Breaking**, which is why this is a patch. Two carry a *Migration* line anyway,
because a caller can observe them and should be told what to expect. Each entry says what a
reader would observe; the mechanism is in the subsystem's doc, and the entry links it.

**Triage, for a 0.5.0 caller.** This is the index to what touches something you have written.

| If your code… | Then |
|---|---|
| reads the first N of `preview` / `edit-with-consequences!`'s `:believed-added` or `:believed-removed` | you get a different N — the halves are content-ordered now, and were handle-ordered |
| calls `clear-caches` and expects the literal cache's hit rate to zero | pass `{:counters? true}`; the reset is off by default |
| walks a `declared-transitive` predicate that also declares an `inverse` | the walk sees the inverse-recorded hops too, so an `ask` can answer more |
| branches on `violations`' `:violation` with a defaultless `case` | `:arbitration-truncated` is a new kind |

**Belief, and what a settle pays.**

- **A preview's capped diff is ordered by content, not by handle.** `preview` and
  `edit-with-consequences!` built `:believed-added` / `:believed-removed` off a relabelled
  region sorted numerically — handles, so assertion order — and `:max-results` then took a
  prefix. The browser's proposal panel caps at 50, so the same batch against the same
  knowledge showed a *different fifty* depending on the order the KB was loaded in, with
  `:bounded?` reporting true either way. Both halves rank on sentence then context
  (`diff-order`) now, ranked where each caller caps: `preview` sorts the built entries, and
  `moved-handles` ranks the handles because its callers cap before building — the liveness
  test fetches every record already, so the key costs no read. *Migration:* a caller reading
  the first N of either half gets a different N — a different, better-defined N. *Class:*
  neither label. The sequence a caller could observe was not reproducible for the same
  knowledge: it moved with the order the KB was loaded in, so there was nothing stable to
  depend on and no working caller could hold it as a contract. The previous docstring called
  handle order "a fact about the KB and not about the batch", which is exactly backwards — a
  handle is allocated in assertion order — so what this restores is the invariant the README
  states of every tie-break, on a public read that was breaking it.
  [docs/preview.md](docs/preview.md).
- **The pass that decides told nobody when it ran out of budget.** A declaration arriving
  after the content it convicts reaches back over that content, bounded by
  `settle/*exposure-instance-budget*`. The *reporting* half filed `:exposure-truncated`; the
  *arbitrating* half, which spends the same budget before anything is **decided**, said
  nothing — so a KB could leave standing a pair a finished sweep would have defeated and show
  a clean ledger. It files **`:arbitration-truncated`** (`:triggers` `:sample` `:budget`
  `:message`), one entry per settle rather than per pass, counting a trigger reached after the
  budget was spent as unswept. A separate kind from its twin because a reader acts on the two
  differently — *unreported* against *undecided* — and because `functional` and `asymmetric`
  reach back on the deciding path and on no other. Guards:
  `exposure_test/an-arbitration-sweep-cut-short-says-so` and the three beside it. The budget
  is drawn per `clash-candidates` call and that runs once per settle *pass*, so a settle that
  iterates draws it more than once — which is worth stating precisely, because it sounds like
  an order dependence and is not one: every pass walks its region in `content-order` and
  `touched` only accumulates, so the sweep meets the same triggers in the same sequence
  whatever order the same knowledge was written in. What a cut **does** leave is stated where
  the budget is: the pairs past it go *undecided this settle* rather than decided the other
  way, and discovery accumulates in `:clashes`, so a later settle's region can surface them.
  Guard: `exposure_test/a-budgeted-sweep-decides-the-same-pair-in-either-arrival-order`, which
  observes both write orders decide the same **set** of pairs at a budget covering one reach
  of two. *Class:* Additive — both violation renderers read
  `(name (:violation v))` rather than dispatching on a closed set.
  [docs/taxonomy.md, "Neither cut is silent"](docs/taxonomy.md).
- **Every mutation sorted every standing clash report.** `record-clashes!` ordered `conflicts`
  and `contradictions` by content on the settle path, so an assert into a KB holding N standing
  dilemmas paid O(N log N) to order a reading nobody had asked for. The vectors are stored in
  arrival order and **`settle/ranked`** puts a reading in content order at the point it is
  read: 1.60 → 1.07 ms per assert at 800 standing dilemmas, against 1.05 ms for the same
  workload before the ordering existed. `lein perf`'s `negation-arbitration` reads 10.02x
  against its 12x bound, from 12.65x failing, and `clash-arbitration` 8.09x against its 15x;
  both are full-run readings, and `vaelii.bench.perf`'s header states why that is the only
  reading these two have. Guard:
  `order_independence_test/the-reported-lists-are-content-ordered-not-arrival-ordered`, which
  observes the reported *sequence* over every ordering of three independent pairs. *Class:*
  neither label — both readings answer exactly what they did, in the same order.
- **A belief flip cost what the taxonomy held rather than what moved.** `refresh-relation` read
  the settle's region *backward*: deciding whether to run walked every supporter, and running
  recomputed the believed-supporter set of every edge. One flip measured 176.6 ms in a 64k-edge
  relation and 8.2 ms merely to decide the relation was untouched; through the engine,
  defeating and reviving one `genl` edge cost **6.87x across 8x the edges the flip is not
  about**. `:handle-edge`, the transpose of `:support`, lets the scope be read forward off the
  moved handles instead: 9.2 µs at 64k edges, **0.61x across the same 8x**. `perf`'s
  `taxonomy-belief-flip` is the gate.
  [docs/taxonomy.md, "The belief reconcile is scoped to the moved region"](docs/taxonomy.md).
- **Every settle paid the size of the KB's declared vocabulary to learn it had nothing to
  reconcile.** `:cache-support` holds every `disjoint` pair, predicate property, `inverse` and
  declared `arity` at once — tens of thousands on a corpus of OpenCyc's order — and the five
  flat caches read it backward. The *gate miss*, the settle that touches no declaration and is
  nearly every settle, measured 5.0 ms at 32k declarations for finding nothing; a flip measured
  95 ms. Read forward off `:cache-handle-keys`, the same readings are 5 µs and 1 µs, flat
  across 64x the declarations, and defeating and reviving one `(disjoint a b)` moves 1.2x
  across 8x the declarations where it moved 7.0x. `perf`'s `flat-cache-belief-flip` is the gate.
  [docs/taxonomy.md, "The belief reconcile is scoped to the moved region"](docs/taxonomy.md).
- **What the scoping removed was a rescan four writers were leaning on.** `add-edge` /
  `del-edge` and `support-add` / `support-drop` run with no `believed?` in hand, so they
  recompute an edge's or an entry's contexts from every *recorded* supporter. On the
  single-supporter case that is already the believed reading; on a **shared** one it is a
  superset, and losing the last *believed* supporter of something two sentexes still assert is
  a deactivation only a `believed?` can make — which the whole-KB rescan corrected without
  being asked. A writer touching a shared edge or entry records it in `:dirty` /
  `:cache-dirty` and the reconcile takes those whether or not belief moved there: a set
  proportional to the edits, never to the KB, and one a bulk load of distinct declarations
  never enters. The flat-cache oracle fails 95 assertions across its 25 random edit-and-flip
  trials without `:cache-dirty`.
  [docs/taxonomy.md, "The belief reconcile is scoped to the moved region"](docs/taxonomy.md).
- **The index behind the flat caches is a multimap where the closures' is 1:1.** A `genl`
  sentence names one edge, so `:handle-edge` can be `{handle edge}`; the flat-cache writers key
  one entry per sentence too, but nothing in the structure says so and removal is per-(handle,
  key) — a 1:1 index would let the first `support-drop` take a handle out from under an entry
  the same sentex still supports, which reads as a cache that quietly stops being reconciled
  rather than as a crash.
- **The two caches that still gate read whichever side is smaller.** The equality partition and
  the rewrite rules hold asserted term-identity claims rather than vocabulary, and the equality
  scan rebuilds `:out`, which is relation-wide state — so both gate rather than scope.
  `moved-touches?` walked the supporter set unconditionally, so deciding a 32k-entry cache was
  untouched cost 4.9 ms whatever the settle's own region was; it compares the two counts and
  walks the smaller, at 0.9 µs for both caches at every size measured.
- **A taxonomy edge retired every memo, because a counter says something moved without saying
  what.** Two guards in `settle` retired a whole memo on a generation counter, so at 400
  standing dilemmas one `genl` edge with nothing above or below it cost 800
  `checks/arbitrable-violations` calls, and one `genlContext` edge under a context no
  contradiction was stated in re-derived all 400 opposed bodies. Both cost zero now.
  `clash-nogoods` weighs the `genl` relation **per pair**: a pair of unary memberships is
  decided by `disjoint?` of the two types its sentexes name, so the memo stamps those two
  supertype closures and carries any pair whose reading stands — `[type context]`-keyed, and
  taking the global closure only where the member's own context already sees the whole of it.
  `negation-nogoods` records the joint-visibility verdict for each context pair it crosses and
  re-derives only the entries whose verdicts moved. Gates: `taxonomy-edge-arbitration` and
  `context-edge-arbitration`, each red before and green after, with `settle_region_cost_test`
  beside them.
- **Two more settle-path guards charged the whole KB.** `refresh-supersessions` runs every
  settle — the closure changes on retraction too, and that path moves no label — and
  re-examined every displaced spelling each time: a record fetch, a rewrite through the closure
  and a store probe apiece, which on the `owl:sameAs` volume an RDF import emits is one probe
  per standing merge per write. It is narrowed to `jtms/touched` plus migration's own output,
  with the closure compared rather than assumed: one unrelated retraction against 400 standing
  merges was 400 `rewrite-term*` calls and 9.06x across 16x the merges, and is 0 calls and
  1.70x. Beside it, a negated exception conjunct registers under the functor `not`, which hides
  the predicate it is about — so the `genls(super)` walk could not decide it and waved it
  through to `:all`, costing one level-6 query per firing the rule had ever made, per `genl`
  edge written anywhere. Keyed on `specs(sub)` instead, the contravariant twin: at 800 firings,
  1,600 exception evaluations and 10.16x become 0 and 0.91x, and an edge on the conjunct's own
  predicate still re-checks every firing.
  [docs/equality.md](docs/equality.md), [docs/exceptions.md](docs/exceptions.md).
- **A `disjointMetatype`'s membership is vocabulary, not a roster.** `clash-vocabulary` carried
  the metatype *roster* and not the metatype *membership*, and the two are not the same claim:
  `(disjointMetatype M)` separates M's members by being consulted, so `(M b_t)` leaving stops
  separating `a_t` from `b_t` while the mark still stands, no closure moves, and neither member
  of the standing pair is in the region. The memo carried the pair, so the KB kept reporting a
  dilemma the oracle does not report. Only the **departure** was silent — a member arriving is
  its own sentex and reaches its pairs through `metatype-member-reach` — which is why the
  assert-shaped tests never saw it, and `clash_oracle_test`'s ontology declares no metatype at
  all, so the randomized stream could not generate the shape either. The membership map is a
  value like the four beside it, so a settle that moves no member abandons nothing.

**Where arrival order was deciding an answer.**

- **A predicate's second declared inverse hid its first, and which one survived was the order
  they arrived in.** `(inverse P Q)` and `(inverse P R)` are both legal and the taxonomy held
  **one** partner per predicate, so the later declaration displaced the earlier and every
  reader of `inverse-of` answered off whichever that was: `(transitive beforeEv)` proved
  `(beforeEv A C)` with `afterEv` declared second and **failed** with it declared first — the
  order independence the README states as an invariant, broken by a legal pair of declarations.
  Retracting one was worse: `cache-uninstall` dropped the predicate's whole entry, leaving `P`
  with no inverse while `(inverse P Q)` was still believed. `:inverse` is
  `{predicate -> #{partners}}` now, maintained in both directions the way `:disjoint-index`
  is; **`tax/inverses-of`** is the set the step relation and `solve-inverted` read, and
  **`inverse-of`** keeps its shape — one partner or nil — and answers the lexicographically
  smallest, so a caller wanting *a* partner gets a content-keyed answer rather than an
  order-keyed one. `vaelii.core/inverse-of` is unchanged in arity and return. *Class:* neither
  label — no working caller can have depended on which of two declarations won, since nothing
  documented which would. [docs/taxonomy.md, "The step relation"](docs/taxonomy.md).
- **`kb-quality` ranked its capped lists on the handle**, which is assertion order — so two
  loads of the same knowledge reported the same `:never-count` over a different `:never`, and
  the examples moved with the order an author happened to write the rules in while the counts
  beside them did not. The listed sets rank on content now: the consequent predicate and the
  sorted antecedent predicates, both already in the vocabulary pass, with the stored sentence
  breaking a tie only within a group that shares a signature — so the store is read for the
  listed rules rather than for every rule in the set. *Class:* neither label — `kb-quality`
  is new in this release and has never shipped the handle-ranked reading.
- **A prompt is cut by content, and a sample says it is one.** The LLM prompt builders took
  their lines and *then* sorted them, so the page a model was shown for a term with more
  mentions than the cap was a prefix of the index's own order — arrival order, since handles
  are allocated in assertion order — and the same knowledge loaded twice proposed against two
  different pages. The sort precedes the cut now, at each of the four sites, and the heading
  tells the model it is looking at a sample rather than the whole record. `:max-scan` (4000)
  replaces a hidden 4x oversample and is stated rather than derived, the number chosen so the
  fetch is noise beside the model call the prompt is built for. Guard:
  `llm_page_test/the-cap-takes-the-content-first-lines-not-the-first-stored`, which
  discriminates — restoring the take-then-sort makes it pick the first-stored fact over the
  content-third line. `used-with`'s own scan cap is the one place arrival order still shows,
  and closing it means walking the extent. *Class:* neither label — `vaelii.impl.llm.*` is
  impl, and what moves is which lines a model sees. [docs/llm.md](docs/llm.md).
- **The scan above the cut was ordered by the index, which is not an order at all.** The four
  sorted cuts sat on top of a `take` over the term index's posting set, and that set is a
  Clojure **set** rather than a handle-ordered list — so the sample was hash-ordered, moved with
  the index's representation, and differed between the columnar and KV backends over identical
  knowledge. The handles are sorted before the cap now, which costs a sort and **no extra record
  reads**, the posting set being materialized either way. Be exact about what that buys: below
  the bound a page is a function of the knowledge alone; *at* the bound it is a sample of the
  term's **earliest** mentions, because ranking sentences by content means fetching all of them,
  which is the cost the bound exists to refuse. The heading already tells the model it is
  reading a sample. Guard: the same knowledge asserted in three orders yields one page, and it
  fails without the sort.
- **A card's cut is a count, including the cut that was not counted.** `used-with` claimed
  everything its scan missed was "still offered under a later tier", and that is false for
  exactly the predicates it exists to find: one used with the term but never declared and never
  `argIsa`'d lives in that tier alone, so a scan miss drops it from the card rather than
  demoting it. Its cap is 200 facts, which a common term passes routinely. `:dropped` gains
  **`:unscanned`** — the facts at each position the scan never read, one O(1) `count-with-arg`
  apiece and no record fetched — and the card says so in words: *this card did not read N
  further facts about this term; a relation used only there is not listed above.* Beside it, the
  fifth site of the ordering bug: `correct.clj` took `first` of a position's `argIsa`
  declarations, so two contexts declaring one position decided by index order whether a
  reversed-argument alternative was offered and whether `:confidence` read `:low` or `:medium`.
  It ranks by **specificity** now — narrowest first, name breaking the tie — which is the honest
  reading of two constraints, since a term must satisfy both to stand there.
- **A declaration's supporters were being lost or arbitrarily chosen, and the cycle goal could
  throw.** Three fixes on one path. The `disjointMetatype` sweep walked the *believed*
  memberships where it records *supporters*, so a membership defeated at that moment never
  entered `:cache-handle-keys` and clearing the defeat could never revive it — belief depending
  permanently on whether the defeat or the declaration arrived first, and the live KB
  disagreeing with the recovered one over the same store, since `rebuild-taxonomy`'s second
  pass reads what is stored. It reads `stored-declarations` now, the same helper that pass
  uses. A KB may state `(functional P)` in two contexts, which is two handles and is refused by
  nothing, and `derive-functional-equalities` took `first` of them into the justification's
  antecedents — so retracting that one withdrew a merge the other still licensed, and which it
  was depended on arrival order; every supporter contributes a justification now
  (`tax/prop-supporters`), the shape `deduce-lift` already uses. And `(P ?x ?x)` ranked its
  answers with a bare `sort`: those are terms, a term need not be `Comparable`, and an
  unreifiable function application stays structural in argument position — so a cycle relating
  two of them threw `ClassCastException` out of `ask`. It is `sort-by pr-str`, the key this
  file ranks terms by elsewhere.

**The model backends, the apply path, and what they refuse.**

- **A credential that cannot ride in an HTTP header is refused by name and never by value.**
  `anthropic/credentials` handed the environment's value straight to
  `HttpRequest.Builder.header`, and the JDK rejects a CR, LF, control or non-ASCII character with
  an `IllegalArgumentException` whose message **quotes the value verbatim**. Nothing on that path
  caught it and the browser renders an error message onto the proposal panel, so a `.env` ending
  in CRLF — or a `$(cat key)` in a shell that keeps the newline — was one hop from putting an API
  key on a page. The header call is caught and re-raised as
  `{:type :llm-bad-credential :header "x-api-key"}`, which names the header and carries no value,
  and the two environment reads are trimmed so the common case never reaches the JDK. Trimming is
  not the guarantee — a control character mid-string still gets there — which is why the catch is
  what the promise in `credentials` rests on. *Class:* Additive: a `:type` where none was.
- **A streamed body has a deadline, so a host that goes quiet releases the thread.** A request's
  `.timeout` bounds the response *arriving*; a streamed turn is almost entirely what comes after
  that, since the lines are pulled off the socket once `send` has returned — and the browser's
  page path always streams, which is the one path the option was written for. Both transports
  read the body under a daemon watchdog that closes it at `:timeout-ms`, measured from before the
  send so the option bounds the whole turn, and a failure after the watchdog fires is
  `{:type :llm-timeout :timeout-ms n}` rather than whatever a closed socket raises. *Class:*
  neither label — a read that outlives the timeout its caller configured is the defect, not a
  contract anything could depend on.
- **A 200 whose body is not JSON carries a `:type` like every other refusal here.** A proxy in
  front of the host answering HTML, or a chunk truncated mid-object, escaped as the JSON
  library's own exception — the one thing in this tree a caller could not discriminate on. Both
  transports raise `{:type :llm-bad-response :status s :excerpt …}`, the excerpt bounded at 200
  characters and in the data rather than the message. *Class:* Additive. Beside them, the `ant`
  credential probe is killed at five seconds rather than waited on — `available?` reaches it on
  the request that runs a turn, so a wedged CLI wedged a request thread on what is only a probe —
  and a backend that probes available and then will not build now logs a warning naming the
  backend instead of falling through to the stub in silence, with `opts` never in the line since
  it may carry a credential.
- **A turn the model ran out of tokens in was being diffed into proposed deletions.**
  `:stop-reason` was read only through `refused?`, so `"max_tokens"` was not a status — and on
  the selection path every row the model never reached came back as a `:remove`, which is a
  transport artifact rendered to a human reviewer as an intended retraction. Truncation is
  decided **before** the diff now: `:truncated` is a status on the paths whose answer is diffed
  (carrying no batch at all, and placed ahead of the tool-use arm so a half-written tool call
  cannot run) and `:answer-truncated?` is a flag on the additive paths, where a short answer
  costs assertions rather than proposing a retraction. `propose-page` also lifts `:page-found`
  and `:page-truncated?` out of metadata into the returned map, where a `select-keys` cannot drop
  them — the sample heading reached the model and nothing reached the reviewer.
- **`apply-proposal!` catches, settles, and says what landed.** It calls `edit!`, which
  `vaelii.core` documents as **not a transaction**: `check-edit` grades each add against the KB
  as it stands, so two jointly-inconsistent adds both pass, and a throw at entry N left 1..N−1
  stored **and skipped the settle** — a KB holding a prefix nothing had reconciled, reported to
  the caller as a bare exception. It returns `{:result :applied :failed-at :error}` now, with the
  settle run by hand on the failure path, so a partial apply is a believed prefix a caller can
  read rather than a stranded one. Guard: a `disjoint` batch that `check-batch` passes, asserting
  `:applied 1`, `:failed-at 1`, and that the settle histogram moved.
- **A `StackOverflowError` reading model text read as "the model proposed nothing".** Every read
  of model-written EDN caught `Exception`, and a deeply nested form throws an `Error` — the same
  hole `web.clj` had already closed and stated. Eleven sites across the session, tool, score and
  oracle namespaces catch `Throwable` now, and the mechanism was measured rather than assumed:
  the EDN reader overflows around 5,000 nestings, but **`sentex/canon` overflows at 500**, well
  inside what the reader accepts without complaint, which makes the score path's handle lookup
  the sharpest of them. Cheshire does not overflow at all — Jackson refuses past depth 1000 with
  an ordinary exception — so the comment there states the policy rather than a mechanism that
  does not apply. One of those sites marked its parse failure with `(.getMessage e)`, which is
  **nil** for a `StackOverflowError`, so the nil fell through to the map branch and returned an
  empty batch: a crash presented as a model with nothing to say. It names the class now.
- **The `^:llm` consent gate could be satisfied by a helper that does not consent.** `lein test`
  makes no model call, held by two independent things — the `^:llm` mark and the
  `VAELII_LLM_LIVE` gate — and the meta-test that keeps them agreeing accepted *a call to any fn
  named `live-model`* as proof. One namespace defined a `live-model` that was a bare provider
  constructor with no gate in it, so a new marked test there calling only that helper would have
  satisfied both meta-tests and dialled out unconsented. The scanner follows the call now rather
  than matching the name: it collects the names a file defines whose own source reaches
  `live-llm?`, to a fixpoint, and consent is proved by calling the gate or one of those. The head
  regex also takes `defspec`, which brought one more test into scope. Six marked tests, all
  proving consent; nothing unmarked consents.

**The taxonomy and its closures.**

- **A `genlContext` edge out of a context that sees another one back never returned.** Three
  asserts reach it: `(genlContext A B)`, `(genlContext B A)`, then any edge out of `A`. The
  depth potential ranks the **condensation**, so `A` and `B` are level as one component, and
  `raise-depth` lifted the single node — which put `A` above its own mate, which forced `B`
  above `A`, round the cycle without end. The lift moves whole components now, and the
  condensation being a DAG is what terminates it. `taxonomy_depth_test` bounds the call on a
  daemon thread rather than trusting it, because a suite that hangs reports nothing.
- **Retracting one edge of a context cycle cost the whole context graph.** A deletion can split
  a strongly connected component, so `deactivate` surrendered the depth potential and rebuilt
  every component in the relation: **11.19x across 16x a background the retraction is not
  about**, where an acyclic edge on the identical KB is flat. An edge can only break the strong
  connectivity of a component whose induced subgraph it belongs to, so an edge merely
  *incident* on a cycle is left alone; when both endpoints share one, that component's subgraph
  is re-run through Tarjan and the pieces ranked against each other and against what they point
  at. The same retraction reads **0.97x**, and `lein perf` gains
  `retract-context-cycle-scaling` — the first check in the file to build a context cycle at
  all, which is why a whole-relation repair per deleted cycle edge stayed invisible.
- **A repeated closure ask reads the answer instead of walking it again.**
  `TransitivePredicateProver`'s open-argument arms hold the reach per
  `[direction predicate node context]` on the KB, stamped with the change clock: **0.10–0.14x
  on a repeat over a 2,000- to 8,000-node chain, and no record read at all**. A **closed** goal
  reads the cache without filling it, since computing a closure to store would charge a two-hop
  question for the whole extent. The clock is the whole invalidation story and is what makes
  the cache follow belief — a relabel moves it, so a defeated edge retires the closure that
  crossed it. The bound counts **members**, not entries. **Additive**: no answer moves, and
  `caches`/`clear-caches` show and drop it like every other.
  [docs/taxonomy.md, "What is cached, what is not, and why"](docs/taxonomy.md).
- **`(P ?x ?x)` cost a closure per node to answer nothing.** The one-variable arm of a
  declared-transitive goal asked `reaches?` of every source term, and `reaches?` walks that
  source's whole reach in order to *fail* — so an acyclic chain, which is what a `before` or
  `partOf` relation ordinarily is, cost O(n²) to answer the empty set it always answers. It is
  one iterative Tarjan condensation over the step relation now (`on-a-cycle`, O(V+E));
  iterative because a component's depth is a chain's length. The answers are unchanged.
- **A transitive predicate's hops are the believed matches, and the inverse spelling is one of
  them.** `(transitive before)` walked stored `before` facts, so `(inverse before after)` on
  the same relation left every hop recorded as an `after` fact off the graph — the chain broke
  mid-walk and the answer came back negative with no diagnostic, on a shape that is ordinary
  temporal modelling. `succs` / `preds-of` probe the partner literal beside the direct one,
  deduped as a set of neighbour terms; the probe is a `matches-visible` call and never a goal
  handed back to the registry, which keeps the step relation a function of the KB alone.
  `(inverse P P)` is a legal declaration and now a storable one — the flat-cache key was the
  checked `#{p q}` literal, which threw `Duplicate key` out of `assert`. *Migration:* an `ask`
  over a declared-transitive predicate returns **at least** what it did and never less, so the
  only caller affected is one that counted on an inverse-recorded hop being invisible —
  including through negation as failure, since `unknown` and `exceptWhen` read the same list.
  *Class:* neither label, on §3.8's own precedent: an author who declared
  `(inverse before after)` and got a walk that ignored every `after` fact was not getting what
  they believed, which is the case Go's compatibility promise exempts and SemVer calls an
  internal change that fixes incorrect behavior.
  [docs/taxonomy.md, "The step relation"](docs/taxonomy.md).
- **The closure walk's per-edge cost is measured, and the record fetch is the minority of it.**
  A walk of *n* nodes pays *n* `get-sentex` calls, and `lein bench-walk` times the walk against
  a direct sweep over the same records on the same mount rather than assuming the share. What
  it finds is a threshold rather than a slope, and the threshold is the hot-record LRU's
  capacity: under it a `:disk` fetch is 0.06 µs and *cheaper* than the `:memory` one; past it
  the fetch is a page-in at 3.03 µs and reaches 21% of the hop, with the `:disk` walk at 0.61x
  the `:memory` one. `:disk-memory` lands with `:disk` at every size, which says the record
  store is the whole of the difference. [docs/taxonomy.md, "What one hop costs"](docs/taxonomy.md),
  [docs/storage.md](docs/storage.md).

**Reified NATs, and what a retraction sweeps.**

- **A unary fact about a reified NAT was deleted with the constant, silently.** One clause of
  the orphan sweep matched on **arity alone**: any believed `(p K)` read as a materialized
  `resultIsa` type with no test that anything had declared one, so `(prime (PrimeFn Seven))` —
  a claim somebody asserted — made `K` look orphaned the moment its other uses went, and the
  sweep retracted the claim with the constant. No error, no report. Bookkeeping is decided by
  **authorship** now: `nat/minted-for` re-derives what `mint-nat!` wrote from the same believed
  declarations the mint read, and everything else naming `K` is somebody's assertion whatever
  its arity. `nat_test` gains the two cases that separate the readings. The one constant this
  keeps that arity would have collected is one whose `resultIsa` was retracted after the mint —
  and holding it is the direction to err in. *Class:* neither label. The set of sentexes
  surviving a retraction moves in both directions here, which is observable — but a caller
  whose unary claim about a reified constant was being deleted underneath them was not getting
  what they believed, and the materialized `(T K)` this now keeps is a believed sentence nobody
  has withdrawn.
- **One retraction cost what the whole KB had ever reified.** The sweep asked "which constant
  is orphaned?" by matching `(termOfUnit ?k ?e)` — every NAT in the KB — after every teardown
  and to a fixpoint, so retracting a plain fact that names no NAT cost **16.70x across 16x the
  NATs the retraction is not about**, linear, which on a corpus of OpenCyc's order is seconds
  per retraction. No benchmark saw it, because the sweep is gated on the KB declaring a
  `reifiableFunction` and no synthetic probe declares one. It asks only about the constants the
  teardown's own removals named (`nat/constants-named-by` → `nat/orphaned-among`), each settled
  by one inverted-term-index read: **1.22x across the same 16x**, and flat is the claim, gated
  by `retract-nat-scaling`. The teardown also stopped reading the expression and the
  correspondence declarations at all — `assert_cost_test`'s `nat-orphan-teardown` re-pins from
  1,700 functor-root reads to 1,400 and from 100 trie-lookups to none.
- **A teardown records only what a sweep will read.** `integrate/removal-sink` retains every
  sentex that leaves the store for the length of a teardown, which on a cascade is the whole
  cascade held in a vector — and it exists for the reified-NAT orphan sweep, which is itself
  gated on the KB declaring a reifiable function. The gate now decides whether the record is
  kept, so a KB that reifies nothing pays nothing. `edit!` reads the sink before its adds, so a
  batch declaring the KB's first reifiable function finds a nil sink and takes the whole-KB arm
  — the stricter question, and the right one for a batch that has only just made reification
  possible.
- **The removals reach that sweep through `integrate/*removed-sink*`**, because they arrive
  from three places and only one is the caller's: the dependency-directed sweep, the settle
  that follows it, and the orphan sweep's own retractions. The third is what makes the region
  grow with the fixpoint, so a NAT nested in a collected orphan's expression is still collected
  rather than left dangling as a raw `nat/` symbol. `preview`'s rollback keeps the whole-KB
  sweep and says why: the batch it undoes runs with the settle sweep off, so the claim it owes
  is about all of the KB. A use that merely stops being **believed** is not a use that went and
  does not make its constant a candidate — collecting on a defeated use would delete the
  `termOfUnit` map while a stored sentence still names the constant. `nat_test` gains the
  cascade case and the settle-swept case.

**The change feed, and the daemon under load.**

- **The change feed crosses the process boundary, as a subscription with a cursor.** `watch`
  takes a function and a function does not cross an EDN wire, so the daemon's half is the one
  thing request/response can carry: `:watch` answers a token, `:poll` reads that subscription's
  ring forward from an integer cursor, `:unwatch` drops it, `:watchers` says what is open. All
  four live in `serve/feed-ops` rather than `serve/ops`, which is what keeps a subscription out
  of the model's tool set. `:lagged` is on every reply rather than only the bad ones, since a
  feed with a silent gap is worse than polling; `{:wait-ms n}` parks the request outside the
  write monitor, capped at 30 s. A test drives a batch through `POST /op` and compares the
  wire's events against an in-process listener's after a full EDN round trip.
  [docs/feed.md, "Across the wire"](docs/feed.md).
- **A parked long poll held a thread nothing counted, so the feed could stall the daemon it
  exists to keep live.** Moving the wait outside the write monitor stops a parked poll blocking
  the *writer* and does nothing about the *worker threads*, which were never bounded — ring's
  pool defaults to 50, the subscription ceiling was 64, and nothing related the two. 55
  concurrent polls drove the pool to 50/50 busy and `/health` from 62 ms to 25,997 ms, and one
  subscription was enough, since nothing bounded polls per token. `subscribe/max-parked` (16)
  bounds how many may wait and `serve/http-threads` (50) is stated rather than defaulted so the
  pair is checkable. Over the ceiling a poll *asking to wait* is refused
  (**`:too-many-waiters`**, 400) and told to poll on a timer; one that does not ask, or whose
  events are already there, is never refused. *Class:* neither label, and the reason is the
  same for every refusal in this run of entries — the feed itself is new in this release, so
  there is no 0.5.0 caller to have written against the unbounded shape.
- **Two ways the feed could be taken down or lied to, and the bounds that stop them.**
  `{:wait-ms 1e300}` answered 500: the option was validated as a `number?`, which admits a
  magnitude no long holds and admits `##NaN`, which coerced to 0 and turned the long poll into
  one that answers instantly forever — it is `nat-int?` now, capped before the coercion rather
  than after. And a subscription dropped *while it was being registered* took the whole feed
  down permanently: an unguarded `assoc-in` **recreated** an entry that had gone, with no
  `:polled-at` in it, so `reap` — which runs at the head of every feed op — read `(- at nil)`
  and threw for every later call on that daemon. Guarded like its two siblings now. What one
  caller can allocate is bounded three ways, since nothing authenticates `POST /op` on the
  loopback default: 64 subscriptions, 256 events per ring, and one nobody has polled inside
  five minutes reaped at the next call. Reaching a ceiling refuses the **new** subscription
  (`:too-many-subscriptions`) rather than evicting somebody else's. *Class:* neither label —
  new surface refusing input it never shipped accepting.
- **The ceilings bound the event count, not the bytes**, and `docs/feed.md` says so: an event
  carries one settle's whole relabelled region, and 20 batches of 500 facts left one abandoned
  subscription holding 10,000 preview entries. `:watchers` is what an operator reads against
  that, and it reports `:delivered` and `:pending` — both client docstrings said `cursor`, the
  one word neither field may use, since neither number is the reader's position.
  `vaelii.client/watchers`, `vaelii.serve/feed-ops` and `vaelii.serve/op-names` join
  `public_api_test`'s roster, which is a subset check and had been letting them through
  unnamed. The browser is untouched, and that is a decision: its live regions poll an htmx
  fragment, which is the right pattern for a progress bar, and a job's percentage is not belief
  moving.

**Conjunctive query planning.**

- **Planning one fixed conjunction is flat in the size of the KB, and a gate says so.** The cost
  model divides by the trie's distinct-value count at a position and asked for it once per
  literal per plan — and `(count (children …))` answers that by *materializing* the child set,
  so planning a conjunction that never changed cost 25x more against 32x the facts, per rule
  expansion, per node in the node engine and per `prove` call. `p/count-children` is the same
  number off a cardinality instead. **Additive** — a new `IndexStore` read, and the two
  implementations of that protocol are the only ones that owed it. `lein perf` gains
  `plan-scaling`, which reads flat with the count and 24.6x without, and `backend_parity_test`
  carries the new read. The O(1) has one exception and it is the overlay's merge rule, which
  `overlay_test` holds to the same answer at every depth.
  [docs/indexing.md](docs/indexing.md), [docs/overlay.md](docs/overlay.md).
- **A conjunction is costed as a join rather than as a column of literals.** `plan/est-rows`
  sits beside `est-matches` and answers the other question — not *can* this literal fan out, a
  sound upper bound, but *how much*, an expectation that is wrong in both directions and
  composes for exactly that reason. It returns the relation's shape
  (`{:rows 400 :vars #{?x ?y} :distinct {?x 20}}`), and the planner threads that summary
  through its fold, so the *k*-th pick is costed against the rows reaching it rather than
  against its own extent. Two literals that each look cheap can join to something enormous; on
  a rule with three or more antecedents a per-literal count's error is multiplicative.
  [docs/inference.md, "Conjunctive query planning"](docs/inference.md).
- **A count the trie read beats one inferred.** `:distinct` holds only the column the walk can
  reach — the trie narrows left to right — and the join divides by the larger of the counts the
  two sides *read*. Where neither read it the model falls back on a proxy rather than dividing
  by nothing, because calling that join a cartesian product is the error that compounds fastest
  with depth. A variable repeated inside one literal is the same join and priced the same way.
  **No statistics table**: every number is already in the count-aware trie, and a second source
  of truth about cardinality would need maintaining on every write. The generators are split
  into blocks — two literals sharing a variable are one connected component — and the blocks are
  ranked by adjacent transposition, a descending sort on `s/(n−1)`, optimal in O(k log k), with
  two placements outside the law because they are claims an estimate cannot make: a block
  *proved* to match at most once runs first, and the block reached by the caller's bindings, the
  evaluables or the recursive literal runs before the rest.
- **The estimator is measured before the plans are, and `lein bench-plan` reports the curve.**
  q-error per join depth is the go/no-go: flat in the depth means the estimates compose. It
  reads **1.00 at every depth through six literals** on a uniform chain, and 1.00 / 2.75 / 2.87
  on a corpus built to break the independence assumption — wrong, and flat, where a model whose
  error compounded per join would read about 7.5 at depth 3. Against an oracle over all 24
  permutations of randomized four-way joins the planned order runs a mean **1.13x** the best
  possible (2.18x before), and the same conjunction as a **rule's** antecedents runs 7.1x and
  8.4x faster planned at four and five antecedents. Two assumptions are stated rather than
  pretended away — independence, and that the counts span every context where a read is scoped
  to one — and `plan_test` pins all three consequences.
- **`query-plan` carries the numbers the order turned on.** Additive: a join plan's rows gain
  `:est-rows`, `:est-prefix` and `:block` beside the `:est-matches` already there, and the
  browser's plan table shows the same columns. The three together are what makes a surprising
  plan diagnosable — a literal placed early on a small `:est-matches` whose `:est-prefix` then
  jumps is the model being wrong about a *join*, not about a literal. They are read off the plan
  that ran rather than recomputed beside it, through the same two calls the planner costs with.

**The browser: jobs, caches, and a reading of the knowledge.**

- **Long work is one mechanism: a job registry, and the screen that watches it.**
  `vaelii.impl.jobs` holds every operation that takes minutes rather than milliseconds — filling
  a KB from a corpus, writing one back out, joining every rule over everything stored — with one
  status vocabulary (`:running` → `:cancelling` → `:done` / `:cancelled` / `:failed`), one
  progress reading and one cancel. The browser gained `/jobs`, `/jobs/rows` (a self-terminating
  poll) and `/jobs/cancel`; a job survives the request that started it, so closing the tab stops
  nothing. A finished job's report stays an hour and nothing unsettled is ever dropped, because
  forgetting a job releases its writer claim and a thread still running is still writing. The
  catalog's load and export were **moved onto** the registry rather than left beside it, so the
  panel and the loader can no longer tell two stories.
  [docs/web.md, "Long work as jobs"](docs/web.md).
- **`POST /chain` is a job, with the derivation bound on the form.** A fixpoint over a corpus was
  minutes of this process's one writer inside a request, with nothing on screen and no way to
  stop it short of killing the browser. It reports about four times a second, takes a cancel at
  its next report, and carries `:max-derivations` as a field — and a run that settles inside 250
  ms still answers with the `/stats` page and its derivation count, so nothing small acquires a
  spinner. What a stopped run leaves is stated beside the button: a KB holding a prefix of the
  run rather than a corrupt one.
- **A second writing job is refused as `:job-busy`, where a second load answered `:busy`.** One
  job writes at a time — a load and a chaining run each claim the writer, an export claims
  nothing — and the refusal names the job that holds it rather than queueing behind it. **Not
  Breaking**: `:busy` was thrown at one site in `vaelii.impl.catalog` and read by
  `vaelii.impl.web` alone, both inside the impl boundary, so no caller the boundary covers could
  discriminate on it. It carries an entry because `type_contract_test` holds every `:type` in
  the sources, public surface or not.
- **The browser's status words are the registry's**, so an entry on `/kbs` says `running` and
  `done` where it said `loading` and `ready`, and the CSS classes move with them. A
  screen-scraper is the only caller that can observe this; the vocabulary being one rather than
  two is the point.
- **What this process is holding, on a page — caches, heap, and the profiler.** `/kbs` measured
  heap; nothing measured what the engine holds *beside* the store, which is a dozen derived
  structures whose whole purpose is that a repeated question is not recomputed. `caches` is one
  read over all of them — entries, the bound they are cleared wholesale at, what one entry
  counts, and the hit rate where anything counts one — and `/caches` renders it beside the heap
  strip it reuses. A hit rate is the cost model's report card: "the second query was fast" is a
  demo, and "because it was served from a cache, and here is the rate" is evidence. `/stats`,
  `/kbs` and `/jobs` each carry a line to it, and a test asserts all three. `VAELII_PROFILER`
  starts `clj-async-profiler`'s UI with the browser (`VAELII_PROFILER_PORT` moves it off 8080)
  through a `requiring-resolve`, so it exists without the dependency and says so when the class
  is absent rather than linking to a port nothing is listening on.
  [docs/web.md, "What this process is holding"](docs/web.md).
- **A number's scope is part of the answer, because two of them differ.** A row carries `:scope`
  for what its entries count and `:counters` for what its hit and miss counters count, and the
  literal cache is the awkward case: its entries are one KB's and its counters are global across
  every KB in the process. Rendering the second as the first attributes another KB's work to
  this one, so the page says *rates: this process* and a test asserts it with two live KBs.
  `:unit` is on every row for the neighbouring reason, and `:limit` takes a thunk where the
  bound is a dynamic var — the field a reader consults to ask whether a cache is about to flush
  is the last one that may be stale.
- **The list is complete rather than merely finite.** Every cache-holding namespace declares
  itself into a register at load, so there is no central list to forget to add to — and a cache
  in a namespace this process never loaded has no row at all, which is the honest answer where a
  row of zeroes would claim a cache that does not exist. Two tests hold the line: a roster, and
  a scan of the sources for the bounded-cache constant. A row that throws is reported as a cache
  that could not answer, and costs its own row and no other.
- **The clear is a measuring instrument, not an edit — and `clear-caches` took a KB and reached
  past it.** It drops every derived cache and reports what went; nothing is destroyed, since
  every entry is derived, so it is bare rather than `!`, moves no belief, holds no writer, and
  is usable *while* a load runs. It leaves the structural caches alone, where dropping entries
  costs the sharing they exist for. But it also reset the literal cache's hit and miss counters,
  which are process-wide — so asking one KB to drop its entries zeroed the rate every other KB
  in the JVM was reporting, mid-measurement. The counter reset is `{:counters? true}` now, off
  by default and named at the call site, with `:counters-reset` in the reply;
  `literal-cache/clear-cache` drops entries only and `literal-cache/reset-counters` is the wider
  control it was split from. *Class:* neither label — `clear-caches` is new in this release and
  has never shipped with the wider behaviour.

**The shipped ontology.**

- **The shipped ontology decontextualizes predicate metadata and nothing else.**
  `SocietyContext` declared `(decontextualizedPredicate marriedTo)`, the one *domain* relation
  carrying a mark the rest of the ontology reserves for claims about a **predicate**. A marriage
  stated in any context was therefore deduced into UniverseContext and became a claim of the
  whole KB, so a story, a jurisdiction or a hypothesis could not hold one the rest of the KB did
  not share. It also reached past what the declaration names: a rule fires on the lifted copy
  too, so `SocialContext`'s marriage rule placed `knows` within reach of every data context —
  **decontextualized by consequence**, declared nothing. The declaration is gone; `marriedTo`
  keeps `symmetric`, and a KB that wants marriages lifted asserts the declaration itself, where a
  reader of that KB can see it. A roster test pins the shipped set to the metadata marks plus
  `genlContext`. *Class:* no label — ontology **content**, not the surface a caller writes
  against (§3.8); what `decontextualizedPredicate` means is unchanged.
  [docs/contexts.md, "What the shipped ontology declares it of"](docs/contexts.md).
- **Every argument position in the shipped ontology is declared.** 227 `argIsa` / `argGenl`
  declarations across `CoreContext` and the four upper contexts that carried none, at `thing`
  throughout — the point being that every position is *stated*, not that any is narrowed, since a
  constraint at the root never convicts. What that buys is schema completeness, a wrong-position
  refusal, and an edit rather than an addition when a position is later narrowed.
  `argGenl genl 2` is the single position left undeclared and `CoreContext` says why beside it.
  [docs/argtypes.md](docs/argtypes.md).
- **Six types enter the upper ontology, and the declarations narrow onto them**, so an argument
  constraint refuses something rather than only recording that the position was considered.
  `spatial_thing` takes `physical_object` beneath it, `time_point` sits under `temporal_thing`,
  `function` beside `predicate`, and `integer`, `character_string` and `context` name themselves.
  Space takes `spatial_thing` on all 100 of its positions, Time takes `temporal_thing` on 46 and
  `time_point` on 16 — meeting at `startOf` and `endOf` — and the meta-vocabulary takes
  `predicate`, `function`, `context`, `integer` and `character_string` where it held `thing`, so
  `(before genlContext genl)` is an `:arg-type` refusal. A position stays at `thing` where that
  is the true answer and says so at the site. *Class:* no label — `resources/kb/` is ontology
  **content** rather than the surface a caller writes against (§3.8), and what it owes instead
  is the roster that pins the shipped set, which is `vocabulary_audit_test` over
  `vaelii.impl.vocabulary`. *Migration:* a KB built on the shipped Space or Time vocabulary can
  be refused where 0.5.0 accepted it — the refusal names its convicting declaration, so widen
  that declaration or state the argument at a type the position admits.
- **Flight is a capability of a kind, and the kind that cannot is an exception.** `flies` was a
  verb-shaped one-place predicate, which says the thing in a shape that cannot be generalized:
  every further ability needs a further predicate and nothing relates them. It is
  `(hasCapability bird flying)` now, and `canTravel` goes the same way for the same reason —
  `travelling` is a capability and `flying` a kind of it, so what flies travels off the `genl`
  closure rather than off a second rule. Three nouns enter the upper ontology: `capability`
  under `intangible`, with `flying` and `travelling` under it, so the abilities form a hierarchy
  where two predicates formed nothing. `hasCapability` is read at **both** levels and carries no
  `relationKind`: `(hasCapability bird flying)` says the kind flies, `(hasCapability Tweety
  flying)` says one bird does, and a rule joins them rather than either being the other — the
  quantifier between them being the one this KB has always declined to guess. Its first position
  takes `argIsa` and not `argGenl` even though it holds a kind half the time, `argGenl` being
  the one argument check that is not open-world about an individual. The exception is written
  twice, because there are two things to except: `(not (hasCapability penguin flying))` at the
  kind, which stops what `penguin` inherited through `(argPreserving hasCapability 1 genl)` and
  leaves crow and eagle flying, and an `exceptWhen` on the descent rule at the member.
  `ontology_test` is where the mini-ontology's modelling decisions are pinned. *Class:* no
  label — ontology **content** rather than the surface a caller writes against (§3.8).
- **`has-prop?` and `props` accept every kind the engine marks.** `::prop-kind`, the spec gating
  both, named six of the ten kinds the special table records — so `:asymmetric`, which
  `has-prop?`'s own docstring and `docs/api.md` both list, along with `:abducible`,
  `:reifiable` and `:unreifiable`, were documented calls that **instrumentation refused**.
  Uninstrumented callers never saw it, which is why it sat there. `prop-entry` records its kind
  in the table entry under `:prop`, so the roster is derivable from the vocabulary that defines
  it, and `special-table-test` holds the marked set and the specced set equal **in both
  directions** — a kind the spec omits is a refused call, and a kind the spec names that nothing
  marks is a `has-prop?` that can only ever answer false.

**Storage, and the instruments that price it.**

- **A bulk load is decomposed, and the index write is 57% of it.** `lein bench-loadphase` loads
  one corpus repeatedly through the same door, each run with one more phase stubbed out from the
  outside in, so consecutive runs differ by exactly one phase and the deltas **sum to the
  baseline**. At 1,000,000 distinct binary facts on the `:memory` pair — 43.4 µs/fact, 23,100
  facts/s — the index write is **56.8%**, the JTMS node and premise mark 21.5%, the
  special-predicate suite 10.5%, the public `assert` prelude 6.7%, the record store 3.5% and
  canonicalization 2.0%. Two `KvBackend` decorators split the index write further: postings
  35–39%, key streams 11–15%, count maintenance 6–10% — so the **counts are priced and are not
  the lever**, recomputing them once at the end saving a tenth at most and buying it by making
  `count-with-functor` answer a stale number for the length of a load. Two write-side tricks
  measured **worse** and are reported rather than built: a transient for the whole load ran 5–7%
  slower, and sorting by trie key buys locality a hash map has nowhere to spend. The same ladder
  at 100,000 facts puts the index write at 56.5%, so no phase changes character with N.
  [docs/storage.md, "What a bulk load costs"](docs/storage.md).
- **The one write on that path that grows with the corpus is guarded, and the load reports its
  own rate.** A store posts its sentence's body to the negation memo's `:dirty` set, which is one
  `conj` per fact into a set that ends a load holding an entry per fact of the corpus. Both
  readers filter it by `:opposed` first, so `kb/note-opposed!` writes only for a body opposed
  before the store or after it. **It does not move the wall clock** (0.994x at 250,000 facts over
  five pairs, the two arms alternated A-B-B-A inside one JVM so accumulated drift lands on both);
  what it removes is a structure proportional to the corpus, which is a claim about a
  ten-million-fact load's heap. Beside it, the in-memory record store's `mark-premise` stops
  re-`assoc`ing a strength the record already carries. And `bulk-assert-facts!` reads
  `:on-progress`: `{:phase :loading :done n :elapsed-ms ms :facts-per-sec r}` every 100,000 facts
  and `{:phase :done :total n …}` after the closing settle, so the last event is a rate for the
  whole load. [docs/storage.md](docs/storage.md), [docs/api.md](docs/api.md).
- **The workload profile grows the two arms no reasoning workload runs, and prices a
  retraction.** Every arm `lein bench-profile` had was a load, a chaining run, a proof or a
  synthetic probe, so the term index and the term roster read **zero** on every corpus — which
  reads as a family nobody uses and means a family no *reasoner* uses. The **interactive arm**
  makes the reads an application makes, and its read table is the inverse of every other arm's:
  on the shipped starter, 88% `:term-index`, 12% `:term-roster`. The **churn arm** retracts a
  sample of premises and puts each one back, which is the only way `unindex-sentex!` runs at all;
  it is net-neutral by construction and says so when it is not. A fifth tally `:retracts` catches
  what that costs, kept apart from `:writes` because `:dead` — the trie nodes a removal emptied —
  is decided by what else shares the prefix rather than by the sentex. On the starter a
  retraction is ≤23.8 batch ops against an assert's 18.1. The goal report also gains **an open
  compound after an open position**, the shape the trie cannot prefix *and* the argument roots do
  not key. [docs/profile.md](docs/profile.md).
- **Eleven checks join the perf gate, and one of them was widened before it ever shipped.** The
  new checks are `flat-cache-belief-flip`, `taxonomy-belief-flip`, `retract-context-cycle-scaling`,
  `retract-merge-scaling`, `retract-nat-scaling`, `closure-membership`, `plan-scaling`,
  `quality-report-scaling`, `genl-edge-negation-recheck`, `taxonomy-edge-arbitration` and
  `context-edge-arbitration` — and **`standing-clash-reading`**, which does not gate. That last
  one costs what the entry at the top of this section moved: ordering the standing clash set at
  the read is a path `lein perf` had no check on at all, and the argument for putting it there
  was about how often a reading is asked for rather than about what one costs. It runs
  `contradictions` at `negation-arbitration`'s sizes over the identical KB, so the write cost and
  the read cost of one standing set are quotable against each other. **27 checks in the vector,
  and all 27 judge.** A read of the standing set is Ω(n log n) by construction rather than flat,
  so the number that sits above that floor is read off a full run at both ends: healthy it reads
  85.4x and 80.9x over a floor near 66x, and with the read filtering the standing set by cross
  product — the shape the claim rules out — it reads 937.8x. It ships at **175x**, twice the
  worse healthy reading and 5.4x under the defective one. Calibrating it from both ends is what
  the bound is worth having: a placeholder meaning "nobody has measured this" had to be a number
  no reading reaches, and 1000x let the cross-product shape pass. All 27 are in the default set
  and none is skippable.
  `retract-merge-scaling` was written at a 10x bound and ships at **18x**: it reads 5.66x run
  alone and 10.49x in place, because `lein perf` runs one JVM over the whole vector and a check's
  reading depends on what ran before it. That position dependence is the reason two of these
  bounds look loose beside the claim they gate, and it is a property of the harness rather than
  of the engine.

## 0.5.0 — 2026-08-07

Operating the engine, in the two senses a running process needs: what it will let a
caller do, and what it will tell an operator it is doing. The daemon authenticates and
refuses to bind an address without a credential, ships as a container image, and says
which posture it started in; every switch the build reads has a row in a table a test
keeps honest, and the four that took a presence where they meant a value now refuse a
value nothing reads; the log level is a dial a running process turns; and the failures
that look like answers — a query that returns `()`, a KB that shares another's store, a
sentence legal enough to store and wrong enough to never match — each gained something
that says so. Beside all of that, two entries are about the vocabulary rather than the
process: a name can carry two more roles than it could, which is what a KB built by
reading text needs of it, and a reader that counted a context's contents was the only one
of three that did not say `count`. Nine entries are marked **Breaking**, one of which
simplifies a store's name from two numbers to one and one of which turns a switch's name
the right way up. The three **Refusal** entries (CONTRIBUTING §3.8)
cover input that is newly refused where what 0.4.0 did with it was run a configuration
nobody asked for and report a clean pass, so no working caller loses anything it had.
Each entry says what a reader would have observed; the mechanism is in the subsystem's
doc, and the entry names it.

**Triage, for a 0.4.0 caller.** Every Breaking and Refusal entry below carries its own
one-line *Migration*; this is the index to the ones that touch something you have
written or deployed.

| If your code… | Then |
|---|---|
| names `:record-space` / `:index-space` | one `:space` — keep the record number, drop the index one |
| runs a daemon on a non-loopback `--listen` | export `VAELII_API_TOKEN` there and in every client, or it exits 2 |
| reads a daemon 401, or branches on the wire `:type` | `:unauthorized` is a new one; `GET /health` is the only route without the token |
| relies on `VAELII_RETE=0` running the sweep | it means off now; unset, or `=1` for on |
| sets `VAELII_NOHIER` | it is `VAELII_HIER`, the other way up — `VAELII_NOHIER=1` becomes `VAELII_HIER=0` |
| sets `VAELII_QUERY_ENGINE` / `VAELII_QUERY_STRATEGY` | a name outside the roster is refused rather than silently running the default |
| sets `VAELII_WEB_PORT` for `lein browser` while `-main` stayed on 3000 | it moves both; pass `--port 3000` to pin `-main` |
| lists KBs out of a search-path directory holding more than 200 | name the ones that matter in the catalog file |
| depends on vaelii and has no SLF4J provider of its own | add one — `org.slf4j/slf4j-nop` no longer arrives transitively |
| branches on what `term-role` answers | `:sense` and `:lexeme` are two new answers — add arms, or a `default` |
| writes a `lex`-namespaced predicate | it names a lexeme now, and a lexeme names no relation |
| calls `core/context-size`, or sends the daemon `:context-size` | both are `count-in-context` — same arguments, same answer |
| compares two compound terms with `different` | a merged symbol inside one now makes them equal, where it did not |
| sets `VAELII_ASP_SOLVER` to a name outside `clingo`/`clasp` | it is refused at `open-kb` rather than silently running auto |

- **Breaking: a name can carry two more roles — a sense, and a lexeme.** `term-role`
  answers `:sense` for a disambiguated type (`abrasive-grit`) and `:lexeme` for a symbol in
  the `lex` namespace (`lex/fool's_gold`), so its documented domain gains two values a total
  `case` has no arm for. Two things move at a `:strict` front door with them: a lowercase
  dashed name is a legal unary type where it was refused, and a lexeme applied to arguments
  is refused (`:lexeme-functor`), a surface form naming no relation. *Migration:* a `case`
  over `term-role` gains `:sense` and `:lexeme` arms, or a `default`; nothing else changes
  unless you wrote a `lex`-namespaced predicate, which names a lexeme now and cannot be
  applied to anything. `docs/naming.md`.
- **Breaking: `context-size` is `count-in-context`.** The three O(1) cardinality readers
  are one family and two of them said so; the third delegates to a protocol method already
  called `count-in-context`, so the name it now carries is the one it always answered to a
  layer down. The daemon's op keyword moves with it. *Migration:*
  `(v/context-size kb ctx)` becomes `(v/count-in-context kb ctx)` and `{:op :context-size}`
  becomes `{:op :count-in-context}` — same arguments, same answer, and the old spellings are
  gone rather than deprecated. `docs/api.md`, `docs/indexing.md`.
- **Breaking: `different` descends into compound arguments.** It normalized each argument
  with one lookup in the equality closure, and the closure is keyed by symbol — so a compound
  was never found in it and `(different (QuantityFn 5 Kilogram) (QuantityFn 5 Kg))` answered
  *different* with `(sameAs Kilogram Kg)` believed. It replaces symbols at every depth before
  comparing, the congruence its documentation always described. *Migration:* a goal comparing
  two compounds can newly answer false where a merge reaches inside one; comparing symbols is
  unchanged. `docs/equality.md`.
- **Breaking: one space number names a KB's stores, `:space`.** `open-kb` takes a single
  number where it took `:record-space` and `:index-space`, and it defaults to 0; a
  `:disk` KB's derived directory is `space-<n>`, and the suite owns a block of two db
  numbers rather than four (scratch 15, isolated 14). *Migration:* `{:record-space 2
  :index-space 3}` becomes `{:space 2}` — keep the record number, drop the index one;
  either retired key is refused by name (`:type :unknown-option`) rather than ignored.
  Pass `:dir` to name a durable directory the derived spelling does not reach.
  `docs/storage.md`.
- **Breaking: the daemon authenticates, and refuses to bind an address without a
  token.** With `VAELII_API_TOKEN` set, every request carries `Authorization: Bearer
  <token>` or is answered 401 with `{:ok false :type :unauthorized}` — a new `:type` on
  the wire — and `GET /health` is the only route that answers without it. What the daemon
  binds decides what it requires: `--listen` naming a non-loopback address without a token
  is one line on stderr and exit 2, where 0.4.0 logged a warning and served the whole write
  block to anything that could reach the port. *Migration:* export `VAELII_API_TOKEN` for a
  daemon that names an address and give the same value to every client that reaches it;
  `vaelii.client` reads the same variable and takes `:token`. Nothing changes on the
  loopback default. `docs/operations.md`, "Daemon — `vaelii.serve`".
- **Every switch the build reads has a row, and a test keeps the roster honest.**
  `docs/operations.md` gains a configuration table — 56 environment variables and JVM
  system properties, grouped by who sets one, each with where it is read, its legal
  values, its default, and the one thing it decides. `config_surface_test` pins the
  names against `test/golden/config-surface.edn` in both directions and checks each
  `file:line` citation against the line it names, so the table cannot drift from the
  code without a failing test. CONTRIBUTING §3.8 files a renamed or removed switch as
  **Breaking**.
- **Refusal: the four harness switches read a value instead of a presence.**
  `VAELII_RETE` and the hierarchical-retrieval switch were membership tests, so `=0` ran
  the sweep it names and an exported-but-empty variable ran one nobody asked for; the two
  query switches took a bare `(keyword …)`, so a misspelt engine ran the *default* and
  reported a clean pass for a configuration nothing exercised — the worst shape a test
  switch can have, since the result reads as evidence. All four take the engine's boolean
  vocabulary now and refuse anything else by name, and a test calls each reader with the
  properties cleared so the table's **Default** column fails rather than merely reading
  wrong. All four are read only by the test harness, which is what keeps a silent change
  of sense inside a Refusal rather than making it a ninth Breaking. *Migration:* none for
  a value in the vocabulary; a job relying on `=0` meaning *on* now gets the sweep off.
  `docs/operations.md`, "Developer — the suite and the scripts".
- **Refusal: the ASP backend switches are read against their domains, at the door.**
  `VAELII_ASP_SOLVER` took a bare `(keyword …)`, so a misspelt backend matched no arm of the
  selector and ran **auto** — a run pinned to clasp could use clingo and report a clean pass
  for a backend nothing exercised. `VAELII_CLINGO_MAX_BYTES` parsed with a bare
  `Long/parseLong` inside a cached delay, so a non-numeric value threw from the first ASP
  solve rather than from the configuration that was wrong. Both go through `config/check!`
  now — refused at `open-kb`, by name. *Migration:* none for a legal value.
  `docs/operations.md`.
- **Breaking: `VAELII_NOHIER` is `VAELII_HIER`, and the sense is the other way up.**
  A switch that carries the negation in its own name makes `=0` mean *on*, which is the
  one thing a reader must not have to work out at a glance — and the entry above had
  just made the value load-bearing, so the two had to move together or `=0` would read
  as the fallback path it now selects. `VAELII_HIER` defaults `true` (the set-algebra
  retrieval), and `VAELII_HIER=0` routes every context-scoped match through the
  reference nested fan-out. *Migration:* `VAELII_NOHIER=1` becomes `VAELII_HIER=0`; a
  `VAELII_NOHIER` left set is simply unread, since a variable cannot be refused by name.
  `docs/operations.md`.
- **The log level is a dial a running process turns.** `vaelii.core/set-log-level` takes
  one of `:error :warn :info :debug :trace` and installs Trove's console backend at it;
  `log-level` reads back what is in force, and `VAELII_LOG_LEVEL` says it at startup (a
  value outside the five is refused by name). Unset, the engine installs **no** backend
  at all, so an application holding its own `taoensso.trove/*log-fn*` keeps it. Three
  `:debug` statements are what make turning it up worth doing: what a chaining run
  concluded and how long it took, what a settle cost and found, and the rule a dropped
  conclusion came from. `docs/operations.md`.
- **Breaking: `VAELII_WEB_PORT` moves `-main`'s port, and not only `lein browser`'s.**
  `dev-repl` read the variable and `-main` did not, so `VAELII_WEB_PORT=3011 lein run -m
  vaelii.web` bound 3000 and logged 3000. Both read one `default-port` now: the variable,
  else the `vaelii.web.port` property, else 3000; an explicit `--port` still wins.
  *Migration:* a deployment that set the variable for `lein browser` while relying on
  `-main` ignoring it now moves both; pass `--port 3000` to pin `-main`.
- **Breaking: a search-path directory is probed for its first 200 entries, and a KB
  below the cut no longer appears on `/kbs`.** `sources` is recomputed per request, which
  is what lets a corpus appear with no restart and what made the scan unbounded — a
  `classify` per candidate, and a size estimate per `:store` one, on every page load.
  `catalog/max-discovered` bounds it, and the cut is named on the page and in the log,
  since a list that quietly ends early reads as "this machine has no other KBs".
  *Migration:* name the ones that matter in the catalog file to list them regardless of
  the count. `docs/catalog.md`.
- **The front door says what a legal-but-wrong sentence should have been.** `(isa Muffet
  Dog)` breaks no naming invariant, so it stored a two-place relation nothing reads and
  `(isa? kb 'Muffet 'Dog)` answered false with nothing to search for. `nm/advice` reads
  intent where `problems` reads the invariants: it recognizes the shape and logs a
  `:warn` once per process spelling the rewrite that was meant. Beside it, a
  `:no-placement` drop names `genlContext` and points at the `:rule-context` /
  `:fact-contexts` already on the entry. `docs/naming.md`.
- **A second `open-kb` defaulting onto the shared in-RAM space now warns**, naming both
  fixes — give the KB its own number, or name `{:space 0}` explicitly to say the sharing
  is meant. A warning rather than a refusal, since sharing the space is how `recover`
  sees the same records and how a base is mounted. `docs/storage.md`.
- **Refusal: the CLI checks each command's argument count before it dispatches, and
  `help` names what each one takes.** `dispatch` reached into `args` with `nth`, so `lein
  cli assert '(dog Rex)'` answered `error: IndexOutOfBoundsException` — true about a
  vector, no help to someone who left off a context — and a long line was worse, since
  the extra operand was dropped in silence. One table now carries every command's arity,
  operands and gloss, so `check-arity!` and the usage text cannot go out of step.
  *Migration:* none for a call already at the right arity; `lein cli help` prints the
  count each command takes. `docs/operations.md`.
- **`docs/troubleshooting.md` is a new page, indexed by symptom rather than by
  subsystem.** The engine's hardest failures are the ones where nothing goes wrong — a
  query answers `()`, an `assert` returns a handle, and both are legitimate values no
  error distinguishes from the answer that was wanted — so a reader has to already know
  the cause to find the page explaining it. Nine symptoms, each with what you would have
  observed, how to confirm it in one call, and the fix.
- **`lein lint` gains a versions check, and the kondo row notes a local/CI version
  mismatch.** The `:with-foreign` pin and `defproject`'s own version are cut together and
  nothing held them to it: the 0.4.0 bump left the pin naming `0.3.0`, so every
  `lein with-profile +with-foreign` command failed to resolve. `lint-versions` reads that
  pair and the `lein-cloverage` version stated twice, failing when either disagrees. The
  kondo row prints a `NOTE` — never a failure — when the local binary is not the version
  CI pins, since a newer kondo infers more than an older one flags.
- **Three doc samples now print what they actually produce, and `prove`'s docstring says
  it counts proofs, not answers.** `prove` returns one solution per derivation, so a goal
  reachable both as a materialized fact and as the rule concluding it comes back twice
  with equal maps — wrap it in `distinct` for an answer set, or reach for `query` / `ask`,
  which project to the goal's variables and answer each binding once.
- **The daemon ships as a container image**, with a two-stage `Dockerfile` and
  `docker-compose.yml`: a build stage that runs `lein uberjar`, and a runtime stage of a
  JRE and the jar alone. The container binds an address, so the token is required — an
  image run without `VAELII_API_TOKEN` does not start rather than serving unauthenticated
  — and one container per volume, a second opener being refused `:disk-locked` rather than
  scaled, which is why the compose file carries no `replicas:`.
  `docs/operations.md`, "Container — the daemon as an image".
- **A reflection warning and an uncalled public var now stop the build.** Both signals
  were already emitted and neither was read. `lein lint` gains two rows: **`reflect`**
  compiles `src` and `bench` and fails on any reflection, auto-boxing or primitive-recur
  warning, and **`unused`** reads clj-kondo's analysis over `src test bench` and fails on
  a public definition with no usage, against `scripts/unused-publics-baseline.txt`. Ten
  warnings had to go first, none in `src`. CONTRIBUTING §1.1.
- **Breaking: `org.slf4j/slf4j-nop` no longer reaches a consumer's classpath.** It sat in
  top-level `:dependencies`, so every application depending on vaelii inherited it too,
  where it could win SLF4J's provider race against that application's own backend and
  silence it — the one thing a library must not do on a consumer's behalf. It lives in
  the `:dev` and `:uberjar` profiles now, so every entry point this repo ships still
  carries it while `lein deploy` publishes it as a test-scope declaration a consumer does
  not resolve. *Migration:* an application that ships Jetty, had no provider of its own,
  and relied on vaelii's to keep it quiet now sees SLF4J's "no providers" line again —
  add `org.slf4j/slf4j-nop`, or any other provider, as its own dependency.
  `docs/operations.md`.
- **A public `--listen` bind with no `VAELII_ALLOWED_HOSTS` now warns.** Naming an address
  drops the `Host` allowlist to every `Host` answered — a deliberate default, since a
  reverse proxy legitimately sets its own and an operator cannot always enumerate it in
  advance — but nothing said so at startup. `host-posture` names the policy
  (`:allowlisted` / `:open`) beside the token question, and a public bind left unset gets
  its own warning, apart from the token and TLS lines so a reader knows which check is
  missing.
- **`docs/troubleshooting.md` and `docs/storage.md` now name `:type :unknown-backend`.**
  `open-kb` throws it from five call sites — an unknown `:backend` sugar name, the one
  `{:records :memory :index :disk}` pairing the axes refuse, and an unknown `:records` /
  `:index` / `:tms` kind — and none carried a line in either doc. The new entry reads the
  other key each throw's `ex-data` carries to say which of the five it is.

## 0.4.0 — 2026-08-05

Correctness fixes found by reading the engine against its own stated invariants, in
the places 0.2.0 and 0.3.0 did not reach: a backward-chaining loop guard that made a
conjunctive query answer nothing, doors that disagreed about what they would accept,
an index trusted without being checked against the records it describes, slots and
keys that let arrival order decide belief, and derived caches a settle read one
revival out of date. Thirteen entries are marked **Breaking** — they refuse input
0.3.0 accepted, rename what it exported, or change an observable contract — which is
why this is 0.4.0. The **Refusal** entries (CONTRIBUTING §3.8) cover input that is
newly refused where what 0.3.0 did with it was corrupt state or answer a different
question in silence, so no working caller loses anything it had. Each entry says what
a reader would have observed; the mechanism is in the subsystem's doc.

**Triage, for a 0.3.0 caller.** Every Breaking and Refusal entry below carries its own
one-line *Migration*; this is the index to the ones that touch source you have written,
so the rest can be read at leisure.

| If your code… | Then |
|---|---|
| hands `assert` text it did not read as EDN | it is refused (`:shape`) — fix the producer |
| writes `exceptWhen` literals like `(lives_in ?x cold_place)` | spell them to the invariants; re-check any rule 0.3.0 left bare |
| spells an `edit!` batch `{:adds …}` | spell it `{:add […] :remove […]}` — the old key wrote nothing |
| names one of `:record-space` / `:index-space` | name both, or neither, in every opts map |
| passes `:direction` to `assert` on a non-rule | it is refused; a rule takes it and now acts on it |
| states one rule two ways (bare `implies` after a `set/*Rule`) | the slots join by content; `retract!` and re-assert to narrow one |
| calls `edit` or `edit-with-consequences` | they are `edit!` and `edit-with-consequences!` — the wire op stays `:edit` |
| matches `:bad-opt`, or a `:shape` from a non-map `opts` | match `:unknown-option` |
| reads a dump's `meta.edn` dialect | it is `:vaelii` |
| stores skolem witness names across runs | the names moved; rebuild from the assertions (`export!` / `import!`) rather than carrying both spellings |
| parses a daemon 500 for a client mistake | it is a 400 with a `:type` |
| writes `(ist Ctx S)` with other than three elements | it is refused with `:shape` |

- **A conjunctive query could answer nothing while each of its conjuncts answered.**
  `[(anc Tom ?y) (anc Tom ?z)]` was empty where `(anc Tom ?y)` answered twice, because
  the per-path loop guard grew for a whole frame and a queued conjunct is a sibling of
  the expansion, not a descendant. Silent in every direction: forward chaining and the
  node engine both answered, `provable?` said false, `prove-within` reported `:status
  :complete`, and the planner became semantic. `docs/inference.md`, "The loop guard's
  scope is the subtree, not the frame".
- **Breaking: `assert` refuses a sentence that is not an s-expression.** A string — what
  a failed EDN read hands back, from `impl.cli`'s `read-arg` and the daemon's `:args` —
  was stored, indexed and believed as an object no query can match; `nil` likewise; a
  symbol, number or map threw a bare `UnsupportedOperationException` with no `:type`.
  `check` refused all five, so the door built to predict `assert` disagreed with it.
  *Migration:* nothing a working caller sent is refused; fix the producer that handed
  `assert` unread text, and discriminate on `:shape`.
- **Breaking: an `exceptWhen` query's literals are held to the naming invariants.**
  `(exceptWhen (lives_in ?x cold_place) …)` stored a literal `docs/naming.md` says is
  refused, as an exception no query could match — so the rule read as guarded and fired
  as bare. Both doors now read each conjunct, before the rule is stored, so a refused
  exception leaves no bare rule believed. *Migration:* spell the exception's literals to
  the invariants (`livesIn`, not `lives_in`), and re-check any rule 0.3.0 left bare.
- **Breaking: an `edit!` batch key nothing reads is refused.** `{:adds […]}` bound nil,
  so `edit!` wrote nothing and reported `{:added [] :removed {…0}}` — a success — while
  `check-edit`, whose job is to predict exactly that, reported no problem. Over the
  daemon it was a `200 {:ok true}` for a write that did not happen. *Migration:* spell
  the batch `{:add […] :remove […]}`; a batch under any other key wrote nothing.
- **Breaking: naming one in-RAM space number and not the other is refused.**
  `:record-space` and `:index-space` default independently, so
  `{:backend :memory :record-space 77}` paired a private record store with the
  process-default index every other in-memory KB writes. `assert` then found the other
  KB's handle, read it as a duplicate, **stored nothing**, and returned a handle `in?`
  answered true for. A fork's `:base` and `:overlay` halves take the same keys and are
  refused the same way. *Migration:* name both or neither, in every opts map.
- **A durable index is checked against the records it claims to describe.** `layout.edn`
  gates the index's key shape; nothing gated its coverage, so a short index opened
  clean, answered short forever and re-cemented its own stamp — and re-asserting a fact
  it could not find minted a second handle for a sentence already stored. Three ways in:
  a torn `kv.log` tail, a directory grown under a derived-index mode, and a crash
  between the record write and the index batch. `docs/storage.md`.
- **Breaking: `assert` acts on `:direction` instead of accepting and dropping it.** Only
  `assert-rule` read the key, so a rule asserted `{:direction :backward}` stored `:both`
  and forward-chained, materializing the cross product a backward-only rule exists to
  avoid. A `:direction` on a non-rule, one contradicting the sentence's own wrapper, and
  a value outside the roster are refused rather than resolved. In the same pass a
  non-map `opts` answers `:unknown-option` from both doors, where `check` said `:shape`.
  *Migration:* spell the direction `:backward` (`:forward` `:backward` `:inert` `:both`);
  a `check` caller matching `:shape` for a non-map opts matches `:unknown-option` now.
- **Breaking: a re-asserted rule's direction and defeasibility resolve by content.**
  Neither slot is in the identity key, so a rule stated two ways resolves to one record
  and the second spelling was dropped — letting arrival order decide a slot that decides
  belief. A bare `implies` after a `set/inertRule` stayed inert and never fired; after a
  `set/defaultRule` it stayed defeasible and lost to a monotonic rival it should have
  tied with. The resolution reaches conclusions already derived, since a justification
  bakes the rule's contribution in as its `:strength` at fire time.
  `docs/canonicalization.md`. *Migration:* the join only widens a slot; to narrow one,
  `retract!` the handle and re-assert the intended spelling.
- **The derived caches are reconciled with what `clear-defeats!` revived.** A settle
  lifts last settle's defeats at its top, but the cached closures were refreshed only in
  `settle-finish` — after `constraint-nogoods` had read them — so discovery asked its
  question against a vocabulary one settle out of date. A `P`/`¬P` pair made visible by
  a revived `genlContext` edge went unarbitrated and `retract!` returned with both
  believed, a state `recover` over the same records disagrees with.
- **The disk KV index reads and publishes its RAM map under the lock.** `apply-ops!`
  read `@data` before acquiring and published after releasing, while `compact!` runs on
  the durability daemon's executor — a thread the single-writer contract says nothing
  about — so a compaction in either window rewrote the log from a map missing the
  in-flight write. `kv-clear!` was sharper: a compaction between its truncate and its
  publish wrote the entire pre-clear map back over the log just emptied.
- **Breaking: a client's mistake answers 400 with a `:type`, not 500 with none.**
  `docs/operations.md` promises every `{:ok false}` carries the type the engine threw;
  an unreadable body, a wrong argument count and an unknown op all answered untyped, the
  first two as 500s. The engine's whole refusal vocabulary now answers **400**, unlogged
  — answered 500 they count as backend faults at every reverse proxy and 5xx alarm.
  *Migration:* a client branching on the status code should branch on `:type`; every
  `{:ok false}` carries a non-nil keyword.
- **The browser's `/propose/*` EDN read catches `Throwable`**, as every other
  untrusted-EDN read in the namespace already does. A deeply nested form raises
  `StackOverflowError`, which an `Exception` catch let escape — and the browser has no
  exception middleware, so it left the handler entirely.
- **Refusal: `query` refuses a non-map `opts` and a negative or non-integer
  `:max-depth`.** Both read as "no depth", which is not an error condition but a
  *different question* — the no-rule-expansion answer, returned as if it were the
  bounded one asked for. `{:max-depth 0}` is admitted: it is that answer asked for by
  name. *Migration:* none for a working caller.
- **Breaking: `edit!` refuses what `check-edit` reports, before applying anything.** The
  two disagreed in both directions: a 4-element `:add` entry applied with the extra
  silently dropped where the dry run reported `:shape`, and a non-sequential entry threw
  a bare `ISeq` error from every door. An unknown `:remove` handle is refused before any
  entry is applied, so a checked-clean batch cannot half-apply. *Migration:* a
  remove-if-present batch filters its handles through `in?` first.
- **The recursive-literal hold-back keys on the peeled predicate.** A `not`- or
  `ist`-headed consequent read its own frame as the predicate, so every frame-headed
  antecedent was "the recursive literal" — two orderings of a negated-head rule minted
  two handles, and a genuinely recursive rule with a negated head lost the hold-back,
  turning right-recursion left-recursive.
- **Breaking: a skolem witness is a function of its rule's content, not its handle.**
  Retracting and re-asserting the same rule re-fired to a *different* witness, so a fact
  stated about the old one silently stopped co-referring — and two KBs holding the same
  knowledge in different orders stored different `termOfUnit` content, a handle in
  stored content that order independence rules out. `docs/skolem.md`. *Migration:*
  rebuild the KB from its assertions (`export!` / `import!` replays firings) rather than
  carrying both spellings.
- **Breaking: `edit` is `edit!`, and `edit-with-consequences` is
  `edit-with-consequences!`.** The batch's `:remove` half runs the same
  `retract-storage!` sweep `retract!` runs, while the name read as additive — the one
  gap in the `!` roster the convention exists to close. *Migration:* rename the calls;
  the wire op stays `:edit`, as `:retract` stays for `retract!`.
- **Breaking: `:bad-opt` is retired, and one compression spelling survives.** Two
  keywords split one failure class on no rule a reader could predict — seven sites said
  `:bad-opt` where thirty-four said `:unknown-option`. *Migration:* discriminate on
  `:unknown-option` and `:unsupported-compression`.
- **Breaking: the dump's `meta.edn` names its dialect `:vaelii`.** Decorative on the read
  side — the frame decides how a sentence is reconstructed — but it is a value in the
  frozen format and a documented key of `import-dump`'s return, so the name it carries
  is now-or-never. *Migration:* a reader matching the old value matches `:vaelii`;
  `import-dump` reads dumps written either way.
- **The node engine's claimed-key reads each guard's identity, not the guard count.** Two
  distinct rules, each carrying its own `exceptWhen`, can rewrite one goal to the same
  canonical residual through the `genl` fan; keyed on the count the two children were
  one key, so the second was dropped before it was enqueued and every answer only its
  exception admits was lost — silently, on the path `query` routes to whenever
  `:max-depth` is given. `docs/inference.md`.
- **A belief flip on a visibility `except` queues the same re-check as its arrival.**
  Only the store and removal chokepoints called `recheck-except`, so an except *defeated*
  by a settle's resolution revived nothing it hid: backward proving answered yes while
  the store held nothing, and which belief set the KB ended with depended on the order
  the except and its defeater arrived.
- **`recover` reads only positive, atomic declarations into the taxonomy.**
  `sentexes-with-functor` returns both polarities and the rebuild arms destructure the
  positive shape positionally, so a stored `(not (genl a b))` bound its inner sentence as
  a taxonomy node and nil as the other — poisoning every cache on any recover, the
  default `{:recover? :auto}` reopen included.
- **A `:neg` nogood is an at-least-one in every reader.** The ASP translation's soft
  branch emitted only the positive body atoms, so a `:neg`-only nogood — what
  `set/softConstraint` over negated choice literals produces — emitted its violation
  witness as an unconditional fact: no steering pressure, and `:violated` reported a
  satisfied at-least-one as broken. `docs/solving.md`.
- **`conflicts` and `contradictions` are content-ordered.** Each report's sides were
  already ordered by content; the *list* came off a hash set of handle-keyed nogoods, so
  which pair `(first (contradictions kb))` returned was an answer about which was typed
  first. `docs/nmtms.md`.
- **Refusal: the connective frames are shape-checked at every door.** An `implies` at
  arity 2 threw a bare `IndexOutOfBoundsException` while arity 4 stored a silently
  truncated rule `check` read as clean; `(not A B)` stored as a positive fact whose
  record and index disagreed; a bare symbol passed as a rule literal was accepted,
  unmatchable; and a non-finite measure magnitude stored cleanly, then threw out of every
  later duration goal in the context. *Migration:* nothing a working caller sent is
  refused — every one of these stored an object no query could match.
- **Refusal: the last open rosters close.** `find-terms` and `abduce` take key rosters (a
  misspelt `:mtch` ran the prefix default; a misspelt `:keep?` tore down the scratch
  context whose handles the caller meant to commit), the CLI refuses a flag outside its
  roster, `escalate` refuses a floor outside 0–7, and `import-dump` refuses an unknown
  `:framing` where it guessed a reader and failed as a `ZipException`. *Migration:* spell
  the key or flag as the refusal's roster lists it.
- **Refusal: the web and serve entry points refuse what their grammars do not know.**
  `vaelii.web --listen` with no address parsed to a nil host — Jetty's wildcard bind,
  with the Host allowlist reading nil as *any* — so a truncated command line put the
  browser's unauthenticated write routes on every interface with the rebinding guard
  off. `serve` read its positionals as a prefix, so `4200 --listen 0.0.0.0 /var/lib`
  dropped the directory and ran a disk daemon in memory. *Migration:* none beyond
  completing the command line.
- **Refusal: the opts and shape rosters reach the remaining doors.** The roster guard
  held at `assert`, `why`, `query` and `open-kb`, and every other door took the misspelt
  key in silence — answering a different question than the one asked. Now refused: an
  `open-kb` mount or durability key without its axis, an opts key nothing reads at
  `forward-chain`, the extent readers, `preview`, `export!`, `import!` and the anytime
  budget maps. *Migration:* spell the key as the refusal's roster lists it.
- **Refusal: the operator's mistakes answer in one line.** A CLI flag missing its value
  bound nil in silence — `lein cli assert '(dog Muffet)' Ctx --strength` stored known-true
  content at `:default` — and now exits 1 naming the flag; `--memory --dir` is refused as
  a contradiction. *Migration:* none beyond completing the command line.
- **The browser and CLI survive what they read.** The repl loop and the CLI command arm
  catch `Throwable`, so a deeply nested form answers `error:` and a next prompt; the
  browser's retract POST makes the `check-edit` round-trip `docs/operations.md` promises,
  so a stale handle answers the problem panel rather than a success-styled "Retracted 0
  sentexes".
- **Refusal: every durability switch is read against a domain, and a value outside it
  fails the open.** Each of the thirteen checkable `vaelii.*` / `VAELII_*` switches was a
  membership test or an equality against one spelling, so none of them had a wrong value —
  every misspelling was the *other branch*, silently: `vaelii.disk.auto-compact=disabled`
  read as compaction on, and `vaelii.disk.fsync=always` as the three-second tick, the level
  the operator was trying to leave. The three numeric reads had no catch at all.
  *Migration:* none for a working setup, but two spellings now *act* where they were
  ignored — `vaelii.disk.tokens=1` and `vaelii.index.snapshot=1` turn their features on,
  and `vaelii.disk.lock=0` disables the lock. Spell what you mean. `docs/storage.md`.
- **Refusal: the mapped index image refuses the platform it corrupts on.** The image
  publishes by renaming a new file over the live one while it is mapped, which is what put
  `vaelii.index.snapshot` on macOS and Linux only — `docs/storage.md` said so and nothing
  enforced it, so on Windows the publish failed part-way through a four-file commit, naming
  neither the cause nor the fix. *Migration:* none — the property never worked where it is
  now refused. `docs/storage.md`.
- **Breaking: `assert-rule` refuses a rule literal whose predicate is a variable.**
  `(implies ((?p ?x ?y) (transitive ?p)) (?p ?y ?x))` asserted cleanly and was indexed
  under `?var0`, which no arriving fact and no goal can spell — so the rule answered no
  backward goal at all and fired forward only when the concrete-predicate antecedent
  beside it arrived. Two arrival orders, two answers, from a rule the engine reported as
  accepted. An `:inert` rule is exempt, which is what `CoreContext`'s decontextualized-
  predicate lift is. *Migration:* assert the instantiated rules, one per predicate the
  metarule ranged over.

## 0.3.0 — 2026-08-04

Correctness fixes across the durable index, the snapshot, the JTMS, the export dump
and the bounded prover, a sweep that gives every refusal a `:type`, the one wire
contract 0.2.0's own sweep left qualified, and the serialization both servers' storage
layer already assumed. Then a run of **inference and belief** work: two orders that
reached two answers, the two doors that disagreed about an inherited claim, and two
enumerations that grew with the vocabulary rather than with their own answer. Eight
entries are marked **Breaking** — they refuse input 0.2.0 accepted or change an
observable contract, which is why this is 0.3.0 and not 0.2.1; the rest are compatible.

- **Breaking: the daemon's refusal `:type` keywords are plain** — `:not-edn`,
  `:cross-origin`, `:bad-host`, `:body-too-large`, where the namespace serving them
  qualified each one. This finishes tree-wide what 0.2.0's own breaking entry claimed.
- **Breaking: both servers hold one request-body ceiling.** The cap and its
  `VAELII_MAX_BODY_BYTES` override (16 MiB) live in `vaelii.impl.guard`, which both
  read, so the browser answers **413** for an oversized form body where only the daemon
  did. A daemon read is also fully realized **inside** the write monitor — `wire-safe`'s
  walk is what realizes a lazy answer, so running it after the monitor released let a
  `:query` straddle a concurrent `:assert`.
- **Breaking: the browser serializes its writes.** Jetty serves the write routes on a
  thread pool, so two POSTs were two writers — where the storage layer is written on the
  promise that they are not. Interleave two and the WAL holds both frames while the RAM
  map holds one, so the running index and the one replayed on the next open disagree.
  The browser now takes one process-wide monitor around every content write, as the
  daemon always did; a concurrent write waits rather than racing.
- **Every `ex-info` the engine throws carries a `:type`.** Twenty refusals threw an
  untyped map, so a caller had to guess from which keys were present. Two forms that
  threw a raw Java exception now answer instead: `(genl ?x ?x)` / `(disjoint ?x ?x)`
  answer the question one variable in both positions asks.
- **Breaking: an `ist` form must have exactly three elements.** 0.2.0 read `assert` and
  `check` positionally, so `(ist Ctx S junk)` asserted with the extra silently ignored
  and `(ist Ctx)` raised a raw `IndexOutOfBoundsException`. Both refuse with `:shape`.
- **The durable index is gated on its key layout at open.** A log whose stamp does not
  match `kv/index-layout-version` is cleared, rebuilt from the records and restamped,
  `:recover?` notwithstanding; without the gate such a log replays cleanly and then
  misses every read whose key shape moved. **A 0.2.0 durable store carries no stamp, so
  its first open under 0.3.0 pays one automatic reindex**: O(records), logged at `:warn`,
  paid once. `docs/storage.md`.
- **Breaking: `open-kb` refuses a `:base` whose durable index is at an older key
  layout** (`:stale-index-layout`). The repair is a write and a base is mounted
  read-only, so the refusal names the one place the rebuild can happen: open that
  directory as a KB, then mount the fork over it.
- **Breaking: `(fork (fork base))` is refused** (`:stacked-fork`), which is what
  `docs/overlay.md` has always stated.
- **Breaking: `open-kb` refuses a `:recover?` setting it does not name.** `:auto` is the
  default, `true` an alias for it, `:warn` and `false` the rest; any other value read as
  the warn branch and handed back an empty TMS over a store that is not empty, which
  answers `[]` to everything. A stale derived index is dropped on open whatever
  `:recover?` says.
- **Breaking: `close!` releases a durable fork's own directory.** A fork's writable half
  takes the same exclusive lock as any durable KB, so without its own `:dir` it could
  never be handed to another process short of exiting the JVM. 0.2.0's docstring promised
  the opposite, so code that closed a fork in a `finally` and kept reading it worked and
  now does not.
- **A failed compaction takes its temporary files with it.** A rewrite that threw closed
  its handles and left `<log>.compact` behind, and the next compaction in the same
  session opened that temp and appended to it — its replay then put back records deleted
  in between. The cleanup is scoped to the pre-commit phase: past the marker the temps
  are the only complete copy.
- **A failed open gives back the directory lock with no handles still on it.**
  `open-kv-backend` and `open-token-log` replayed their logs outside any guard, so a torn
  frame propagated to a caller that answers a failed open by releasing the lock —
  leaving it released while this JVM still held an open handle.
- **A fork's merged `kv-entries` is realized under its monitor.** Both halves were lazy,
  so the seq handed back from inside the lock realized outside it. An export of a fork
  taken while anything wrote it projected two states at once.
- **The rete alpha registry is synchronized.** It is JVM-lifetime shared state reached
  from the store observer hooks, which fire on whichever thread is writing, and a
  `HashMap` racing its own rehash can leave a reader spinning on a probe loop that never
  terminates. Its check-then-put is one step too, so two callers cannot leave the loser's
  alpha permanently unmaintained.
- **`load-source` claims the catalog under one monitor.** The busy test, the
  already-loaded test and the registration were three separate reads, so two requests
  arriving together each passed all three and spawned a loader.
- **The browser reads untrusted EDN under `Throwable`, as the daemon does.** A deeply
  nested form overflows the reader's stack with a `StackOverflowError`, which an
  `Exception` catch lets escape — a 500 where an unreadable term is the ordinary answer.
- **The index snapshot's roots-fallback blob is validated like the sections beside it.**
  `roots-fallback.nippy` carries argument-root postings, which are primary index truth,
  and a missing or torn blob loaded as `[]` behind a warning while every argument-root
  read answered `#{}` out of a snapshot that opened clean. The meta records the blob's
  count and byte length, and the load thaws strictly.
- **The mapped index snapshot survives a JVM shutdown, and a failed save leaves the
  previous image intact.** The stamp is taken against the records before a byte moves,
  durability registrants close in phases, and every section lands in a `.tmp` until the
  swap. A failed *open* likewise gives back the handles it took.
- **An export dump carries every provenance stamp, and `export → import → export` is
  byte-stable.** The provenance walk covers justification handles as well as sentex ones,
  and import stores a justification's antecedents as a **vector**, the shape the engine's
  own write path stores.
- **The JTMS dedup index carries the identity of the TMS it mirrors.** A nested chain
  over a second KB — legal from an `:on-progress` callback, with overlapping handle
  spaces — could answer one KB's dedup question out of the other's supports. Keys coerce
  fixnum boxing to `Long` at the boundary, since the map compares with Java `equals`
  where the scan compares with `=`.
- **`prove-within` prepares its goal**, through the same `prepare-goal-for-read` every
  other read path takes, so a reifiable NAT or a merge-retired spelling is the same
  question under the bounded prover that it is under `ask`.
- **The rete forward matcher fans over predicate-`genl` sub-predicates at every arity**,
  as the reference `res/match-pattern` does. Fanning only for a two-element sentence gave
  the opt-in matcher a different belief set on any rule whose antecedent had another
  arity.
- **A firing refused at derive time comes back when its exception releases.**
  `place-conseq` does not place a firing whose `exceptWhen` exception already holds, and
  such a firing left no justification and nothing in `jtms/blocked` — so a settle pass
  could not see it and the conclusion stayed suppressed after the block lifted. The same
  knowledge in the other order concluded it. The refusal is recorded as `[rule handle,
  bindings]`, capped at 4096 entries per rule. `docs/exceptions.md`.
- **Five order-independence repairs.** `contradictions` names the same side of a clash
  whatever order the two arrived in; the two settle sweeps sharing one exposure-instance
  budget walk their moved region in content order; `query` with `{:proof? true
  :portfolio? true}` returns each answer once; `negation-nogoods` writes with a
  compare-and-set; and the node engine's inline join plans with the `:est-override`
  belonging to its registry leaf.
- **A forward rule fires on a claim argument-position preservation licenses**, so
  `sentexes-matching` and `ask` stop disagreeing about the same knowledge.
  `(argPreserving largerThan 1 genl)` beside `(largerThan dog cat)` licenses
  `(largerThan chihuahua maine_coon)`, which `ask` reached while the fixpoint fired only
  on the claims that were written — so the conclusion it never drew had no `why`, no
  retraction path and no way to be an antecedent. The join contributes the handles the
  inherited claim was read from, so retracting any of them withdraws the conclusion. One
  asymmetry is left: a justification confers the weakest class it rests on, so a
  `:monotonic` claim declared preserved by a `:default` declaration draws a `:default`
  conclusion. `docs/inherit.md`.
- **A head-existential rule carrying an aggregate mints a ground witness.**
  `skolem/frontier-vars` subtracts a post-join literal's output, so the Skolem NAT no
  longer takes a variable into its argument list.
- **An open `disjoint` goal is enumerated from the declarations rather than from the
  vocabulary.** A separation convicts two subtrees, so the answers are the subtypes of
  what a *visible* declaration names and the cost is the answer's own size; 0.2.0 asked
  `taxonomy/disjoint?` once per type, and once per **pair** with both arguments open. On
  4,000 types carrying one separation that is 15.4 ms to 0.13 ms with an argument bound —
  flat where it grew linearly — and at 1,000 types the two-variable goal goes from 2.5 s
  to 4 ms. `lein perf`'s `disjoint-enumeration` check is the claim.
- **A definitional clash is arbitrated from a context that can see both halves.** The
  checks are scoped to the context they are asked in, so a pair whose halves sit either
  side of a `genlContext` edge was answerable from exactly one of the two, and only when
  that half was the one the settle moved. `settle/clash-askers` runs the check from the
  candidate's own context and from the maximal common descendant of it and each context
  holding a sentex it could pair with; nothing is widened.
- **A pair per opposing sentex, not per opposing type.** One sentence stated in a general
  context and again in one that sees it is two sentexes, of possibly different strength,
  and a claim that denies it denies both — where the checks named one handle each, so the
  content-first of the two was weighed and the other left believed beside content that
  contradicts it.

## 0.2.0 — 2026-08-03

**Not a drop-in upgrade from 0.1.0.** Several of the changes below refuse input
0.1.0 accepted or change an observable contract — each such entry is marked
**Breaking** — which is why this is 0.2.0 and not 0.1.1. Entries between here and
the 0.1.0 header are in it, newest first.

- **The argument roots are scoped by predicate** (`[:argument-root pred pos
  term]`), so a materialising join reads one literal's postings rather than
  wading through every functor's at a shared slot. An `[:argument-slot pos
  term]` roster, reference-counted off those postings, keeps the
  predicate-agnostic reads answerable as a union over the predicates present.
  The packed long has no room for a fourth key part, so the dense roots route
  the family to their boxed fallback. `index-layout-version` is **2**: an index
  written by 0.1.0 reads as `:layout-changed` and is rebuilt on first open —
  no action needed, but a large durable store pays a reindex for it.
- **Breaking: every handle-taking fn refuses a non-handle** (`:bad-handle`) —
  the vector `assert` returns for a conjunctive rule included, which 0.1.0's
  `retract!` silently answered with `{:removed-sentexes 0}`. `nil` stays a
  question with an answer (`in?` false, `why` `{:stored? false}`,
  `add-provenance` a no-op), and `check-edit` reports what `edit!` throws. `why`
  also takes `{:max-depth n}` (default 256), marks a capped branch
  `{:truncated? true}` instead of overflowing, and refuses bad opts
  (`:unknown-option`).
- **`close!` releases a durable KB's directory** without waiting for JVM exit,
  and `import!` is `export!`'s inverse. An unclean close still releases the
  lock and registry; the first component failure is rethrown after.
- **An `argIsa` / `interArgIsa` / `argGenl` refusal names its convicting
  declaration in content order**, not in whichever order retrieval enumerated.
- **The five sweeps run in CI** — dense TMS, incremental matcher, node query
  engine, its tacticians, reference retrieval — each failing-set-identical
  with the default it replaces. Nothing ran them before.
- **Breaking: `assert` refuses a non-map `opts`** (`:unknown-option`) —
  `(assert kb s ctx :monotonic)` stored a defeasible sentence in 0.1.0.
  `check` already reported the same request; the two agree now.
- **Breaking: `open-kb` recovers by default** (`:recover? :auto`). The old
  `:warn` default handed back a KB that answered wrongly from a reopened
  store. The cost moves to construction — O(records) on a populated store —
  and `{:recover? false}` defers it. `:warn` and `false` remain.
- **The public surface is six namespaces**, where it was one: `vaelii.core`
  plus thin shims `vaelii.client`, `vaelii.starter`, `vaelii.web`,
  `vaelii.serve` and `vaelii.cli` over the `impl` namespaces they front. The
  boundary is now what the docs said it was.
- **Breaking: `vaelii.client`'s `assert` and `assert-rule` are spelled bare**,
  without the `!` 0.1.0 gave them. A `!` marks a fn that destroys stored
  knowledge and neither does — both are additive, and `retract!` is what takes
  one back — so the client now spells them exactly as `vaelii.core` does. A call
  site writing `c/assert!` or `c/assert-rule!` no longer resolves.
- **A clash names the sentex that states the membership**, not one that merely
  entails it, under either retrieval strategy.
- **An auto-compaction queued for a closed store is dropped**, so the next
  open no longer replays it as a crash-interrupted compaction.
- **Breaking: error `:type` keywords are plain across the tree**
  (`:unknown-source`, not `:vaelii.impl.catalog/unknown-source`), and
  `open-kb`'s backend refusals carry one. Swept in the same pass: the settle
  re-check queue no longer drops entries queued by a concurrent thread, and
  `foreign/register` refuses with `ex-info` rather than an elidable `{:pre}`.
- **Leiningen 2.10 is the minimum**: `:preserve-eval-meta` needs it, and 2.9
  ignores the key silently.
- **Breaking: `POST /op` requires `Content-Type: application/edn`.** The type
  is not CORS-simple, so a browser must preflight and the daemon answers no
  CORS headers — which closes cross-site request forgery against a loopback
  daemon. A client that sent no content-type is refused; add the header.
- **Breaking: a request body over 16 MiB is refused** (413) before it reaches
  the heap; `VAELII_MAX_BODY_BYTES` adjusts the cap.
- **Breaking: DNS rebinding is closed on both servers.** Every route requires
  a `Host` naming the interface the server was started on. A request with no
  `Host` still passes (a non-browser client carries no ambient browser
  context); a reverse proxy or local alias sets `VAELII_ALLOWED_HOSTS`.
- **`+with-foreign` names a coordinate that exists**
  (`com.vaelii/vaelii-foreign`); the bare id it carried resolved nothing.

## 0.1.0 — 2026-07-31

The first release. What follows is the development log that produced it, newest
first; every entry below is in 0.1.0.

## 2026-07-30

- A declaration re-checks the exceptions it moves: `(symmetric P)`,
  `(transitive P)`, `(inverse P Q)` and the `argPreserving` forms change what
  may be concluded with no fact arriving; `(functional P)` sweeps the extent
  when it lands.
- An equality restates a fact for each reader rather than once for the KB, and
  is itself a re-check trigger for `exceptWhen`, `unknown` and census reads.
- A change feed: the region a settle already computes is handed to a listener
  instead of discarded.
- English in — a sentence read into candidates a person still has to accept.
- A qualitative relation two contexts entail together fires a forward
  rule; a believed negative reaches the wiring a positive does; "some context"
  means the union of what the readers answer.
- Three readers of one question agree over a cyclic hierarchy, and settle
  repairs the context ranking after reconciling belief as well as before it.

## 2026-07-29

- One front door for backward chaining: the four paths measured, then
  consolidated to two chainers behind one entry point with one dial. A proof
  of an ephemeral answer reads the way `why` does.
- The goal frontier's order is a policy measured on time-to-first-answer,
  `:ground-first` by default; the goal-stack chainer drives one solution at a
  time and level 7 streams its search.
- Foreign formats arrive as a classpath plugin, so a reader ships and retires
  without touching the engine.
- A constraint declaration may name a second sentex it must not weigh, and a
  depth bound has no default because there is no defensible one.

## 2026-07-28

- `lein gate`: lint, the suite, and the scaling claims, measured and failed on
  rather than asserted; five checks added for costs that grow with what they
  must not.
- The columnar index is written once and mapped back; backend names read
  `<records>-<index>`, all seven.
- A literal's matches are remembered and retired on a clock; converging
  branches share one rule expansion; a third backward chainer whose state is
  a frontier.
- The naming invariants belong to the knowledge base, and the bulk door counts
  what it skips.

## 2026-07-27

- Aggregation: a count is a query operator, and a firing that rests on one is
  maintained like any other — gated by a permutation test. A census counts
  distinctness through the representative the asking context elects.
- `argIsa` entails as well as constrains, behind a toggle, retroactively too.
- A definitional clash names a second sentex, making it a nogood, and the
  arbitrating sweep asks the taxonomy rather than a fixed functor set.
- The qualitative network lives on the knowledge base and warm-starts off its
  own previous answer; a violation ledger is a claim about one KB.
- The browser draws term shapes, composes English at three densities, and
  gained `lein browser`; OpenCyc loading went from 378s to 277s.

## 2026-07-26

- Contexts got a vantage: every taxonomy supporter records the context it
  asserts from, so disjointness, matching fan-out and settle all read only
  what the asking context can see.
- A firing names the `genl` edges it subsumed through — belief and strength
  run through them like any antecedent, checked against all 24 orderings.
- Records and index became two independent choices, plus an overlay backend:
  a private writable fork over a shared read-only base.
- A knowledge base is readable before it finishes loading, and the suite runs
  on every backend from one script.

## 2026-07-25

- OpenCyc, read and re-expressed: every constant given back its role, 1.1M
  sentexes in the engine's own format, on the machine that reads it. Nothing
  of Cycorp's is redistributed.
- An export format no rename can break, with `xz`, an importer, and an oracle
  comparing two knowledge bases; a dump lands every record at its handle.
- Qualitative spatial and temporal reasoning: RCC-8 and three more spatial
  algebras, Allen intervals, durations and instants, behind one glue.
- One gap written in two units is one constraint: both spellings snap to the
  tolerance grid, and a unit given two conversion factors is its own base.
- A knowledge-base catalog with a browser that switches between KBs;
  `inherit` declared rather than assumed; definitional checks reach every
  term; `argGenl` constrains one level up.

## 2026-07-24

- The scale program opened with measurement first: the truth-maintenance
  wall, a posting-encoding bake-off on a real corpus, and a rule audit.
- Three dense representations, each measured: `:memory-dense` integer
  postings, the `:memory-columnar` int-token trie with CSR compaction (3.18x
  whole-index), and a bitmapped TMS behind a protocol.
- The disk side got dense too: positional record reads with a hot-record LRU,
  a positional frame codec, tokenized bodies over a durable dictionary — all
  behind a backend parity gate.
- Recursive forward chaining went O(n³) → O(n log n); a term roster
  enumerates vocabulary in O(terms).
- The web browser was hardened — escape by default, guard the parse, bind
  loopback, refuse cross-origin writes — and a pluggable LLM proposes edits
  and never applies them.

## 2026-07-23

- A performance review, its findings fixed: the disk log records operations
  rather than grown values (killing an O(N²) write amplification), settle
  keeps a coincidence set, re-checks narrow to the moved cone, region
  fixpoints became semi-naive worklists, compaction is copy-on-write.
- Symbolic equational reasoning: pure oriented rewriting with full
  Knuth-Bendix orientation, order-independent normalization, and
  non-confluence surfaced; `rewriteOf` extended over predicates and types.
- An operational surface: an EDN-over-HTTP daemon, a command-line driver, a
  thin client, and a browser that attaches to a daemon — with the public API
  closing every hole the browser tracked.
- Existential rule heads with deterministic skolemization; an occurs check;
  closures answered on demand; the record split into atomic and rule shapes
  with interned symbols; a bulk-load fast path.

## 2026-07-22

- Negation as failure, at top level and in antecedents, with block, sweep and
  revive, and stratification to keep it sound.
- Resource-bounded anytime inference with qualitative cost tiers and a
  cost-ordered forward-chain join; `ask-within` normalizes its goal.
- Reification of non-atomic terms; structural subterm indexing,
  oracle-proven, then on by default.
- The storage seam: index logic onto one key-value protocol, an in-memory
  backend, then the on-disk substrate — files, lock, durability, record
  store, index store.
- The index benchmark harness, and a per-handle provenance side map.

## 2026-07-21

- `exceptWhen` canonicalized into the record, blocking excepted conclusions
  with only reachable firings re-checked; its query reified the way a fact
  is.
- Equality landed: the closure, the `different` prover, a specification
  suite, and wiring into assert; stratification is checked on edge change.
- The engine split out of one namespace into five, and the knowledge base
  restructured into a layered tree loaded on start.
- `assumptionRules` with persistent solve and labeling contexts, proven on a
  sudoku.
- Retrieval got sharper: argument roots, multi-column narrowing, predicate
  subsumption, set-algebra retrieval, an opt-in incremental matcher.
- Truth-maintenance mutations are atomic; lint arrived.

## 2026-07-20

- Canonical rule form — canonical variables with a varmap, literal order,
  comparison direction — so rules alike up to renaming share one handle.
- The eight-level lookup-to-query stack, lazy throughout, with a browser page
  showing which level answered.
- Order independence and locality pinned as invariants: region-local
  relabelling, belief-following closures, content-keyed tie-breaks.
- The answer-set layer wired to the edge-solver seam, with a labeling
  materialized as a context; the defeasible layer made sound, six bugs
  pinned as failing tests first; `exceptWhen` began as a failing suite.
- Everything but `core` moved under `vaelii.impl.*`; `!` reserved for
  irreversible operations; tests became net-neutral, and a second concurrent
  run fails fast rather than corrupting the first.

## 2026-07-19

The first day: a contextualized common-sense knowledge base with a trie
index, inference and truth maintenance.

- Sentexes — a sentence plus the context it holds in — stored as records
  behind protocols with nippy serialization; rules are sentexes too, with
  built-in transitivity for types and contexts.
- Forward chaining with dependency-directed retraction, and a backward
  chainer; a non-monotonic TMS with strengths, soft prioritized
  contradictions, and a solver seam.
- An inverted term index, directed rules, disjointness, well-formedness
  checks, and a pluggable prover query engine; structural connectives
  canonicalize into the record; evaluable arithmetic.
- A web browser over the whole thing, over a starter ontology with every
  term documented.

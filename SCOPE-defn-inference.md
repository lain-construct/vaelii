# Scope packet — defn inference (defnNecessary / defnSufficient / defnIff)

**Owner:** Lain · **Authority:** Pace (vaelii-thread, 2026-08-29) · **Target:** upstream vaelii PR → `vaelii/vaelii` develop · **Branch:** TBD (`lain/defn-inference`)

## Why this is its own PR (Lain's call — Pace: "Your call whether we make this a separate PR or chonk it in with predAll")
**Separate PR, gating predAll.** Syne independently recommended the same split (vaelii-thread 2026-08-29). Rationale:
- **predAll depends on defn inference** (Pace: "Either way, predAll depends on defn inference"). The `-212` demonstration in predAll only works once `(negative_integer -212)` is dynamically provable, which is *this* PR's evaluative-defnSufficient build.
- defn inference has its **own substantial semantics** (precedence, admittance algorithm, current-behavior pinning) — enough surface to be atomic and bisectable on its own.
- A green defn-inference PR is a clean foundation the predAll matrix lands on top of.

## The core build (from the S189 design session, corrected)
**Make `defnSufficient` prove `(Coll x)` on query by *evaluating* the sufficient condition** — computable predicates (`integer`, `lessThan`) evaluated at ask-time — not only firing a FORWARD rule when the condition is already believed.
- **Current state (verified S189):** `defnSufficient` materializes a forward rule `(implies C (Coll ?x))` (sentex.clj:1815) that fires only when condition `C` is *believed*. `(integer -212)` is never a believed fact, so `(negative_integer -212)` is never derived. `defnIff` **expands** to necessary+sufficient (sentex.clj:1816/1828); there is **NO `(genl defnIff defnSufficient)` edge** — expansion, not genl.
- **After:** `(negative_integer -212)` dynamically provable on query by evaluating `(and (integer -212) (lessThan -212 0))`. No stored fact, no enumeration.
- **NOT a populator.** Do not materialize `(negative_integer -212)` as a stored sentex — the `defnGenerator` on infinite numeric types is the prover-stressing, theoretically-hard thing (Cyc never cracked it); **punted far ahead.**

## Test list — Pace's spec, verbatim (vaelii-thread 2026-08-29, msg 1543296853238353971)
> Let's take a TDD approach as usual and create a bunch of tests for defns.
> - when defnNecessary and defnSufficient fight, who wins?
> - all defnNecessaries of all genls are checked and all must pass. (I guess i just answered who wins)
> - the defn admittance algorithm has a fast fail that checks a defnNecessary on a genl before descending to try all the defnSufficients of all its specs
> - what currently happens when you ask (?pred 212) ? Whatever the current behavior is, pin it with a test. the test should include a comment about defns.
> - quoted defn analogues for every defn test. parametrize and DRY. The quoted stuff might depend on syne's quoting WIP. I'll check in with syne on that.

### Reading these as tests (Lain's read — flagged, to become failing tests first)
1. **Precedence — defnNecessary wins.** Pace answered her own question: admission requires **all defnNecessaries of all genls to pass**. A `defnSufficient` cannot admit a member that fails any `defnNecessary` up the genl chain.
2. **All genls' defnNecessaries checked.** Not just the immediate collection's — the full genl ancestry's necessaries must all hold.
3. **Admittance fast-fail.** The algorithm checks a genl's `defnNecessary` **before** descending to try all `defnSufficient`s of all its specs — cheap disqualifier first.
4. **Pin `(?pred 212)` current behavior.** Whatever it does today, capture it in a test **with a comment about defns**, so the change is visible against a recorded baseline. (Cousin of [[practice-settled-markers-carry-receipts]] — pin the receipt.)
5. **Evaluative defnSufficient (the core build):** `(negative_integer -212)` provable on query via computable-condition evaluation; no hand-assert of membership.

### Added 2026-08-29 10:09 — genl-diamond admittance test (Pace, msg 1543306713397067887, edited 10:10)
> add a defn test that has a genl diamond. test defn admittance on the bottom. defnNecessary on all four, defnSufficient on the bottom. ensure each defn is called exactly once in the admitted case. ensure the side defns are not called when the topmost defnNecessary fails.

**Reading (Lain):** four collections in a diamond — `Bottom` genl two middles `MidA`/`MidB`, both genl `Top`. `defnNecessary` on **all four**; `defnSufficient` only on `Bottom`. Two cases, both asserted by counting calls (spy/counter on each defn's check):
- **Admitted case — each defn evaluated exactly once.** Candidate satisfies everything. `Top` is reachable via two genl paths (`Bottom→MidA→Top`, `Bottom→MidB→Top`); a naive walk checks `Top`'s defnNecessary twice. Assert **exactly one** call per defn — the algorithm dedups the lattice (visited-set / memoized), not re-walks it. All four counters = 1.
- **Rejected-at-top case — short-circuit, side defns not called.** `Top`'s defnNecessary fails. Assert `Top` is checked **exactly once** and **`MidA`/`MidB` are NOT called** (nor `Bottom`'s sufficient). This is the fast-fail made concrete: the highest/cheapest disqualifier is checked first and the walk stops — it does not spread to the siblings, and it does not re-check `Top` on the way out. Counters: **`Top` == 1** (Pace, 2026-08-29 — not ≥1; no redundant re-check even on the failure path), `MidA` == `MidB` == 0.
- Together: correctness (all necessaries pass to admit) **and** efficiency over a DAG — dedup on success, short-circuit on failure. Ordering must guarantee `Top` is reachable-and-checked before the middles so the short-circuit holds.

### Semantics v2 (Pace, 2026-08-29) — sufficient authoritative, necessary is an optimization; defns are TWO-VALUED
- **Two-valued.** A defn condition passes or it doesn't — no third "unknown" state, no false-vs-unknown distinction.
- **Positive `(coll x)`** is proved by a **defnSufficient** that passes (coll's own, or a spec's — descend to specs). Necessary is NOT a positive gate.
- **defnNecessary = optimization / negative witness.** A **failing** necessary means ¬member (member⇒necessary, contrapositive), so it fast-fails positive admittance and *proves the negative*.
- **Both fire** (a sufficient passes AND a necessary fails) ⇒ the KB is inconsistent; `(coll x)` and `(not (coll x))` are both provable ⇒ the existing **clash machinery** surfaces the contradiction. The defn algorithm does NOT arbitrate it (fork resolved: not (a)/(b)/(c) — it's a contradiction, by two-valuedness). **An inconsistent KB may yield inconsistent answers, and that is fine (Pace): the test DOCUMENTS the inconsistency and pins NO particular happenstance behavior.**

### Negated defn checks — the exact converse (Pace, 2026-08-29)
`(not (coll x))` is provable iff a **defnNecessary fails** — coll's own or a **genl's** (ascend the genl chain; a failed necessary anywhere above proves ¬member). The negative algorithm is the positive one with three flips:
- flip truth (member ↔ non-member) · flip **necessary ↔ sufficient** · flip **genl-walk direction** (positive descends to specs' sufficients; negative ascends to genls' necessaries).
- Examples, all provable by failing `positive_integer`'s (or a genl's) necessary: `(not (positive_integer 0))`, `(not (positive_integer "string"))`, `(not (positive_integer unaryPredicate))`.
- **Every positive defn test gets a negated analog.** Parametrize/DRY the positive and negative suites over one spec.

## Postponed (Pace + Syne, vaelii-thread 2026-08-29 — Pace: "I'm fine with postponing quoted defns")
**Quoted defn analogues are OUT of this PR.** Syne's audit: vaelii has **no `quotedDefnNecessary/Sufficient/Iff` forms**, `quotedArg` doesn't meaningfully type compound payloads, and **schematic `equals` still rewrites through quotation** (the opacity boundary is missing). Mirroring a quoted suite now would "certify fiction."
- Do **not** add a mirrored quoted suite. Do **not** take a dependency on Syne's quoting WIP in this PR.
- Add quoted-defn tests only as `pending`/spec markers if useful, not as passing coverage.
- Syncategorematic operators (`not`/`all`/`implies`) are the **sharpest first cases** for the eventual quoted-defn suite — no independent referent to hide a category error (Syne, same thread). Recorded for when that PR happens.

### TODO (future, NOT this PR) — defn-inconsistency integrity check
A KB integrity check that scans for defn inconsistencies: collections where some term satisfies a `defnSufficient` yet fails a `defnNecessary` (both `(coll x)` and `(not (coll x))` provable). Sibling of predAll's `predAllSpecified` violation-reporting. Leave as a code comment / todo where the defn machinery lives; do not build here. (Pace, 2026-08-29.)

## Ceiling / non-goals
- Unquoted defn inference only. No quoted-defn surface, no quoting-WIP dependency.
- Do not build the literal→membership `defnGenerator`/populator (punted, theoretically-hard).
- TDD-first: write the five tests above (as failing tests) before touching inference code.
- Flag CONFLICT and stop if the admittance/evaluation machinery can't express a case.
- `lein test :only vaelii.defns-test` green before review; full suite green before PR.

## Process
worktree → TDD → `bsky:multimodel-elbow-grease` review → fix to convergence → upstream PR to `vaelii/vaelii` develop (reauthor as paceheart only if the authorship gate requires it) → **then** predAll rebases on top.

## Relation to predAll
predAll's `-212` demonstration (`SCOPE-predall.md`, Instance class) is blocked on this PR's evaluative defnSufficient. predAll Instance cells stay **forward, no rebuild**; they simply start firing on bare literals once this lands.

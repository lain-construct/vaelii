# What belief is: the reference semantics

- **Covers:** belief defined as a function of the stored premises and a context, with no
  region, memo, budget or pass; the invariants that definition holds every world to; the
  decisions on the questions the other pages left open; the fragment of the engine the
  definition covers; and the standing state a settle keeps between settles, with what
  invalidates each part of it.
- **Not here:** how a settle computes belief, and what each step costs →
  [nmtms.md](nmtms.md); why a decision is shaped the way it is →
  [defenses.md](defenses.md); what a context sees → [contexts.md](contexts.md).
- **Assumes:** sentex, context, premise, justification, defeat-class, nogood, vantage →
  [glossary.md](glossary.md).

A settle maintains belief incrementally, through the justification network and about thirty
standing caches, each with an invalidation rule of its own. This page states the function
those caches approximate. `vaelii.ref.believe` and `vaelii.ref.nogoods` implement it, by
brute force, in the test tree.

## The function

`believed?(W, S, C)` holds when sentence `S` is believed at context `C`, given a world `W`.
The engine is held to this predicate. The predicate is computed when asked, and it is
local: it reads the supports of `S` and the nogoods `S` could be a member of, and every
family keys those nogoods by the arguments of `S`. Negation keys on the body of `S`,
`disjoint` and `covering` on the individual of a membership, `functional` and
`functionalInArg` on the predicate and the positions the mark does not determine,
`irreflexive` and `anti_symmetric` on the argument pair of the tuple, `anti_transitive` on
each argument `S` shares with another step, and the inherited family on the predicate and
the arguments outside the preserved position. The set `believed(W, C)` of every `S` with
`believed?(W, S, C)` is the enumeration a spec over a small world uses.

**A world is a set of premises.** Each premise is a sentence, a context and a strength:
a ground fact, a denial `(not S)`, a `genl` or `genlCx` edge, a declaration, or a rule.
A world holds the writes offered to a KB, whether or not the engine stored them
(invariant 3), and never what the KB derived. Two premises of one sentence in one context
are one premise at the stronger of the two strengths
([nmtms.md](nmtms.md#strengths-and-the-defeat-class-vaeliiimplstrength)). The order the
premises arrived in is not part of the world.

`believed(W, C)` is the least fixpoint of the following definitions, taken together.

```
up(C)              = C and every context C reaches over the stored genlCx edges
visible(C)         = the premises of W whose context is in up(C)
derived(C, O)      = the closure of visible(C) − O under the rules in visible(C)
                     and under argument preservation
believed(W, C)     = derived(C, O*), where O* is the least O closed under the decisions below
believed?(W, S, C) = S is in believed(W, C)
```

1. **Visibility.** `up(C)` is reflexive and transitive. A context no `genlCx` edge names
   sees only itself, with no implicit root
   ([contexts.md](contexts.md#a-context-outside-the-spindle)). Every `genlCx` edge is
   `:monotonic` and none is denied (invariant 1), so `up(C)` reads the stored edges alone,
   whatever context stores them, and does not depend on belief.
2. **Taxonomy.** At `C`, `A` is a subtype of `B` when a chain of `genl` edges, each
   believed at `C`, leads from `A` to `B`; every type is a subtype of itself and of
   `thing`. The closure reads only edges `C` believes
   ([taxonomy.md](taxonomy.md#reads-are-scoped-by-the-asking-context)). A `covering`,
   `separating` or `partition` declaration states a `genl` edge from each part to the
   whole ([taxonomy.md](taxonomy.md#covering-a-whole-and-the-parts-named-against-it)).
3. **Derivation.** A rule visible at `C` fires on sentences believed at `C`. An antecedent
   `(T ?x)` matches `(S x)` when `S` is a subtype of `T` at `C`. An antecedent also
   matches a claim reached by argument preservation
   ([inherit.md](inherit.md#forward-chaining-on-a-claim-nobody-stored)). The rules are
   evaluated stratum by stratum over the rule dependency graph, which the engine keeps
   acyclic through negation by refusing a rule set that is not
   ([exceptions.md](exceptions.md#stratification)). An `(unknown S)` antecedent blocks a
   binding under which `S` holds, and an `(exceptWhen E R)` blocks every binding of `R`
   under which all of `E` holds. Both are judged over the lower strata's result, without
   backward chaining, and a question with no answer does not block
   ([exceptions.md](exceptions.md#semantics), [naf.md](naf.md#in-a-rule-antecedent)).
   The question is asked at `C`, so a fact only `C` sees blocks the conclusion at `C`
   (decision 4).
4. **Inherited claims.** An inherited claim `(P … sub …)` is believed at `C` when a
   believed `(transitiveInArg P k genl)`, a believed general claim `(P … sup …)` and every
   `genl` edge on some route from `sub` to `sup` are believed at `C`, and no believed
   denial of the claim undercuts that reading (decision 5). A denial undercuts a reading
   of class `:default`; against a `:monotonic` reading it forms the inherited nogood of
   item 6 instead ([inherit.md](inherit.md)). Nothing stores an inherited claim.
5. **Classes.** A premise holds at its strength. A firing confers the weakest of its
   rule's defeasibility (`:monotonic` for a bare rule, `:default` for a
   `set/defaultRule`), its antecedents' classes, and the `genl` edges it rests on; a
   `genlCx` edge is `:monotonic` (invariant 1) and caps nothing. A firing whose rule has
   an `unknown` antecedent or an `exceptWhen` confers `:default` (invariant 9). The
   rule's own write strength is not in that minimum
   ([nmtms.md](nmtms.md#strength-propagates-from-the-antecedents)). The `genl` edges are
   read over the path whose weakest edge is strongest
   ([defenses.md](defenses.md#the-subsumption-path-is-the-widest-bottleneck-not-the-shortest-route)),
   and an inherited claim takes the same widest bottleneck: the maximum over its routes
   of the minimum class along each (decision 9). A sentence's class at `C` is the
   strongest class over its supports at `C`.
6. **Nogoods.** A nogood at `C` is a set of members, all believed at `C`, that cannot all
   hold, plus the declarations and edges the conviction reads (its grounds), all believed
   at `C`. Each family is one sentence:
   - **negation**: `S` and `(not S)`, members both
     ([nmtms.md](nmtms.md#soft-prioritized-contradictions-the-settle-layer));
   - **`disjoint`**: `(T1 x)` and `(T2 x)` where `T1` and `T2` are subtypes at `C` of two
     types a believed `(disjoint A B)` separates; grounds the declaration and the `genl`
     edges ([taxonomy.md](taxonomy.md#disjointness));
   - **`functional`** and **`functionalInArg`**: two tuples of one predicate that agree
     on every position but the determined one and differ there, symbols or not, under a
     believed mark on that predicate or one above it; grounds the mark (decision 6)
     ([taxonomy.md](taxonomy.md#predicate-metadata));
   - **`irreflexive`** and **`anti_symmetric`**: a self tuple `(Q a a)`, one member, or a
     converse pair `(Q1 a b)` and `(Q2 b a)` with `a` distinct from `b`, two members,
     under a believed mark on that predicate or one above it; grounds the mark
     (decision 7);
   - **`anti_transitive`**: `(P a b)`, `(P b c)` and `(P a c)`, three members
     ([nmtms.md](nmtms.md#a-nogood-is-a-set-anti_transitive-has-three-members));
   - **`covering`**: `(W x)` and a believed `(not (A x))` for every part `A` of a
     believed `(covering W A …)`; grounds the declaration and the `genl` route
     ([taxonomy.md](taxonomy.md#covering-a-whole-and-the-parts-named-against-it));
   - **inherited**: a stored `(not (P … A …))` beside a claim `(P … W …)` that a believed
     `(transitiveInArg P n genl)` carries down a `genl` path from `W` to `A`, when every
     part of that reading is `:monotonic`; the members are the denial, the general claim,
     the declaration and each edge of the path, and a reading with a `:default` part is
     undercut and forms no nogood
     ([inherit.md](inherit.md#a-contrary-claim-against-a-known-true-one-is-a-contradiction-and-is-reported)).

   The grounds of a definitional family are read through and never weighed. The inherited
   family is the one whose reasons are members
   ([nmtms.md](nmtms.md#what-qualifies-as-a-nogood)).
7. **Decision.** Read each member's class at `C`. A unique weakest member at `:default`
   goes OUT at `C`. Two or more members tied at the weakest class, and that class
   `:default`, are a dilemma, and every member stays believed. Every member `:monotonic`
   is a hard clash, and every member stays believed
   ([nmtms.md](nmtms.md#soft-prioritized-contradictions-the-settle-layer)); the clash is
   stored and reported, never refused (invariant 3). An all-`:monotonic` `functional`,
   `functionalInArg` or `anti_symmetric` nogood over two symbols is a merge, and every
   member stays believed (invariant 4). Defeat-class is the only axis
   ([nmtms.md](nmtms.md#there-is-no-second-axis)).
8. **The OUT set.** `O` starts empty. Each round recomputes `derived(C, O)`, finds the
   nogoods over it, decides each, and adds the losers to `O`. A round that defeats a
   ground applies those defeats first and alone. The rounds stop at the first round that
   adds nothing, and no round removes from `O` (decision 2).

**Per-context computation turns four properties into consequences of the definition.**
Context scoping holds because nothing outside `up(C)` is an input to `believed(W, C)`.
Belief filtering holds because every read inside the definition (a match, a subtype test,
a class, a nogood member) reads `derived(C, O)`, and nothing reads a stored-but-OUT
sentence. Order independence holds because `W` is a set and the definition has no step
that picks one of several equals: a tie is a dilemma, and nothing is chosen. Locality
holds as a bound on dependence: a premise in context `X` can move belief only at the
contexts whose `up` holds `X`. The engine maintains each of these properties by
mechanism, and the reference holds them by construction, so a disagreement between the
two is a defect in the engine.

### Decisions

Each entry states the question in one sentence, the decision, the engine change it
implies, and the section of another page it changes. The `TODO(spec)` markers the
builders of `vaelii.ref.*` wrote are now citations of these decisions by number.

1. **Whose belief of a `genlCx` edge decides `up(C)`?** Nobody's: every `genlCx` edge is
   universal, `:monotonic` and undeniable (invariant 1), so `up(C)` reads the stored
   edges. The engine change is invariant 1's. Section to change:
   [contexts.md](contexts.md#genlcx-the-context-hierarchy).
2. **Does a defeat decided in round 1 stand when its ground goes OUT in a later round?**
   Yes. The OUT set grows round by round, a defeat that withdraws a ground is applied
   first and alone, and the rounds are the semantics while the pass count is not. Before
   decision 14, a round that re-decided every nogood from scratch had no fixpoint on this
   world, all in one context, which `resolve-at`'s docstring in `vaelii.ref.believe`
   cites:

   ```
   :default    (genl chi dog)  (chi Kit)
   :monotonic  (disjoint dog cat)  (cat Kit)  (pp Kit)
               (transitiveInArg pP 1 genl)  (pP dog Bone)
               (set/forwardRule (implies (and (pp ?x) (unknown (chi ?x))) (not (pP chi Bone))))
   ```

   Round 1 takes `(chi Kit)` OUT and the rule fires. With the conclusion `:monotonic`,
   round 2 took the edge OUT, and a from-scratch round alternated between those two
   states. Under decision 14 the conclusion is `:default`, round 2 reads a dilemma
   between the conclusion and the `:default` edge, and both readings stop with
   `(chi Kit)` OUT. No v1 world is known on which the two readings differ under decision
   14, and the rounds stay the semantics. The engine change is that a settle's answer
   does not depend on its pass count (prompt 30). Section to change:
   [nmtms.md](nmtms.md#the-resolution-rounds), which states the case of one round only.
3. **Does a verdict bind a context below its vantage that reads the clash released?**
   No. Each context decides from its own view: a context that sees what the vantage sees
   reaches the vantage's verdict, and a context that sees a denial or an edge dissolving
   the clash believes what the vantage took OUT. The engine change reverses the behaviour
   settle prompt 23 landed, so a defeat does not reach a reader whose view releases the
   clash (a new prompt). Section to change:
   [defenses.md](defenses.md#a-verdict-is-not-withdrawn-below-its-vantage), which the
   decision reverses, and the departure in
   [defenses.md](defenses.md#where-the-four-properties-stop).
4. **Is an `exceptWhen` or `unknown` question asked from `C` or from the conclusion's
   placement context?** From both. The question is asked at the placement context when
   the justification is made, and again at every reader below it; a reader at which the
   exception holds reads the conclusion as withdrawn, which equals asking at `C`. The
   engine change is a withdrawal that re-asks each exception at each reader below the
   placement (a new prompt). Section to change:
   [naf.md](naf.md#evaluated-in-the-placement-context-not-the-join), which states the
   placement half only, and [exceptions.md](exceptions.md#semantics).
5. **Is a claim reached by argument preservation a member of `believed(W, C)`?** Yes, as
   item 4 of the definition derives it, at the class decision 9 gives. The engine
   answers such a claim through `core/ask?`, and no engine change is owed. Section:
   [inherit.md](inherit.md#forward-chaining-on-a-claim-nobody-stored) states the engine
   side and needs no change.
6. **Is a `functional` clash between two symbol fillers a nogood?** Yes, unless every
   member is `:monotonic`, which is a merge (invariant 4). The engine change is
   invariant 4's. Section to change: [taxonomy.md](taxonomy.md#predicate-metadata), which
   merges without the `:monotonic` condition and states the non-symbol case two ways.
7. **What does the reference do with `irreflexive` and `anti_symmetric`?** Both marks
   are forced monotonic, and a violation of either is a nogood decided like any other
   (invariant 2). The engine change is invariant 2's. Section to change:
   [taxonomy.md](taxonomy.md#what-each-constraint-does-in-each-arrival-order).
8. **Is `W` the writes offered or the writes stored?** Offered: no clash is refused
   (invariant 3). The engine change is invariant 3's. Section to change:
   [nmtms.md](nmtms.md#1-order-independence), which claims order independence over what
   was stored.
9. **Which path caps a derivation's class?** The widest bottleneck: the maximum over
   routes of the minimum class along each route, for a derivation and for an inherited
   claim. The `genlCx` half of the question has no case left under invariant 1, so no
   engine change is owed beyond invariant 1's. Section to change:
   [nmtms.md](nmtms.md#strength-propagates-from-the-antecedents).
10. **Can a `genl` edge between two predicates be `:default`, denied or derived?** No. A
    `(genl P Q)` whose two arguments are predicates of arity 2 or more, which their
    camelCase spelling decides ([naming.md](naming.md)), is forced monotonic
    (invariant 5). A `genl` between types stays defeasible, so a type edge admits
    exceptions. A mark's reach through predicate `genl` reads the stored edges and no
    belief. The engine change is invariant 5's. Section to change:
    [taxonomy.md](taxonomy.md#predicate-metadata).
11. **Can a definitional declaration be `:default`, denied or derived?** No. `disjoint`,
    `covering`, `partition`, `sibling_disjoint` and `arity` are forced monotonic
    (invariant 6), so a ground goes OUT only by retraction and no verdict is re-asked
    because its ground moved. An `arity` violation is a one-member nogood, the tuple,
    with the declaration as its ground, decided as an `irreflexive` violation is. A
    defeasible disjointness is written as a `:default` rule concluding a denial, which
    forms a negation nogood. The engine change is invariant 6's. Sections to change:
    [taxonomy.md](taxonomy.md#disjointness), [taxonomy.md](taxonomy.md#arity) and
    [taxonomy.md](taxonomy.md#what-each-constraint-does-in-each-arrival-order).
12. **Can an `except` be derived or defeated?** No. An `except` is asserted and
    retracted, never derived by a rule and never defeated (invariant 7). An `except`
    that targets an `except` still hides it. The reference leaves `except` outside v1.
    The engine change is invariant 7's. Section to change:
    [contexts.md](contexts.md#except-removing-visibility-down-a-context-subtree).
13. **Can a merge be defeated?** No. `rewriteOf`, `sameAs` and `equals` are monotonic
    (invariant 8): a merge rests only on `:monotonic` evidence (decision 6), is never
    defeated, and is undone only by retracting a premise it rests on. A defeasible
    identity is written with a predicate that does not merge. The reference leaves
    equality outside v1. The engine change is invariant 8's. Section to change:
    [equality.md](equality.md#what-a-merge-does).
14. **What class does a firing through `unknown` or `exceptWhen` confer?** `:default`,
    whatever the classes of the rule and of the other antecedents, because the
    conclusion goes OUT when a blocker arrives (invariant 9). A sentence first believed
    after a defeat through such a rule is therefore `:default` and cannot defeat a
    `:monotonic` member, which bounds the rounds; decision 2's world is the case. The
    engine change is invariant 9's. Sections to change:
    [nmtms.md](nmtms.md#strength-propagates-from-the-antecedents) and
    [naf.md](naf.md#in-a-rule-antecedent).
15. **Does a caller choose whether a clash is refused?** No. The `:constraints` option
    (`:refuse` and `:arbitrate`) is removed, with the walk that reads the class of a
    clash's grounds at the entry point. The engine stores a clash, decides it and reports
    it (invariant 3). A caller that passed `{:constraints :refuse}` reads `conflicts`
    instead, which is a Breaking change. `vaelii.reference-test` opens its KBs under
    `:arbitrate` until the option is gone. The engine change removes
    `checks/grounds-class`, `functional-mark-class`, `cover-grounds-class`,
    `against-known-true?`, `opposing-class`, `tax/disjointness-class`, `arbitrating?`,
    `*arbitrate-constraints?*`, the configuration key, the image policy stamp and
    `constraint_policy_test` (a new prompt). Section to change:
    [nmtms.md](nmtms.md#which-entry-point-the-content-came-through).
16. **Is a nogood decided when a settle runs, or when a reader asks?** When a reader
    asks. The negation, definitional and inherited families are found from the asked
    sentence's arguments and decided at the reader, memoized per reader under the
    withdrawal cache's watch (`resolution/withdrawal`, `stale-keys`). Forward firings,
    the `genl` and `genlCx` closures, merges and mints stay at write time. An `unknown`
    or `exceptWhen` keeps its block at the placement context, with a per-reader
    withdrawal below it (prompt 46), and the refusal record and its cap stay. The
    reference already computes belief this way, and the cost model under
    [What the engine has to equal](#what-the-engine-has-to-equal) is the engine's
    obligation. The engine change keeps support labels (`:in`) alone in the
    justification network: `:defeated`, `defeat`, `clear-defeats!` and the second
    `groundable` fixpoint go, `contradictions` and `conflicts` become scans over a
    write-time candidate index, and recover rebuilds support once and runs no nogood
    pass. The touched window, `preview`, the change feed and the withdrawal-cache
    reconcile need per-reader diffs first, in a prompt of their own with a perf check.
    Sections to change: [nmtms.md](nmtms.md#the-runtime-view) and
    [nmtms.md](nmtms.md#a-defeat-is-scoped-to-its-vantage).
17. **Can a rule conclude a forced-monotonic predicate?** No. A rule whose consequent is
    on the roster (`genlCx`, a relation mark, a declaration, an `except`, a predicate
    `genl`, an equality) is refused when the rule is asserted, on the rule alone,
    because a derived sentence goes OUT with its antecedents and cannot be `:monotonic`.
    Prompt 41's choice between coercing at placement and refusing resolves to refusing.
    `vaelii.ref.world/parse-rule` refuses such a rule with `:reason :forced-conclusion`.
    The engine change is a check at rule assert (prompt 41). Section to change:
    [taxonomy.md](taxonomy.md#what-a-rule-may-conclude-and-what-it-reaches).

The docs answer three questions a builder may still ask. A context with no `genlCx`
edge sees only itself. A definitional family's declaration is a ground and not a member,
and under invariant 6 it is `:monotonic` and goes OUT only by retraction. A rule's write
strength does not cap its conclusions; its defeasibility and its guards do.

## Invariants the reference states

The world check refuses a world that breaks invariant 1, 2, 5 or 6, or holds a rule
decision 17 refuses, with `:unsupported`, and the generator never produces one. The
engine does not yet hold all nine; each entry names the engine change and the prompt that
owes it.

1. **`genlCx` is universal, monotonic and undeniable.** A `genlCx` edge holds at every
   context whatever context stores it, every write of one is stored `:monotonic`
   whatever strength it was written at, and no world holds `(not (genlCx …))`, so
   `up(C)` is a function of the stored edges. Engine change: the entry point stores a
   `genlCx` write `:monotonic`, as it stores a `forced_decontextualized_predicate` in
   CxUniverse, and refuses a denial of one (a new prompt).
2. **The relation marks are forced monotonic.** The roster is `irreflexive`,
   `anti_symmetric`, `asymmetric`, `functional`, `functionalInArg`, `anti_transitive`,
   `transitiveInArg` and `genlCx`, and invariants 5 to 8 extend it. Every write of a
   roster predicate is stored `:monotonic` whatever strength it was written at (coerced,
   never refused, as `forced_decontextualized_predicate` coerces a context), every read
   treats it as `:monotonic`, and no denial of one is in a world. A mark's reach, the
   sub-predicates it convicts through predicate `genl`, reads the edges believed at `C`
   and never their class. Under invariant 5 those edges are `:monotonic` and never OUT,
   so the reach is the stored edges visible at `C`. Engine change: the entry point
   stores every roster write `:monotonic` and refuses a denial of one, and the
   constraint check decides a violation as a nogood without capping it by an edge's
   class (a new prompt).
3. **No clash is refused.** `W` is the writes offered, and the reference judges every
   one of them. A hard clash is stored and reported, as a `:monotonic` `S` beside
   `(not S)` already is. A refusal remains only where it reads the sentence alone:
   naming, arity, groundness and the v1 fragment. A refusal that reads other stored
   content, such as `(disjoint a b)` over two `genl`-related types, becomes a stored hard
   clash. Engine change: under `:arbitrate` the entry point stores the write that
   completes a clash, and the settle reports the hard clash (a new prompt).
4. **A merge needs monotonic evidence on every side.** A `functional` or
   `functionalInArg` collision between two symbol fillers, or an `anti_symmetric`
   converse pair of symbols, merges the two terms only when every member is
   `:monotonic`. Otherwise the collision is a nogood: the unique weakest member loses,
   and a tie at `:default` is a dilemma. v1 has no equality, so the generator never
   produces two colliding `:monotonic` symbol tuples under one mark. Engine change: the
   engine derives the equality only from an all-`:monotonic` collision and decides every
   other one as a nogood (a new prompt).
5. **A `genl` edge between predicates is forced monotonic.** A `(genl P Q)` whose two
   arguments are camelCase predicates is stored `:monotonic` whatever strength it was
   written at, no world holds its denial, and no rule concludes it (decision 17). A
   `genl` between types stays defeasible. `vaelii.ref.world/predicate-genl?` reads the
   spelling. Engine change: the entry point coerces such an edge and refuses its denial,
   and the belief half of `marks-above?` and `clash-marked-below`, the un-merge by edge
   defeat in `equate-under-edge` and the predicate arm of `preserving-moves` go (a new
   prompt).
6. **Every definitional declaration is forced monotonic.** `disjoint`, `covering`,
   `partition`, `sibling_disjoint` and `arity` are stored `:monotonic`, never denied and
   never derived, so a ground goes OUT only by retraction. An `arity` violation is a
   one-member nogood with the declaration as its ground. v1 admits `disjoint` and
   `covering`; `partition`, `sibling_disjoint` and `arity` stay outside it. Engine
   change: the entry point coerces a declaration and refuses its denial;
   `report-arity-reach!`, the chain from `arity-bound-by` to `stored-specs` and the
   subtree sweep per `genl` edge go; and prompt 42's related-type declarations become
   one-member or two-member hard clashes (a new prompt).
7. **`except` is forced monotonic and premise-only.** An `except` is asserted and
   retracted, never derived and never defeated, and an `except` that targets an `except`
   still hides it. `except` is outside v1. Engine change: `resolution-watch`,
   `resolution-flips`, `watched-count` and `watched-believed`, the resolution call of
   `recheck-flipped-excepts` and the `except` half of `revival-flips` go (a new prompt).
8. **Equality is monotonic.** A `rewriteOf`, `sameAs` or `equals` merge rests only on
   `:monotonic` evidence, is never defeated, and is undone only by retracting a premise
   it rests on. Equality is outside v1. Engine change: `refresh-supersessions` moves
   from `settle-finish` to the write path, and the `:supersessions` stamp, the relabel
   case of `region-suffices?`, the supersession half of `clash-dirty` and the relabel
   half of `:respell` go (a new prompt).
9. **A guarded firing confers `:default`.** A firing whose rule has an `unknown`
   antecedent or an `exceptWhen` confers `:default` on its conclusion, whatever the
   classes of the rule and of the other antecedents. Engine change:
   `jtms/conferred-class`, which caps a firing on its antecedents' classes alone, caps
   a guarded firing at `:default` (a new prompt). Until then the harness counts the
   divergence as `:naf-conclusion-monotonic`.

## What the engine has to equal

A settle is an incremental computation of `believed(W, C)` for every context at once.
It reads a region, memos, budgets and passes, and none of them may change the answer: a
settle that differs from the function on any world and any context is wrong, whatever its
tests say, unless the difference is a known divergence below. `vaelii.reference-test`
is the witness. It loads random small worlds in every arrival order into fresh KBs under
`{:constraints :arbitrate}` and compares the engine's belief at each context with the
reference's, sentence by sentence: a stored sentence through `core/believed?` on its
handle, and an inherited claim, which has no handle, through `core/ask?` at the context.
A context whose view holds a merge verdict is not compared, and the harness counts it.

**Under decision 16 the engine decides at the reader.** The negation, definitional and
inherited families are found from the arguments of the asked sentence `S`, by the keys
[The function](#the-function) lists, and decided at the reader `C`; forward firings, the
`genl` and `genlCx` closures, merges and mints stay at write time. The costs the engine
is held to:

- a write costs the forward chain, the closure updates, the support relabel and the memo
  invalidation, O(touched × degree);
- a first read of `S` at `C` costs O(|support ancestor set of `S`| × postings under the
  key arguments of `S`);
- a warm read costs O(1) until a handle the memo watches moves.

**Every disagreement has a kind.** `gen/check-world` classifies each disagreement by the
shape of the minimal shrunk world, and a disagreement it cannot classify is
`:unclassified`. `vaelii.reference-test`'s `known-divergences` map names each known kind
with the decision it follows from and the prompt it waits on. The test fails on a kind
outside the map, `:unclassified` included, and counts and prints every known one. A write
the engine refuses and the reference stores is an `:engine-refused-*` divergence: the
reference judges `W` as offered, the engine side is read without the refused write, and
the run is reported under that divergence rather than as a belief disagreement. An entry
leaves the map when the prompt it waits on lands.

## The fragment

v1 of the reference covers the rows marked yes. A KB holding a row marked no is refused
by the world extractor with `:unsupported`, so the generator cannot produce one.

| feature | in v1 | where the engine documents it |
|---|---|---|
| ground facts and denials, `:monotonic` and `:default` | yes | [nmtms.md](nmtms.md#strengths-and-the-defeat-class-vaeliiimplstrength) |
| `genl` between types, rooted at `thing` | yes | [taxonomy.md](taxonomy.md#genl-the-type-hierarchy) |
| `genlCx`, acyclic, `:monotonic` | yes | [contexts.md](contexts.md#genlcx-the-context-hierarchy) |
| `genlCx` at `:default`, or denied | no, by invariant 1 | [contexts.md](contexts.md#genlcx-the-context-hierarchy) |
| forward `implies` with `and` bodies and variables | yes | [inference.md](inference.md) |
| `unknown` in a rule antecedent | yes | [naf.md](naf.md) |
| `exceptWhen` | yes | [exceptions.md](exceptions.md) |
| negation nogoods | yes | [nmtms.md](nmtms.md#soft-prioritized-contradictions-the-settle-layer) |
| `disjoint` | yes, forced monotonic (invariant 6) | [taxonomy.md](taxonomy.md#disjointness) |
| `functional`, `functionalInArg` | yes, symbol fillers included, except the all-`:monotonic` merge (invariant 4) | [taxonomy.md](taxonomy.md#predicate-metadata) |
| `irreflexive`, `anti_symmetric` | yes, as nogoods (invariant 2) | [taxonomy.md](taxonomy.md#predicate-metadata) |
| a `:default` write of a mark, `disjoint`, `covering` or a predicate `genl` | yes, stored `:monotonic` (invariants 2, 5 and 6) | [taxonomy.md](taxonomy.md#predicate-metadata) |
| a denial of a mark, a declaration or a predicate `genl` | no, by invariants 2, 5 and 6 | [taxonomy.md](taxonomy.md#predicate-metadata) |
| a rule concluding a forced-monotonic predicate | no, by decision 17 | [taxonomy.md](taxonomy.md#what-a-rule-may-conclude-and-what-it-reaches) |
| `anti_transitive` | yes | [nmtms.md](nmtms.md#a-nogood-is-a-set-anti_transitive-has-three-members) |
| `covering` | yes, forced monotonic (invariant 6) | [taxonomy.md](taxonomy.md#covering-a-whole-and-the-parts-named-against-it) |
| `transitiveInArg` along `genl`, one position | yes, decision 5 | [inherit.md](inherit.md) |
| equality: `rewriteOf`, `sameAs`, `equals` | no | [equality.md](equality.md) |
| supersession | no | [equality.md](equality.md), [nmtms.md](nmtms.md#the-set-membership-states-a-node-can-hold) |
| visibility `except` | no | [contexts.md](contexts.md#except-removing-visibility-down-a-context-subtree) |
| argument types, mints, lifts | no | [argtypes.md](argtypes.md), [contexts.md](contexts.md#decontextualized_predicate-a-fact-that-belongs-to-the-kb-not-to-one-theory) |
| generators (rules concluding rules) | no | [generators.md](generators.md) |
| backward-only rules | no | [inference.md](inference.md) |
| the qualitative calculi | no | [qcn.md](qcn.md) |
| NATs | no | [nat.md](nat.md) |
| quantities | no | [quantity.md](quantity.md) |
| `disjoint_metatype`, `sibling_disjoint` | no; `sibling_disjoint` is forced monotonic (invariant 6) | [taxonomy.md](taxonomy.md#disjointness) |
| `partition`, `separating` | no; `partition` is forced monotonic (invariant 6) | [taxonomy.md](taxonomy.md#partition-and-separating-add-no-separation-mechanism-of-their-own) |
| `arity` | no; forced monotonic, and a violation is a one-member nogood (invariant 6) | [taxonomy.md](taxonomy.md#arity) |
| the ASP solver | no | [asp.md](asp.md), [labeling.md](labeling.md) |
| `asymmetric` | yes, as the `asymmetric` family; forced monotonic (invariant 2) | [inherit.md](inherit.md#asymmetric-p) |
| `genl` between predicates of arity 2 or more | yes, forced monotonic (invariant 5); the generator writes none | [taxonomy.md](taxonomy.md#predicate-metadata) |

## The standing state

One row per atom the KB keeps between settles, ordered by the settle step that writes
it. The steps are the ones [nmtms.md](nmtms.md#the-runtime-view) numbers: *write* is the
assert and retract path with its store and removal choke points, 1–8 are `settle*`'s
steps, F1–F8 are `settle-finish`'s, and *read* is a cache a read fills. The last column
states the inputs whose change invalidates the atom, as the docstrings and the code state
them; **not stated** means no docstring, comment or stamp comparison says. **Partial**
marks a cell where the stated rule and the code disagree.

| atom | step | holds | written by | read by | invalidated by |
|---|---|---|---|---|---|
| `:opposed` | write | the bodies stored in both polarities | `kb/note-opposed!`; `kb/rebuild-opposed!` on recover | `settle/negation-nogoods` | a store or removal of either polarity. Partial: a bulk load with denials owes a `rebuild-opposed!`, because the choke point reads the index mid-load |
| `:preserving` | write | `{[P R] count}` of the `transitiveInArg` declarations stored | `kb/note-preserving!` | `settle/preserving-nogoods`, `vaelii.impl.inherit` | a store or removal of a declaration; belief is the reader's filter |
| `:excepted` | write | `{context {target #{except-handle}}}`, storage only | `kb/note-excepted!` | `vaelii.impl.resolution`, `special`, `settle` | a store or removal of an `except`; an except's belief is read live. Partial: the record comment gives the shape as `{except-handle hidden-handle}` |
| `:meta-except-count` | write | how many stored excepts target an except | `kb/note-excepted!` | `res/withdrawal-stamp` | a store or removal of an `except` |
| `:rule-antecedents`, `:rule-contexts`, `:solve-rules` | write | per antecedent key and per context, the rules indexed | `special/note-rule!`; `kb/rebuild-rule-roster!` | `special/visibility-seeds`, the chainer, `do/label` | a rule indexed or unindexed |
| `:minted` | write | the stored mint conclusions by term and by context, and the departed records owed a re-check | `special/entail-arg-type`, `integrate/sentex-removed!` | the mint re-checks beside step 6 | a mint justification added, a record leaving the store; the mint's belief is not tracked |
| `:sib-exc-dirty` | write | the `siblingDisjointException` pairs a retraction removed | the exception's retract arm in `special` | step 3 | a queue: F5 empties it |
| `:recheck` | write, 2, 4 | `{rule-handle triggers}`, the rules whose block conditions owe a re-evaluation | `special/mark-recheck` | step 5 | a queue: step 5 drains it. Partial: the record comment names fact moves on an exception's predicates and taxonomy edges; the code also posts on declarations, preserving extents, calculus entailments, `except` moves and rule indexing |
| `:except-moves` | write, 2, 4 | the handles an `except` began or stopped hiding, and the denials that moved | `special/note-except-move!`, `special/note-denial-move!` | the loop beside step 6, F3 | a queue: F3 takes it, and a leftover forces a full supersession pass |
| `:respell` | write | the predicates whose permuting marks moved | `special/note-permuting-moves!` | the re-seed after `settle*` | a queue, posted when the permuting-mark pair changes identity at a removal or a relabel |
| `:refused` | write, 8 | `{rule-handle #{refusal}}`, the firings a block condition declined, plus pending mints and lifts | `chain/record-refusal!`, `special/note-pending!` | steps 7–8 | a refusal dies when it fires, its rule goes, or its antecedents stop being believed; a rule's entries are re-asked only while the rule is on `:recheck`; constraint and lift entries on a move of the `genl` or `genlCx` generation or a region naming the term; mint entries on the generation alone |
| `:qcn-joined` | write, 8 | per calculus and context, the network the rules were last joined over | the chainer's qualitative re-join | the next join | none by design: a missing baseline makes the next join a full one |
| `:violations` | write, F5 | the ledger of dropped conclusions and sweep cuts, newest 1000 | `vaelii.impl.violations` | `core/violations` | not a belief input: a retraction does not withdraw an entry, `clear-violations!` empties it, and a refused firing placed later withdraws its entry |
| network `:defeated` | 1, 4 | the datums the network holds OUT | `jtms/defeat`; `jtms/clear-defeats!` | the relabel | emptied at step 1 and re-decided at step 4, every settle |
| `:scoped-defeats` | 1, 4 | `{vantage #{handle}}`, the losers of a vantage below their own context | `settle/scope-defeats!`; `settle/clear-scoped-defeats!` | the withdrawal, the settle, `special/visibility-seeds` | emptied at step 1 and re-decided at step 4, every settle |
| `:vantage-disagreements` | 1, 4 | one entry per nogood whose vantages defeated different members | `settle/note-vantage-disagreements!` | the withdrawal, `settle/disagreement-reports` | emptied at step 1 and re-decided at step 4, every settle |
| `:clashes` | 3, F3 | the definitional-pair memo, the `:held` pairs and the pending sweep keys | `settle/clash-nogoods` | step 3 | a member in the region or in `clash-dirty` (a supersession flip, an equality move), a change of `clash-vocabulary`, or a move of the pair's `genl` view; a member no longer stored drops the pair. Partial: nmtms.md lists four of the ten vocabulary components the stamp compares |
| `:arbitration-cursors` | F5 | the unread tails of the sweeps a budget cut | `settle/carry-arbitration-sweeps!` | step 3 | a queue, pruned to the keys `:clashes` still names; a trigger no longer stored or believed is dropped; a throwing settle empties it |
| `:negations` | write, 4, F3 | per opposed body, its nogoods and the contexts each polarity is believed in | `settle/negation-nogoods`, `kb/note-opposed!` | step 4 | the region, the bodies a store or removal posted, a `genlCx` move whose verdicts changed, a supersession flip ([nmtms.md](nmtms.md#the-negation-memo)). Partial: the record comment says a context edge retires the whole memo, and the code re-derives only the bodies whose verdict moved |
| `:preserved-clashes` | 4 | per stored claim, its inherited nogoods, the askers and the classes read | `settle/preserving-nogoods` | step 4 | a member OUT or reclassed, a vocabulary move, a moved claim that reaches it, a retraction in the region, and the stamp of the `genlCx` generation, `tax/flat-contexts` and `:excepted` ([nmtms.md](nmtms.md#the-inherited-clash-memo)) |
| network `:blocked` | 8 | the justification ids whose block condition holds | `jtms/set-blocked`, from `settle/exception-blocked-set` | `valid?` | the `:recheck` triggers. Partial: `set-blocked` says the caller re-evaluates every exception, and `exception-blocked-set` carries every block outside the queued candidates forward |
| taxonomy relations | write, 2, F2, F4 | per relation, the supporters, the active edges and a generation | `tax/add-edge` and its removal twin, `tax/refresh-beliefs` | every closure read | an edge change moves the generation; `refresh-beliefs` after a relabel re-activates an edge exactly when some supporter is believed ([taxonomy.md](taxonomy.md#the-closures-are-derived-state)) |
| taxonomy side caches | read | `:closure-memo`, `:closure-lru`, `:vis-index`, `:rewrite-order` | the closure reads | every closure read | the relation's generation, plus the `genlCx` generation, the census generation and the supporter-visibility generation for `:vis-index`. Partial: `:rewrite-order` is stamped on the identity of the active rewrite map, not a generation |
| network `:superseded` | F3 | the displaced spelling of each merged datum | `special/refresh-supersessions` | `in?` | replaced every settle, narrowed by `special/region-suffices?` |
| `:supersessions` | F3 | the stamp the superseded set was last reconciled against | `special/refresh-supersessions` | F3 | the equality edges, the `rewriteOf` preferences, the rewrite rules and the `genlCx` generation (`special/supersession-stamp`). Partial: the stamp omits `:excepted`, which the reconcile reads; `:except-moves` forces the full pass instead |
| `:clash-readings` | F5 | the conflicts, the contradictions and the report memo, as one publication | `settle/record-clashes!` | `core/conflicts`, `core/contradictions` | republished whole each settle; a report is kept while no member is in the region and its `:kind` and vantages match |
| `:feed` | F6 | the change feed's listeners and the region filed for them | `feed/note-region!` | the delivery at the end of `settle` | not a cache: delivery claims and empties the region |
| `:withdrawn` | read, F7 | per reader, what it reads as withdrawn, with a watch per entry | `res/install-withdrawn!` | `res/withdrawal`, the scoped taxonomy reads | the stamp of the network, `:excepted`, `:scoped-defeats`, `:vantage-disagreements`, the superseded map, `:meta-except-count` and the `genlCx` generation empties it; a watch meeting the touched window drops an entry ([nmtms.md](nmtms.md#the-withdrawal-cache)). Partial: the record comment names three of the seven stamp parts |
| `:settle-stats` | after F8 | counts of passes and blocked-set moves | `settle/settle-finish` | `core/settle-stats` | a counter; belief reads none of it |
| `:closures` | read | the reach sets the provers walked | `provers/cached-reach` | the provers | `observe/change-clock`, which every store, removal, relabel and taxonomy change moves |
| `:matches` | read | what `res/matches-visible` answered | `vaelii.impl.literal-cache` | `res/matches-visible` | `observe/change-clock` |
| `:qcn` | read | each calculus's network per context, and other clock-stamped readings | `vaelii.impl.qcn-kb` and its neighbours | the calculus provers | `observe/change-clock` |
| `:program` | none | the last Program handed to a solver | the labeling solver, a batch rollback | the labeling readers, `core/last-program` | **not stated.** No settle writes it, and no content or belief change invalidates it; `core/last-program`'s docstring says it is nil until a tie is arbitrated, and a settle's arbitration never writes it |
| `:chain-stats` | write, 8 | the run count and the last run's result | `chain/chain-all` | `core/chain-stats`, `core/preview`, the violation run id | **not stated**; nothing resets it |
| `:unrecovered` | open, recover | the write hazards declared and not yet retired | `kb/note-hazards!` and the recovery path | `kb/write-hazards`, `kb/read-view` | history rather than a derivation: `recover` and `reindex` retire what they rebuilt |

Four atoms are counters, queues or history rather than caches of belief: `:settle-stats`,
`:chain-stats`, `:violations` and `:unrecovered`. Belief reads none of them.

**Under decision 16.** Decisions 10 to 16 remove these atoms or reduce them to a lookup
per read:

- `:scoped-defeats`, `:vantage-disagreements`, network `:defeated`, `:arbitration-cursors`
  with the budget cut and carry, `report-unarbitrable-reach!` and `report-arity-reach!`
  go;
- `:clashes` with its `:held` pairs, `:negations`, `:preserved-clashes` and
  `:clash-readings` reduce to a lookup per read, with `contradictions` and `conflicts`
  scanning a write-time candidate index;
- the `:recheck` queue loses its `unknown` half, and `:except-moves` and `:respell` lose
  their relabel halves;
- the `:supersessions` stamp goes, and network `:superseded` is reconciled on the write
  path (decision 13);
- `:withdrawn`'s stamp drops from seven parts to four.

## What the reference does not tell you

The reference says what belief is and never how fast a settle reaches it. It recomputes
every context from every premise on every call, which is the cost locality exists to
avoid. The cost contract of a settle, step by step, with the gate that holds each bound,
is [nmtms.md](nmtms.md#the-runtime-of-a-settle).

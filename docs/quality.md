# Reading the KB rather than the engine

- **Covers:** `kb-quality` — which rules never fire, how skewed the predicate extents
  are, how deep the rule graph's chains reach, how much of the taxonomy is connected,
  which argument declarations constrain nothing — what each reading costs, and what each
  one does *not* mean.
- **Not here:** how a run went (iterations, derived conclusions, dropped ones) →
  [api.md](api.md)'s instrumentation block and [inference.md](inference.md); whether the
  engine's own grammar is read by anything → `vocabulary-audit`; the naming rules a type
  name obeys → [naming.md](naming.md).
- **Assumes:** sentex, handle, justification, informant, `genl` →
  [glossary.md](glossary.md).

`vaelii.impl.quality`, behind `vaelii.core/kb-quality`. Every other instrument here
reports on a **run**: `settle-stats` counts fixpoint iterations, `chain-stats` counts
derived conclusions, `violations` lists the ones that were dropped. None of them is a
reading about the *knowledge*, so the author of a large KB — who wants to know whether any
of it is any good — had no answer at all.

Five questions, and the whole of this page is them:

| question | the read that answers it | cost |
|---|---|---|
| which rules never fire | per rule handle, the justifications naming it as informant | O(rules + firings) |
| how skewed are the extents | `count-with-functor` per predicate | O(predicates), each O(1) |
| how deep do chains reach | the rule graph, SCC-condensed | O(V+E) over *functors* |
| how much of the taxonomy is connected | the `genl` closure per type | O(ancestor **pairs**) — each type's whole up-closure is read to find its root, so a chain of V types costs Θ(V²) where it has V−1 edges |
| which argument declarations constrain nothing | the declared arity per stored declaration | O(declarations × super-predicates) |

Plus the term roster, walked **once** to find the functor names the first four readings
are about — which is the report's one superlinear term and the reason the total below
leads with it.

**Nothing is a gate.** A threshold on somebody's ontology is not a build failure — `lein
perf` gates the engine, and this reports on the content. What *is* gated is the report's
own cost: `lein perf`'s `quality-report-scaling` check holds it to the vocabulary rather
than to the KB.

## One pass, and nothing new indexed

A `rule -> firings` index would be a second copy of the JTMS adjacency to keep in step,
which is the failure class the taxonomy's single `:support` map exists to avoid. So every
reading comes off state that is already there:

- **One walk over the term roster**, and one is the number. The functor names come off it
  by filter, and the type-shaped names come off *those* rather than off the roster a second
  time — every type name is lowercase-initial, so it is already in the first answer.
- **Three O(1) index reads per functor name** — the stored extent off the count-aware trie
  ([indexing.md](indexing.md)), and the rule postings *both* ways. That single pass is
  where the extents come from, where the chain graph comes from, and where the rule handles
  come from.
- **The firing census reads each rule's own `:consequences` adjacency** — the candidate set
  `restrength-informant*` already uses, filtered to the justifications whose *informant* is
  that rule, so a justification that merely uses the rule's handle as an ordinary
  antecedent is not counted. It never scans the justification map; at 11.5M justifications
  the difference is the report existing or not.
- **The declaration census enumerates the declarations** and asks each what binds its own
  predicate's length, rather than asking every predicate what declares it. That is a map
  read where the predicate carries a length of its own and one read per super-predicate
  where it inherits one — the only term in the total that is not flat, and one bounded by
  the hierarchy *above* a predicate rather than by the spec subtree below it.
- **The record store is read for the rules the report lists** — a handful, capped by
  `:limit`, so a listed rule reads as its author wrote it rather than as a handle — and
  for the argument declarations, which are vocabulary and therefore few: 298 in the whole
  bundled ontology.

So the report is
`O(terms + rules + firings + ancestor pairs + declarations × super-predicates)` and never
`O(sentexes)` — the **vocabulary**, which is what the perf check's claim says and what it
measures: 8x the stored facts over 2.8x the vocabulary costs 1.5x, and 8x the vocabulary
costs 8x. A KB of a million facts about a hundred individuals has a hundred-odd names in
it, and that is the number the report answers to.

Rules are enumerated from the **rule index**, which means one absence worth knowing: a
rule the index cannot key by any predicate — an `:inert` one written with a variable
functor throughout, which is what the shipped ontology's own documentation rule is — is
outside the census. It is also a rule that runs in neither engine, so it could not
have fired.

## Which rules never fire, and the two categories beside it

Three outcomes, and four situations produce them:

| the situation | where it lands |
|---|---|
| the rule fired and a conclusion is believed | `:fired`; every recorded firing counts in `:firings` |
| nothing ever matched its antecedent | `:never` |
| it fired, and every conclusion is defeated | `:all-defeated` |
| it fired, and the support was later retracted | `:never` |

The last row is the one to read twice. **A firing is a *currently supported* one.** The
census reads live justifications, so a rule whose conclusion has been withdrawn has none
left and reads as though it had never fired. Firings-ever is a different question and
nothing here answers it — a KB does not keep a history of what it once believed.

`:all-defeated` is separated out because it is the more interesting finding: such a rule
runs, contributes nothing to belief, and would read as working from a firing count alone.

The counts are the headline and the lists are capped (`:limit`, 25 by default) with
`:truncated?` saying so. A listed rule carries `{:handle :sentence :context}`, and the
sentence is the one that was *written* — a rule is stored canonically numbered
([canonicalization.md](canonicalization.md)), which reads as gibberish.

## Extent skew: buckets to read, a Gini to record

Order-of-magnitude buckets are what an author reads (`10^0` holds the predicates with a
single fact); the Gini coefficient is the single number that goes in a baseline — 0.0 when
every predicate holds the same count, `(n-1)/n` when one holds everything, so a small
vocabulary cannot reach 1.0 and the figure must not be read as though it could.

Both are over **stored** counts, and that is not a default anybody should change: a
believed extent is O(n) per predicate ([api.md](api.md), "Stored vs believed"), which
would turn an O(predicates) report into an O(sentexes) one. The stored/believed
distinction is exactly what an author wants to see rather than have chosen for them.

The measured shape on a converted OpenCyc 4.0 corpus at 1.14M sentexes: Gini **0.9621**,
over 7,602 predicates with an extent, of which 5,162 hold exactly one fact and 5 hold over
100,000.

## Chain depth, and the reason it is condensed

The rule graph runs consequent functor → antecedent functors. A KB's is **cyclic in the
ordinary case**: `(genl ?a ?b) & (genl ?b ?c) => (genl ?a ?c)` is a self-loop on `genl`,
and a transitive predicate is the commonest rule there is. So the depth pass condenses
strongly-connected components and computes over the condensation, which is a DAG.

Two mistakes are avoided by construction here, and both are cheap to make:

- **Memoizing the path rather than the node.** Memoizing only acyclic results makes a
  densely cyclic graph re-explore its whole reachable subgraph along every path — not slow
  but *exponential*, with no termination and only a JVM restart to clear it. Memoize the
  component.
- **Keying the condensation by the component itself.** Two node sets compare equal in
  O(nodes), and the condensation runs one such comparison per edge, which turns O(V+E)
  into O(V·E) — the same mistake wearing a quieter hat. Components are keyed by an integer
  id: measured on a 4,000-functor cycle, 1,146 ms became 36 ms.

Depth is reported **per rule** — the depth of the component its consequent functor lands
in — as a histogram plus `:at-least`, the fraction of rules in a chain at least that deep.
The distribution is the reading and a single number is not: most rules can sit at depth 1
while one outlier reaches 7, and an average hides both.

`:cyclic` counts a self-loop as the cycle it is. Counting only multi-node components would
report the commonest cycle in any KB as acyclic.

## Taxonomy coverage is two numbers

`:edged` is how many type names carry a `genl` edge at all. `:rooted` is how many reach
the root, reflexively, so the root counts itself. **The gap between them is the finding**:
a type with an edge into a disconnected island is counted by the first and not the second,
and `:islands` is exactly that difference.

The root is **found, not assumed**. `thing` is this engine's root and a converted corpus
brings its own, so whatever type the most others reach is the one reported against, and
the reading means the same on a corpus that never heard of `thing`.

The denominator (`:names`) is every type-shaped name in the vocabulary, and by
[naming.md](naming.md) that includes a bare lowercase word: `likes` is a legal predicate
*and* a legal type name, arity decides, and the index records no arity to tell them apart.
`genl` itself is counted. Which is the reason the gap is the finding rather than either
fraction on its own.

The measured shape on the same OpenCyc conversion: of 124,417 types, 88,245 (70.9%) carry
a `genl` edge and 79,948 (64.3%) reach the root — and the 29% with no edge at all is a
bigger finding than either.

## Argument constraints that constrain nothing

`(argIsa parentOf 3 person)` is admitted while `parentOf` has no declared length, because
the highest position a declaration names is a lower bound on the arity rather than a claim
about it. When a length does arrive — declared of the predicate, or inherited through a
`genl` edge from a super-predicate — the declaration is left constraining a position the
predicate provably does not have, and the door refuses the identical sentence one line
later. `:declarations` is what names those, and without it a declaration that is enforced
and one that enforces nothing look exactly alike.

It is the **door's own arm, re-asked** of content already stored, so what the census lists
and what an `assert` refuses cannot drift apart: whatever binds a predicate's length for
the door binds it here, and a predicate the KB has bound to no length strands nothing.
`interArgIsa` names two positions and each is asked, since both are the same mistake.

A **`variableArity`** predicate strands nothing either, however high the position: it reads
a tuple of any length from its declared arity upward, so a position past that length is one
its tuples really do reach, and the constraint fires on the tuples long enough to have it.
`lessThan`, `greaterThan` and `functionCorrespondingPredicate` are the shipped ontology's.

Belief-filtered, unlike the extent counts: a stored declaration nobody believes constrains
nothing for a reason that has nothing to do with the position it names, and listing it here
would report the wrong defect.

An entry is `{:handle :sentence :context :predicate :position :arity :via :message}`.
`:via` is the predicate the length was read off — the declaration's own where it carries
one, the super it inherits from otherwise, so an author is not sent looking for a
declaration nobody wrote. `:message` is the sentence the check itself wrote, carried rather
than re-derived, so this map and `check`'s answer say it in the same words. `:total` counts
the declarations walked, `:stranded-count` the ones convicted, and the list is capped by
`:limit` with `:truncated?` saying so.

**A finding rather than an error**, and the reason it is a census question and not a
`violations` one: a stranded declaration constrains nothing, refuses nothing and mints
nothing, so there is no *newly* for a settle to report and it reads the same an hour later.
[taxonomy.md](taxonomy.md) has that argument in full, against the wrong-length **fact**,
which is a ledger entry.

## Reading it

`kb-quality` answers data; `quality-report` renders that same map as Markdown and reads
nothing else, so it cannot print a figure the data does not hold — and refuses a map that is
not one of its answers (`:not-a-report`), because a page of zeros and dashes is a report a
caller who passed the wrong map cannot tell from a report of an empty KB. `:on-progress` is
called as each phase begins, in the order they run — `:extents`, `:rules`, `:chains`,
`:taxonomy`, `:declarations` — and may **throw to cancel**, the reading being of current
state, so a half-finished one is discarded rather than repaired. A phase reports itself
before its loop, so one with nothing in it is still announced: "skipped because empty" and
"not reached" must not read the same to a caller watching for where a long report is.

Read **without a snapshot**, like every other reader here: a write landing mid-report can
leave a count and a list disagreeing by one, since a rule enumerated and then retracted is
dropped from the listed set and stays in the total. A reading of a moving KB, not a
transaction over a still one.

`:firings` is every recorded firing in the KB, the defeated ones included — not the live
rules' share of them, which is why the rendered sentence states it as a total.

    lein cli quality --dir /path/to/kb        # the report, as a document

That is the only consumer in the tree, and it is what keeps the pair exercised.

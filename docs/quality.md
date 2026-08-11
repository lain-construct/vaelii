# Reading the KB rather than the engine

- **Covers:** `kb-quality` — which rules never fire, how skewed the predicate extents
  are, how deep the rule graph's chains reach, how much of the taxonomy is connected —
  what each reading costs, and what each one does *not* mean.
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

Four questions, and the whole of this page is them:

| question | the read that answers it | cost |
|---|---|---|
| which rules never fire | per rule handle, the justifications naming it as informant | O(rules + firings) |
| how skewed are the extents | `count-with-functor` per predicate | O(predicates), each O(1) |
| how deep do chains reach | the rule graph, SCC-condensed | O(V+E) over *functors* |
| how much of the taxonomy is connected | the `genl` closure per type | O(types + edges) |

Plus the term roster, walked **once** to find the functor names those four readings are
about — which is the report's one superlinear term and the reason the total below leads
with it.

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
- **The record store is read only for the rules the report lists** — a handful, capped by
  `:limit` — and only so a listed rule reads as its author wrote it rather than as a
  handle.

So the report is `O(terms + rules + firings + genl edges)` and never `O(sentexes)` — the
**vocabulary**, which is what the perf check's claim says and what it measures: 8x the
stored facts over 2.8x the vocabulary costs 1.5x, and 8x the vocabulary costs 8x. A KB of a
million facts about a hundred individuals has a hundred-odd names in it, and that is the
number the report answers to.

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

## Reading it

`kb-quality` answers data; `quality-report` renders that same map as Markdown and reads
nothing else, so it cannot print a figure the data does not hold — and refuses a map that is
not one of its answers (`:not-a-report`), because a page of zeros and dashes is a report a
caller who passed the wrong map cannot tell from a report of an empty KB. `:on-progress` is
called as each phase begins (`:extents`, `:rules`, `:chains`, `:taxonomy`) and may **throw
to cancel** — the reading is of current state, so a half-finished one is discarded rather
than repaired.

Read **without a snapshot**, like every other reader here: a write landing mid-report can
leave a count and a list disagreeing by one, since a rule enumerated and then retracted is
dropped from the listed set and stays in the total. A reading of a moving KB, not a
transaction over a still one.

`:firings` is every recorded firing in the KB, the defeated ones included — not the live
rules' share of them, which is why the rendered sentence states it as a total.

    lein cli quality --dir /path/to/kb        # the report, as a document

That is the only consumer in the tree, and it is what keeps the pair exercised.

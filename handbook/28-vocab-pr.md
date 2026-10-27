# 28. The vocabulary change

- **Covers:** what a change to the vocabulary states when it goes to review: the
  separation counts before and after, the pairs it gives up, the top unknowns, the
  decisions it banked, the integrity run and the findings it keeps, the cases it leaves
  open, and the common-sense tests it adds.
- **Not here:** the steps that produce these results → [ch. 27](27-audit-sequence.md);
  why a removed separation reaches far below its pair → [ch. 16](16-unknowns.md); the
  file the change edits → [ch. 26](26-file-layout.md); the common-sense questions the
  suite asks per subsystem → [commonsense.md](../docs/commonsense.md).
- **Assumes:** [ch. 16](16-unknowns.md), [ch. 27](27-audit-sequence.md),
  [ch. 2](02-representation.md).

A vocabulary change is reviewed from its description and its diff. The diff shows the
sentences. The description states what the sentences do to the KB as a whole, which the
diff does not show: which type pairs moved from disjoint to unknown, which decisions were
weighed and declined, and which expected conclusions the engine does not yet derive.

## Separation counts

*The report **measure a removed separation** asks for*

**Practice.** Run `disjointness-audit` at the base revision and at the change, in the
same context, and state the counts by status for both. When a separation was removed or
narrowed, list every pair that moved to `:unknown`, restate at the tightest true level
each one that still holds, and name the ones the change gives up.

**Example.** The counts come from one read per revision:

```clojure
(:by-status (v/disjointness-audit kb 'CxWell))
```

The description then carries one line per status, base and change side by side, and
the list of pairs that moved.

**Why.**

- Logical: a `disjoint`, `partition` or `separating` declaration rules out every pair of
  subtypes below its two sides, so removing one turns unknown every pair that only it
  separated. The pair it names is one of many it governs.
- Engine: `disjointness-audit` reads the `subsumption-status` of every unordered pair of
  types visible from the context, and reports each as `:coextensional`, `:genl`, `:spec`,
  `:disjoint`, `:orthogonal`, `:unknown` or `:inconsistent`. The shared-instance query it runs for an
  open pair expands no rule, so the sweep reads the stored knowledge rather than a proof
  search. The `disjointness-coverage-ratchet` test holds a floor on the disjoint pair count
  and on the disjoint share, and a ceiling on the unknown share, so a change that drops
  coverage fails the test until the floor is lowered.
- Maintenance: lowering the ratchet's floor is a deliberate edit in the same change, and
  the description names the pairs that edit gives up. A reviewer then reads a list of
  pairs and decides each, instead of a count that moved.

**Why not the other ways.** Stating only the separation removed leaves the reviewer to
discover which pairs below it changed status. Stating only the totals hides which pairs
moved: a change can remove twenty disjoint pairs and add twenty others, and the totals
read unchanged.

**Audit.** The description states the disjoint and unknown pair counts before and after,
and names each lost pair it does not restate.

## The top unknowns

*The report **top unknowns** asks for*

**Practice.** Beside the counts, list the five type pairs whose relationship is unknown
that one decision would settle most of, ranked by how many open pairs that decision settles,
each with the decision the author proposes: a `disjoint`, an `orthogonal` with its witness,
or a `genl`.

**Why.** An `:unknown` pair is a question the KB has not answered: neither disjoint, nor
`genl`-related, nor declared `orthogonal` or witnessed by a shared instance. One decision
high in the hierarchy settles every pair below it, so the ranking puts the decision with
the widest reach first. The audit reads a declared `orthogonal` pair as `:orthogonal`,
never `:unknown`, so the list holds only real open questions once settled overlaps are
declared.

**Why not the other ways.** A change that reports only its own inconsistencies leaves
the unknowns to grow unread. A list of unknowns with no proposed decision hands the
decision back to the reviewer with no starting position.

**Audit.** The description lists five unknown pairs from `disjointness-audit`'s
`:pairs-data` with `:status :unknown`, each with a proposed decision. The ranking is the
author's.

## Banked decisions

*The report **bank the decision** asks for*

**Practice.** List each property, edge or declaration the change weighed and declined,
with the `(not …)` sentence that states the decision in the KB, or the `(orthogonal A B)`
for a declined separation.

**Example.** `abstract.txt` banks the decision that `partOf` is not antisymmetric:

```clojure
(not (anti_symmetric partOf))
```

Two coextensive regions stay two regions, so `partOf` relates two distinct things in both
directions.

**Why.** Absence is not negation: a missing `(anti_symmetric partOf)` says only that
nobody stated it. A stated negation is visible to the engine and to the next reviewer, so
a later change that would reverse the decision meets it. `anti_symmetric` is
forced-monotonic, so the denial is believed while no `(anti_symmetric partOf)` is, and it
loses to one that is believed. Listing the negations in the description lets a reviewer
check that each one stands for a decision made in this change, and not for a gap filled
by guesswork.

**Why not the other ways.** A decision recorded only in the review thread is invisible to
the KB, and the next author who weighs the same question finds a silence. A negation
asserted to fill a gap the change never weighed states a decision nobody made.

**Audit.** Each declined decision the description lists has its `(not …)` or `orthogonal`
in the diff, and each `(not …)` in the diff has its decision in the description.

## The integrity run

**Practice.** Quote the `:status` of the two `kb-integrity` runs over the new and changed
terms ([ch. 27](27-audit-sequence.md)), and account for every finding: fixed in the
change, or kept with its reason ([Acknowledged findings](#acknowledged-findings)).

**Why.** `kb-integrity` reports the defects nothing on the write path reports: a type
with no path to `thing`, a predicate `genl` that widens an argument type, a position no
declaration types, a stated edge that derives without itself. Each of these stores
without a violation, so the run is the one place they surface before a reviewer reads the
diff. A `:truncated` status means a bound ran out, and the findings it carries are
partial.

**Why not the other ways.** A description that says the run was clean without quoting the
status cannot be told from one that ran with a bound too small to finish.

**Audit.** The description quotes each run's `:status`, and a `:gap` finding with no fix
carries its reason, such as the **state it once** exception its note names.

## Acknowledged findings

*The record **bank the decision** asks for, for a finding the change keeps*

**Practice.** When a `:rule-macro` or `:rule-clash` finding stays, state an
`acknowledgedFinding` with the reason, in the context the sweep reads it from: the rule's
context for `:rule-macro`, and the pair's context for `:rule-clash`. The subject names the
finding by its content: the suggested declaration for a rule macro, and
`(RulePairFn (Quote R1) (Quote R2))` for a rule clash. A finding in any other category
stays with its reason in the description, or in a `;;` note in the file
([ch. 26](26-file-layout.md)).

**Example.** The acknowledgment `core.txt`'s comment gives as an example, and
`declined_rule_macro`, which states the same decision with no reason:

```clojure composed
(acknowledgedFinding :rule-macro (genl livesIn locatedIn) "livesIn is meant as a default")
(declined_rule_macro (genl livesIn locatedIn))
```

**Why.**

- Engine: the sweep moves an acknowledged finding to its category's review-only bucket,
  `:rule-macro-review` or `:rule-clash-review`, with the reason beside it as
  `:acknowledged`. The finding stays visible to a review run and no longer turns a
  default run's `:status` to `:gap`. The record draws no inference, and no other category
  reads it.
- The subject names the finding by content, so the record survives `export-text!` and a
  reload. An edit that changes the rule's shape changes the suggestion or the pair, and
  the finding comes back. Retracting the record brings it back too.
- The KB reads a `RulePairFn` subject as an unordered pair: `core.txt` states
  `(commutative RulePairFn)`, so the two orders store as one sentex, and nothing is sorted
  inside either quote. The sweep compares each quoted rule with the finding's rule by
  canonical sentence, so variable names and antecedent order do not change the match.
  That comparison is the sweep's own: everywhere else a quoted sentence matches only its
  spelling ([ch. 43](43-reflection.md)). Quote the rules as the finding's `:sentences`
  report them, and the record matches under either reading.
- `declined_rule_macro` is sugar: a forward rule in `core.txt` concludes an
  `acknowledgedFinding` from it, with a reason that says none was supplied. The sweep
  reads only the acknowledgment.

**Why not the other ways.** A record that names the rule by `(sentexHandle H)` names a
handle of one store. `export-text!` skips a sentence that names a handle, so the record
does not survive a reload. A reason kept only in the review thread leaves every later run
reporting `:gap` for a decision already made. `declined_rule_macro` records the decision
without its reason, so the next reviewer reads that the finding stays and not why.

**Audit.** Run `kb-integrity` with `:categories #{:rule-macro-review :rule-clash-review}`
over the change. Each finding marked `:acknowledged` has its record in the diff and its
reason in the description, and each record in the diff matches a finding.

## Open cases

*The report **truth, not provability** and the refinement audit ask for*

**Practice.** State which conclusions the change expects the KB to draw, which ones the
engine derives, which exclusions have explicit support, and which cases remain open. Name
each open case with the sentence the engine does not derive and the reason it does not.

**Why.** A definition is true or false independent of what the engine proves. A
conclusion the natural form states but the engine does not derive is an engine
limitation to surface, not a reason to change what the KB says (**ontology over quirk**).
A failure to derive a membership proves nothing about non-membership, so a case the
engine leaves undecided is reported as open, not as a negative.

**Why not the other ways.** A description that lists only the conclusions that derive
leaves the reviewer no way to tell which expected conclusions are missing. Rewording the ontology until every expected conclusion
derives replaces the true form with the form the current engine proves.

**Audit.** For each expected conclusion the description lists, `query` or `prove` it in
the change's context and record whether it derives.

## Common-sense tests

*The check **does it have rules?** asks for, kept in the suite*

**Practice.** For each conclusion the change exists to license, add a test to
`test/vaelii/common_sense_test.clj`, or to `common_sense_qualitative_test.clj` for a
qualitative calculus. The test asks a question the KB holds no stored answer to, phrased
as a person would ask it, over the shipped schema and the test-world's cast. Individuals
and contingent facts the question needs come from the test-world files
(`test/vaelii/world.clj` and its two siblings, below `CxWell`) or from facts the test
states; every rule the answer uses is shipped. A gap the question exposes in the schema is
fixed in the shipped files.

**Example.** `which-of-two-animals-is-heavier-is-read-off-their-weights` asks whether a
dog outweighs a cat. The test states the dog's weight in kilograms and the cat's in grams,
and no sentence states `heavierThan`. `CxSize.txt`'s backward rule answers it from the two
measures:

```clojure
(set/backwardRule
  (implies (and (weightOf ?x ?wx) (weightOf ?y ?wy) (quantityGreaterThan ?wx ?wy))
           (heavierThan ?x ?y)))
```

**Why.**

- A test that reads back what its fixture asserted tests storage. A question with no
  stored answer tests what the vocabulary adds: a membership nobody stated, a comparison
  nobody computed, a containment nobody wrote down.
- Both namespaces run in `lein gate`, so `lein gate` fails on a later change that stops
  the conclusion from deriving. The description's list of expected conclusions
  ([Open cases](#open-cases)) is read once, at review.
- The shipped files carry schema, and an individual is a fact about one world. The
  test-world holds the cast below `CxWell`, where every middle theory reaches it and no
  KB that loads the shipped files inherits it.

**Why not the other ways.** A fixture that asserts the answer passes whether or not the
vocabulary concludes anything. A rule written in the test to make the question answer
covers a gap that every other consumer of the shipped KB still has. An individual added
to a shipped file to give a test data puts a contingent fact in the schema every KB loads.
A test whose name needs the engine's vocabulary to make sense tests a subsystem, and
belongs beside that subsystem's tests.

**Audit.** For each conclusion the description lists as derived, name the common-sense
test that asks it, and read the test's fixture: it asserts no sentence the question reads
back.

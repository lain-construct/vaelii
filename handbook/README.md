# The vaelii ontological engineering handbook

This handbook teaches how to build ontology in a vaelii KB: how to choose a term, place
it, separate it from its neighbours, type its relations, decide where and how strongly it
holds, and write the rules that reason over it. Every practice comes with the reasons
behind it, stated in full in the chapter, so a reader without the rest of the repository
can follow each argument.

The handbook shows only correct forms. Where another way of stating something exists, the
chapter names that way in words and says what it would cost the KB.

The chapters are ordered as an author meets the decisions. Part I says what a KB is for,
and each later part depends on the parts before it. Part VIII covers the harder tasks:
rules, exceptions, definitions, negation and the reasoning built on them. Part IX covers
the vocabularies the shipped KB carries for identity, measures, time, space, change and
written forms, and how to state knowledge in each.

## How a chapter is laid out

Each chapter opens with **Covers**, **Not here** and **Assumes**, so three lines decide
whether to read it. A section treats one principle or one practice, in five parts:

- **Practice:** what to state.
- **Example:** a correct form, quoted from the shipped KB where one exists. `lein lint`
  checks every `clojure` block. A block that calls the public API (`v/…`) must name vars
  `vaelii.core` defines. Any other block is a quote, and each of its forms must appear in
  `resources/kb/` or the test-world files `test/vaelii/world*.clj`. A block the chapter
  wrote rather than quoted opens with `` ```clojure composed ``, which skips the quote
  check and keeps the API check.
- **Why:** what the form entails, what the engine does with it, and what happens to it
  as the KB grows or a premise is retracted.
- **Why not the other ways:** each alternative, named in words, with its consequence.
- **Audit:** the step to run on a vocabulary change, and the tool that runs it.

A principle has a short **handle**, set in bold wherever a chapter cites it. A section on
a principle is headed by its handle, with the full name below.

A link into `../docs/` leads to the engine's documentation for the mechanism a chapter
relies on. The chapter states the reason itself, and the link adds detail only.

## By task

| Task | Chapters |
|---|---|
| decide whether a term or a sentence belongs in the KB at all | [1](01-true-and-useful.md), [2](02-representation.md), [3](03-truth-not-provability.md) |
| add a type | [5](05-search-first.md), [6](06-definitional-block.md), [7](07-comments.md), [8](08-kind-of-term.md), [9](09-differentia.md), [10](10-parent.md), [11](11-siblings.md), [12](12-identity.md) |
| separate two types, or state that they overlap | [13](13-disjointness.md), [14](14-covers.md), [15](15-overlap.md) |
| remove or narrow a separation | [16](16-unknowns.md), [28](28-vocab-pr.md) |
| add a relation | [6](06-definitional-block.md), [17](17-predicate-hierarchy.md), [18](18-argument-types.md), [19](19-relation-properties.md) |
| model a happening and its participants | [20](20-events.md) |
| state a claim about a kind | [21](21-claims-about-kinds.md), [25](25-default-or-enumerate.md) |
| add a function | [22](22-functions.md) |
| choose the context and the strength of a sentence | [23](23-contexts.md), [24](24-strength.md) |
| write a rule, or a default with exceptions | [29](29-rules.md), [30](30-exceptions.md), [25](25-default-or-enumerate.md) |
| define a type by a membership condition | [31](31-definitions.md) |
| state a negation, or reason from what is not known | [32](32-negation.md) |
| state that a filler exists | [33](33-existentials.md) |
| write a rule that writes rules | [34](34-generators.md) |
| state something that holds over time | [35](35-change-over-time.md), [39](39-time.md) |
| state a fact over the time the source gives, in a time slice | [39](39-time.md), [19](19-relation-properties.md) |
| state what an agent believes, or what may be hypothesized | [36](36-agents-and-hypotheses.md) |
| state that two names denote one thing, or two things | [37](37-coreference.md) |
| state a measure, or add a unit or a dimension | [38](38-quantities.md) |
| relate intervals and instants, or date them | [39](39-time.md) |
| state how long something lasts | [40](40-durations.md), [38](38-quantities.md) |
| state where something is, or how regions and directions relate | [41](41-space.md) |
| state that a quantity rises or falls with no figure known | [42](42-signs-and-trends.md) |
| state something about a sentence, a term or a name | [43](43-reflection.md), [7](07-comments.md) |
| place the sentences in a file | [26](26-file-layout.md) |
| audit and describe a vocabulary change | [27](27-audit-sequence.md), [28](28-vocab-pr.md) |

## Contents

**Part I: What a KB is for**

1. [True and useful](01-true-and-useful.md)
2. [Representation over code over prose](02-representation.md)
3. [Truth, not provability](03-truth-not-provability.md)
4. [The economy of statements](04-economy.md)

**Part II: Minting a term**

5. [Search first](05-search-first.md)
6. [The definitional block](06-definitional-block.md)
7. [Comments](07-comments.md)
8. [The kind of term](08-kind-of-term.md)
9. [The differentia](09-differentia.md)

**Part III: Placing a type**

10. [The parent](10-parent.md)
11. [Siblings and intersections](11-siblings.md)
12. [Identity](12-identity.md)

**Part IV: Separations and overlaps**

13. [Disjointness](13-disjointness.md)
14. [Covers and partitions](14-covers.md)
15. [Overlap](15-overlap.md)
16. [Unknown pairs](16-unknowns.md)

**Part V: Predicates and relations**

17. [The predicate hierarchy](17-predicate-hierarchy.md)
18. [Argument types](18-argument-types.md)
19. [Relation properties](19-relation-properties.md)
20. [Events](20-events.md)
21. [Claims about kinds](21-claims-about-kinds.md)
22. [Functions](22-functions.md)

**Part VI: Contexts and strength**

23. [Contexts](23-contexts.md)
24. [Strength](24-strength.md)
25. [Default or enumerate](25-default-or-enumerate.md)

**Part VII: The file and the review**

26. [File layout](26-file-layout.md)
27. [The audit sequence](27-audit-sequence.md)
28. [The vocabulary change](28-vocab-pr.md)

**Part VIII: Harder tasks**

29. [Rules](29-rules.md)
30. [Exceptions](30-exceptions.md)
31. [Definitions](31-definitions.md)
32. [Negation](32-negation.md)
33. [Existentials](33-existentials.md)
34. [Generators](34-generators.md)
35. [Change over time](35-change-over-time.md)
36. [Agents and hypotheses](36-agents-and-hypotheses.md)

**Part IX: The shipped vocabularies**

37. [Coreference](37-coreference.md)
38. [Quantities and units](38-quantities.md)
39. [Time](39-time.md)
40. [Durations](40-durations.md)
41. [Space](41-space.md)
42. [Signs and trends](42-signs-and-trends.md)
43. [Reflection](43-reflection.md)

## The principles by handle

| Handle | Chapter |
|---|---|
| **bank the decision** | [2](02-representation.md) |
| **beware entity** | [9](09-differentia.md) |
| **broad under thing** | [10](10-parent.md) |
| **catbus principle** | [24](24-strength.md) |
| **classify before you constrain** | [13](13-disjointness.md) |
| **content, not handle** | [43](43-reflection.md) |
| **the context is the frame** | [41](41-space.md) |
| **date the points** | [39](39-time.md) |
| **default or enumerate** | [25](25-default-or-enumerate.md) |
| **different-type genl** | [17](17-predicate-hierarchy.md) |
| **differentia from near-misses** | [9](09-differentia.md) |
| **does it have rules?** | [1](01-true-and-useful.md) |
| **don't skip the predicate** | [22](22-functions.md) |
| **DRY** | [4](04-economy.md) |
| **event arg1** | [20](20-events.md) |
| **factor out commonalities** | [11](11-siblings.md) |
| **a figure carries its unit** | [38](38-quantities.md) |
| **identity, not likeness** | [37](37-coreference.md) |
| **the known disjunction** | [39](39-time.md) |
| **leave the converse to the algebra** | [41](41-space.md) |
| **look before you mint** | [5](05-search-first.md) |
| **match the siblings** | [11](11-siblings.md) |
| **meaning, not name** | [7](07-comments.md) |
| **measure a removed separation** | [16](16-unknowns.md) |
| **nesting values aren't individuals** | [8](08-kind-of-term.md) |
| **no naked terms** | [6](06-definitional-block.md) |
| **no OE calligraphy** | [1](01-true-and-useful.md) |
| **no teleology** | [9](09-differentia.md) |
| **objects in locatedIn, regions in RCC-8** | [41](41-space.md) |
| **OE over code over text** | [2](02-representation.md) |
| **ontology over quirk** | [3](03-truth-not-provability.md) |
| **partition over disjoint** | [14](14-covers.md) |
| **references in seeAlso** | [7](07-comments.md) |
| **represent the definition** | [2](02-representation.md) |
| **state it once** | [4](04-economy.md) |
| **strongest form** | [4](04-economy.md) |
| **tightest parent** | [10](10-parent.md) |
| **time from the slice** | [39](39-time.md) |
| **top unknowns** | [16](16-unknowns.md) |
| **truth, not provability** | [3](03-truth-not-provability.md) |
| **use by default** | [43](43-reflection.md) |
| **walk down** | [10](10-parent.md) |
| **what ends a member** | [12](12-identity.md) |

Several principles specialize another: **tightest parent**, **partition over disjoint**,
**classify before you constrain** and **the known disjunction** are cases of **strongest
form**, and **look before
you mint**, **factor out commonalities** and **state it once** are cases of **DRY**. Each
chapter names the principle a section specializes.

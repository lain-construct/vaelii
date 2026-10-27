# 27. The audit sequence

- **Covers:** every audit step from chapters 1 to 25 as one ordered checklist, each step
  with the tool that runs it and the chapter that gives its reasons.
- **Not here:** the reasons for each step → the chapter each step links to; what the
  vocabulary change states about the results → [ch. 28](28-vocab-pr.md); the audits of
  rules, exceptions and definitions → chapters [29](29-rules.md) to
  [31](31-definitions.md).
- **Assumes:** chapters [1](01-true-and-useful.md) to
  [25](25-default-or-enumerate.md).

Each step below is one question asked of a vocabulary change. A step names the tool
that answers it where one exists. Where no tool answers it, the step reads "review", and a
reviewer answers it from the diff and the KB.

The tools, all on the public API (`vaelii.core`):

| Tool | What it reads |
|---|---|
| `kb-integrity` | a set of candidate terms in one context; returns findings by category, stores nothing |
| `disjointness-audit` | every unordered pair of types visible from a context, each with a status |
| `kb-quality` | seven census readings over the knowledge: rules, extents, chains, taxonomy, declarations, subsumption, clashes |
| `direct-specs`, `direct-genls`, `genls` | one step or the whole closure of `genl` from a type |
| `all-specified-violations` | every *Specified* and *Exists* declaration visible in a context |
| `query`, `prove`, `ask?` | whether a sentence derives, and by which proof |
| `git grep` | the shipped files, the tests and the scripts |

`kb-integrity` runs only the categories its `:categories` option names. With no
`:categories` it runs every category except seven review-only ones (`:twin-genls`,
`:derivable-stated-edge`, `:disjoint-could-be-partition`, `:missing-arg`,
`:taxonomy-island`, `:rule-clash-review`, `:rule-macro-review`), so a full review runs the
sweep twice: once with no `:categories`, and once naming those seven.

## The order

**Practice.** Run the steps in the order below: the term's purpose first, then its
search, its block, its kind and its differentia, then its place, its separations, its
relations, and last its context and strength.

**Why.** Each part's steps read the results of the parts before it. A type whose
differentia fails (step 17) has no place to look for (step 20), and a type placed at the
wrong parent makes the disjointness steps report pairs that a better `genl` would settle
(**classify before you constrain**). A separation counted before the placement is fixed
is counted again after it. Running the steps out of order repeats work and reports
findings a later step removes.

**Why not the other ways.** Running only the tools skips the steps that have none: the
purpose, the differentia, the identity and the strength steps are review, and they decide
whether the term exists at all. Running only review misses what the tools compute over
the whole KB, such as the pairs a removed separation turns unknown.

**Audit.** The vocabulary change lists each step below with its result, or states
that the step does not apply and why ([ch. 28](28-vocab-pr.md)).

## Part I: what a KB is for

1. **no OE calligraphy**: for each modelling option, list what it lets the engine
   conclude and what it forbids; an option that is true and licenses nothing loses.
   Review; `kb-quality`'s `:rules :never` lists stored rules that never fired.
   → [ch. 1](01-true-and-useful.md)
2. **does it have rules?**: for a boundary question, list the facts and rules true of
   each side. A side with nothing of its own is not represented; two rich sides are two
   concepts. Review. → [ch. 1](01-true-and-useful.md)
3. **OE over code over text**: for each constraint the change adds in code or in prose,
   ask whether the KB could state it. Review of `git diff -- src/ docs/`.
   → [ch. 2](02-representation.md)
4. **represent the definition**: consider the new term's `seeAlso` and `termsRelated`
   partners; state each sentence of its comment as a fact or a rule where vaelii can,
   using `set/inertRule` for a rule that must not fire; run `kb-integrity` over the new
   terms. → [ch. 2](02-representation.md)
5. **bank the decision**: for each property, edge or declaration the change weighed and
   declined, the KB states its negation, a declined separation as `(orthogonal A B)`, and
   each `(not …)` stands for a decision someone made. `git grep -n '^(not \|^(orthogonal '`
   over the changed files. → [ch. 2](02-representation.md)
6. **truth, not provability**: record which expected conclusions derive, which exclusions
   have explicit support, and which cases stay open. A failure to derive is not a
   negative. `query` or `prove` of each expected conclusion. → [ch. 3](03-truth-not-provability.md)
7. **ontology over quirk**: a workaround that weakens the ontology for an engine
   limitation carries an explicit decision, and an engine bug that corrupts answers is
   reported, not worked around. Review. → [ch. 3](03-truth-not-provability.md)
8. **strongest form**: for every line, ask whether a more specific true fact entails it.
   Review; `kb-quality`'s `:declarations :typed-thing` lists the declarations that type
   a position `thing`. → [ch. 4](04-economy.md)
9. **DRY**: no thing is represented two ways at the vocabulary level; where two encodings
   must stay, explicit rules bridge them and a comment says why. Review and `git grep`.
   → [ch. 4](04-economy.md)
10. **state it once**: for every new `genl`, `disjoint` or `arg`, ask whether the rest of
    the KB entails it; drop it or mark which exception applies, and delete every comment
    clause a definitional assertion already states. `kb-integrity` `:derivable-stated-edge`,
    and `:rule-macro` for a stored rule that a declaration states.
    → [ch. 4](04-economy.md), [ch. 26](26-file-layout.md)

## Part II: minting a term

11. **look before you mint**: search the shipped files, every overlay and knowledge
    directory, setup and migration code, test fixtures, every branch, the live KB and
    the discussion history. `git grep -nw`, `git log --all -S`, and `find-sentexes` on
    the live KB. → [ch. 5](05-search-first.md)
12. **no naked terms**: the term ships with its metatype, `genl`, every `arg`, its
    separations or overlaps with siblings, its comment, and its relation properties and
    cross-references where they apply. `kb-integrity` `:missing-arg`,
    `:not-under-thing` and `:undeclared-arity`. → [ch. 6](06-definitional-block.md)
13. **meaning, not name**: the comment says what membership or the relation means, with
    examples, the hard ones included, and does not restate the name. Review.
    → [ch. 7](07-comments.md)
14. **references in seeAlso**: every pointer to another term is a `seeAlso` or
    `termsRelated` fact, not comment prose. Review. → [ch. 7](07-comments.md)
15. The spelling states the role: a type is snake_case and unary, a predicate camelCase
    of arity 2 or more, an individual CapitalCamel, a context `Cx…`. `assert` refuses a
    violation with `:type :naming`, and `check` reports it without storing. `kb-integrity` `:implicit-arity-class`
    reports a relation whose kind and arity force a class it lacks.
    → [ch. 8](08-kind-of-term.md)
16. **nesting values aren't individuals**: an enumeration of individuals that wants a
    hierarchy becomes predicates or collections. Review. → [ch. 8](08-kind-of-term.md)
17. **differentia from near-misses**: run the six-step refinement audit; a property is
    the differentia only if every member has it and no near-miss does. `direct-specs` of
    the parent lists the near-miss siblings. → [ch. 9](09-differentia.md)
18. **no teleology**: read the verb that defines membership; a process or agency verb
    brings purpose in, and a purpose-defined type becomes a role relation. Review.
    → [ch. 9](09-differentia.md)
19. **beware entity**: the differentia holds of the term's temporal and spatial slices and
    parts, or the comment says how they are treated. Review. → [ch. 9](09-differentia.md)

## Part III: placing a type

20. **tightest parent** and **walk down**: from the current parent, try each direct spec
    and tighten while every member is a member of the spec; a broad parent chosen
    because nothing closer exists is marked provisional. `direct-specs`.
    → [ch. 10](10-parent.md)
21. **broad under thing**: a new direct spec of `thing` is as broad as its siblings there, or it gains its
    missing intermediate parent. `direct-specs` of `thing`; `kb-integrity`
    `:not-under-thing` for a type with no path at all. → [ch. 10](10-parent.md)
22. **match the siblings**: compare the term with everything it is `disjoint` with and its
    `seeAlso` and `termsRelated` partners; an asymmetry is a finding or a comment.
    `kb-integrity` `:twin-genls`. → [ch. 11](11-siblings.md)
23. **factor out commonalities**: repeated `(A P)` plus `(B P)` with neither type below
    the other becomes an intersection; one type below the other is **strongest form**.
    Review; `:twin-genls`. → [ch. 11](11-siblings.md)
24. **what ends a member**: every `orthogonal` between kinds names a witness when one is
    known and says what ends it under each kind. `disjointness-audit`'s `:witness` on each `:orthogonal` pair,
    and review. → [ch. 12](12-identity.md)

## Part IV: separations and overlaps

25. **classify before you constrain**: for every `disjoint`, `arg` or `genlArg`, walk both
    terms up their `genl` chains; a constraint a better classification entails is a
    smell. `genls`; `:derivable-stated-edge`'s `:separated-by`. → [ch. 13](13-disjointness.md)
26. **partition over disjoint**: for every `disjoint`, look for a whole the parts cover.
    `kb-integrity` `:disjoint-could-be-partition`; `:implicit-genl` for an edge a cover
    forces. → [ch. 14](14-covers.md)
27. Every orthogonal declaration is checked against the separations stated over its pair.
    `kb-integrity` `:orthogonal-over-separation`. → [ch. 15](15-overlap.md)
28. **measure a removed separation**: state the disjoint and unknown pair counts before
    and after, and name each lost pair the change does not restate. `disjointness-audit`
    at both revisions; the `disjointness-coverage-ratchet` test fails a drop below its
    floor. → [ch. 16](16-unknowns.md)
29. **top unknowns**: list the five unknown pairs one decision would settle most of, each
    with a proposed decision. `disjointness-audit`'s `:pairs-data` with `:status :unknown`;
    the ranking is review. → [ch. 16](16-unknowns.md)

## Part V: predicates and relations

30. **different-type genl**: a predicate `genl` whose lower predicate's arguments are
    typed more broadly becomes a guarded rule. `kb-integrity` `:genl-arg-widening`.
    → [ch. 17](17-predicate-hierarchy.md)
31. Every argument is typed as tightly as the truth allows, and every position is typed.
    `:missing-arg`; `kb-quality`'s `:declarations` (`:stranded` and `:typed-thing`).
    → [ch. 18](18-argument-types.md)
32. Each relation property weighed and declined is banked as a negation (**bank the
    decision**). Review. → [ch. 19](19-relation-properties.md)
33. **event arg1**: for every relation with an argument typed `event` or a spec of it,
    the event is argument 1. A `query` over the `arg` declarations whose type `genls`
    places under `event`. → [ch. 20](20-events.md)
34. A *Specified* or *Exists* declaration audits clean, and a `transitiveInArg`
    declaration carries the direction its Cyc namesake carries. `all-specified-violations`;
    `kb-integrity` `:all-specified-violations`. → [ch. 21](21-claims-about-kinds.md)
35. **don't skip the predicate**: every function has its corresponding predicates, and a
    waiver is a named decision. `kb-integrity` `:uncorresponded-function` reports a
    function a held rule applies with no correspondence. → [ch. 22](22-functions.md)

## Part VI: contexts and strength

36. Author content sits in a context of its own, a theory in a middle context, and no
    shipped CxUniverse premise is edited. Review; [ch. 26](26-file-layout.md) for the file.
    → [ch. 23](23-contexts.md)
37. **catbus principle**: every default-strength separation with a monotonic copy in
    CxRealWorld names the fictional work and the member that justify it. `git grep -n
    'set/monotonic' resources/kb/middle/CxRealWorld.txt`, and review of each.
    → [ch. 24](24-strength.md)
38. **default or enumerate**: ask whether the default should reach a newly found, a
    hypothesized and a fictional member. These three are considerations, not a required
    check. Review. → [ch. 25](25-default-or-enumerate.md)

## One run of the tools

**Practice.** After the review steps, run the tools once over the change's new and
changed terms, in the context the terms are stated in.

**Example.** Two `kb-integrity` calls cover steps 4, 10, 12, 15, 21 to 23, 26, 27, 30, 31,
34 and 35. The first runs the default categories, and the second runs the seven
review-only ones:

```clojure
(v/kb-integrity kb new-terms 'CxUniverse)
(v/kb-integrity kb new-terms 'CxUniverse
                {:categories #{:twin-genls :derivable-stated-edge
                               :disjoint-could-be-partition :missing-arg
                               :taxonomy-island :rule-clash-review
                               :rule-macro-review}})
```

**Why.** The sweep stores and files nothing, so running it changes no belief.
`:status :audited` means no pass found anything; `:status :gap` names the non-empty
categories; `:status :truncated` means a bound ran out, and a truncated sweep is never
labelled audited. A review that reads `:gap` reads each category against the steps above.

**Why not the other ways.** The first call alone skips the seven review-only passes, so a
redundant edge, a missing `arg`, a cluster of types whose `genl` edges never reach the
root, or a rule clash left for review stays unreported. The second call alone runs only the seven it
names, so a widening `genl` or an orphaned type stays unreported.

**Audit.** The vocabulary change quotes the `:status` of the run and accounts for every
finding ([ch. 28](28-vocab-pr.md)).

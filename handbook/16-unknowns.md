# 16. Unknown pairs

- **Covers:** reading `disjointness-audit`; ranking the type pairs nobody has decided;
  measuring what a removed or narrowed separation gives up; `empty` and `nonempty`, and why
  the audit asks whether a shared subtype has a member.
- **Not here:** writing a separation → [ch. 13](13-disjointness.md),
  [ch. 14](14-covers.md); writing an overlap → [ch. 15](15-overlap.md); the order of the
  audit steps across a whole change → [ch. 27](27-audit-sequence.md); what a vocabulary
  change reports → [ch. 28](28-vocab-pr.md).
- **Assumes:** [ch. 13](13-disjointness.md), [ch. 14](14-covers.md),
  [ch. 15](15-overlap.md).

The disjointness audit classifies every unordered pair of types against the whole
hierarchy. A pair the KB has a decision for reads `:genl`, `:spec`, `:disjoint` or
`:orthogonal`. A pair with no decision reads `:unknown`. A pair with two contradictory
decisions reads `:inconsistent`. The `:unknown` pairs are the KB's open questions about
which kinds can share a member, and this chapter is about keeping that list short and
true.

## Reading the audit

**Practice.** Run `(v/disjointness-audit kb)` before and after a vocabulary change, and
read `:by-status` first, then the `:inconsistent` entries of `:pairs-data`, then the
`:unknown` ones.

**Example.** The call returns `{:types :pairs :by-status :pairs-data}`. Each entry of
`:pairs-data` carries `:a`, `:b`, the resolved `:status` and the raw `:statuses` set. An
entry whose statuses hold `:orthogonal` also carries `:witness`, one of `:declared`,
`:shared-instance`, `:shared-spec` or `:unwitnessed-spec`, and for the last three `:via`,
the instance or subtype found.

**Why.**

- *Engine.* The audit sweeps the types visible from its vantage context, `CxWell` by
  default, so a type only an opt-in theory such as `CxTra` holds is outside the sweep. A
  relation that a `genl` edge between relations names, such as `performedBy` under
  `doneBy`, is a node of the hierarchy and not a type, and the audit leaves it out.
- *Engine.* `genl?` reads the global closure, while the separations and the
  `:orthogonal` witnesses are read from the vantage. The shared-instance check is a
  facts-only query, so the sweep over every pair expands no rule. The audit writes
  nothing.
- *Maintenance.* An `:inconsistent` pair is a defect in the KB: the same pair is, say,
  genl-related and disjoint, or declared `orthogonal` beside a separation. Fix those before
  decision on unknowns, since a decision over an inconsistent region inherits the
  inconsistency.

**Why not the other ways.** Checking one pair at a time with `subsumption-status` answers
the question for that pair and says nothing about the pairs a decision would also settle.
The whole sweep is what shows where the open questions cluster.

**Audit.** The change states `:by-status` before and after, and lists every new
`:inconsistent` pair.

## top unknowns
*A disjointness audit always reports the top unknowns*

**Practice.** Beside the inconsistencies, report the five `:unknown` pairs whose decision
would settle the most other open pairs, each with a proposed decision: `disjoint`,
`orthogonal` with a witness, or a missing `genl`.

**Example.** For each `:unknown` pair `(a, b)`, count the `:unknown` pairs `(a′, b′)` with
`a′` in `(v/specs kb a 'CxWell)` and `b′` in `(v/specs kb b 'CxWell)`, read from the
audit's vantage. That count is the number of open
pairs a `(disjoint a b)` decision would settle. Rank the pairs by the count and propose a
decision for the top five. A proposed `orthogonal` settles one pair and needs a named
witness; a proposed `genl` moves `a` under a type whose separations already reach `b`
(**classify before you constrain**, [ch. 13](13-disjointness.md)).

**Why.**

- *Logical.* A separation is closed under `genl`. A decision that `a` and `b` are disjoint
  is a decision about every subtype of `a` against every subtype of `b`, so a decision high in
  the hierarchy settles many pairs at once.
- *Logical.* An overlap is not inherited ([ch. 15](15-overlap.md)), so an `orthogonal`
  decision settles its own pair alone. The ranking therefore favours the pairs where a
  separation is the candidate.
- *Maintenance.* Thousands of unknown pairs are too many to read. Five ranked pairs with a
  proposed decision are a list a reviewer can decide, and each decision shrinks the list
  the next audit produces.

**Why not the other ways.** An unranked list of unknowns spends review on leaf pairs that
one higher decision settles together. A count of unknowns with no pairs named gives a
reviewer nothing to decide.

**Audit.** The change lists its top five unknown pairs, the count each would settle, and
the proposed decision for each.

## measure a removed separation
*Measure a removed separation before shipping it*

**Practice.** Before removing or narrowing a `disjoint`, `partition` or `separating`, run
`disjointness-audit` before and after. List the pairs that turn `:unknown`, and restate at
the tightest true level each separation among them that still holds.

**Example.** `abstract.txt` states `(set/monotonic (disjoint mechanism organism))`, and
the comment beside it says that the separation reaches `machine`, `electronic_device` and
every kind below them. Removing it turns `:unknown` every pair of a kind below `mechanism`
with a kind below `organism` that no other separation divides, `machine × dog` among them.
The pair counts before and after show the size of the loss. A removal made because a
witness overlaps two particular kinds is restated as the narrower separations that
remain true.

**Why.**

- *Logical.* A separation reaches far below the pair it names. The pairs it settles are
  every subtype of one side against every subtype of the other, and its removal reopens
  all of them.
- *Engine.* `disjointness_audit_test`'s `disjointness-coverage-ratchet` holds the starter
  KB's audit at its current values: a floor on the `:disjoint` pair count, a floor on the
  disjoint fraction, and a ceiling on the unknown fraction. A removed separation lowers all
  three. A type added in the same change whose pairs are mostly `:disjoint` raises the
  disjoint fraction, so the count floor catches a removal the two fractions pass. Lowering
  a floor is the change that names the pairs given up.
- *Maintenance.* A removal made to fix one pair silently reopens hundreds of unrelated
  ones, and nothing else in the KB reports them. The before-and-after counts make the loss
  visible at review.

**Why not the other ways.** Removing the separation and fixing the one witness that
prompted the removal leaves every other reopened pair `:unknown` with no decision.
Weakening a separation to `:default` does not reopen any pair, because `disjoint` is
forced-monotonic and holds at either strength ([ch. 24](24-strength.md)).

*In development:* `disjoint` as a forced-monotonic predicate is in development
([ch. 24](24-strength.md#the-forced-monotonic-set)).

**Audit.** The change states the `:disjoint` and `:unknown` pair counts before and after,
and names the lost pairs it does not restate.

## empty and nonempty

**Practice.** State `(nonempty T)` for a type known to have a member, in the context where
it has one. State `(empty T)` only for a type that has no member in the context it is
stated in. Do not count a shared subtype as evidence of overlap unless the subtype is
known to be nonempty.

**Example.** `core.txt` partitions the unary predicates by emptiness and carries each
half along `genl` in the direction that is true by the definition of `genl`:

```clojure
(set/monotonic (partition unary_predicate empty nonempty))
(set/monotonic (transitiveInArgInverse empty 1 genl))
(set/monotonic (transitiveInArg nonempty 1 genl))
(set/forwardRule (implies (and (disjoint ?type ?type) (unary ?type))
                          (empty ?type)))
```

The `comment` on `empty` says that an empty claim holds for the context it is stated in:
`(empty hobbit)` holds in a context about the actual world, and `(nonempty hobbit)` in a
context about Middle-earth during a period when hobbits exist.

**Why.**

- *Logical.* `(disjoint c c)` holds exactly when `c` has no instance, so an empty type is
  disjoint from everything, itself included. An empty type is also a subtype of every
  type. A shared subtype of `a` and `b` therefore shows an overlap only when it has a
  member.
- *Engine.* The forward rule concludes `(empty c)` for a type below two separated types,
  which the separation check reads as separated from itself. A stated `(disjoint c c)` is
  refused by `wff`. Emptiness descends `genl` and nonemptiness climbs it through the two
  preservation declarations.
- *Engine.* `disjointness-audit` reads a shared subtype with a known `(nonempty c)` as a
  `:shared-spec` witness. A shared subtype not provably empty and not known nonempty still
  reads `:orthogonal`, marked `:unwitnessed-spec`: the two types can overlap and the KB
  names no instance in the overlap. A pair whose only shared subtypes are provably empty
  stays `:unknown`.
- *Maintenance.* One type stated both `empty` and `nonempty` in contexts one reader sees is
  a disjointness clash through the partition, so a contradiction about emptiness is
  reported like any other.

**Why not the other ways.** Without emptiness named, an empty shared subtype would count as
an overlap witness, and the audit would report two disjoint types as overlapping. A
`(nonempty T)` stated in `CxUniverse` for a kind that exists only in some worlds claims
the kind has members in every context; the claim belongs to a context bounded to the world
and time where it holds.

**Audit.** For each `:unwitnessed-spec` entry, either state `(nonempty c)` for the shared
subtype in the context where it has a member, or name an instance of both types.

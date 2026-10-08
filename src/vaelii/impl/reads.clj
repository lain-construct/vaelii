;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.reads
  "The named entry points onto the index — a read **as stored**, or a read **as believed**.

  The fourth invariant is that a stored sentex is not a believed one (README.md, \"The
  model in one page\").  Every `IndexStore` posting is storage: it holds a defeated
  default, a conclusion whose support was withdrawn and a spelling an equality retired,
  because all three are revivable and the index is not where belief lives.  So a caller
  reading a posting has a question to answer, and until it is asked in the name of the
  read nothing distinguishes the caller that answered it from the one that forgot.

  This namespace is where it is asked.  Every raw `vaelii.impl.protocols` index read
  outside a short roster of implementers goes through an entry point here, and the entry point's own
  name says which answer it gives — `lein lint`'s **E16** is what keeps that true, and
  its roster is the one place the exceptions are written down.

  ## The two entry points, and why they take different arguments

  - **`as-stored-…` takes the index store.**  An as-stored read *is* an index
    operation, so the entry point's arglist is the protocol method's and nothing else is in
    scope.  A caller reaching one is saying it wants storage: a candidate set it filters
    itself, a roster that must over-approximate, a diagnostic that reports what is
    written.  Each entry point below says what a stored-but-disbelieved answer is *for*.
  - **`believed-…` takes the KB.**  Belief lives in the JTMS, so a believed read is a
    question about the KB and not about the index — which is exactly the distinction the
    arglists carry.  The filter is `jtms/in?`, which already drops a **superseded**
    spelling along with a defeated one (`vaelii.impl.jtms`'s `-in?`), so a believed entry point
    means what `kb/sentexes-matching` means for the handles it yields.

  An entry point is a **wrapper and never a rewrite**: one call to the protocol method it names,
  the same laziness, the same count-aware path.  It adds no index operation, which is
  what keeps `assert_cost_test` reading the same numbers on either side of one.

  ## Where there is only one entry point, and why

  - **The cardinalities** (`stored-count-…`) count a posting set's members.  Belief is
    not in the index, so there is no O(1) believed count and this namespace does not
    pretend otherwise — a believed count is `(count (believed-… …))` and is O(n).  The
    public readers state the same thing (`vaelii.core/count-with-functor`).
  - **The vocabulary** (`stored-terms`, `stored-term-count`) is the roster of names the
    term index is keyed by.  A name enters with the first sentex mentioning it and leaves
    with the last, so it answers *what this KB talks about* — a question defeat does not
    change.
  - **The watched-rule roster** (`watched-rule?`, `watched-rules`, `watched-rules-on`)
    answers \"which rules might need re-checking\", never \"does the exception hold\", and
    stores no truth value at all (`protocols/IndexStore`).  Filtering it by belief would
    narrow a re-check queue, and a missed re-check is a wrong belief where an extra one
    is a query nobody needed.

  ## Two belief questions this namespace does not answer

  - **A rule's** belief is `resolution/rule-believed?` and not `jtms/in?`: a sentex the
    TMS holds no node for is *available* rather than disbelieved, which is an arm a plain
    membership test does not have.  So `as-stored-rules-by-antecedent` and its consequent
    twin have no believed sibling here, and a chainer asks `res/rule-believed?` of each
    handle it means to fire.
  - **`resolution/*belief-blind*`** is not read here.  It is a named opt-out scoped to
    the retrieval entry point that resolves `CxEverything`, and no caller of these entry points is on
    that path — an entry point that consulted it would extend the opt-out to reads nobody granted
    it to."
  (:require [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kv :as kv]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- extents: the trie and the secondary roots ---------------------------

(defn as-stored-in-context
  "Handles stored in `context` — its whole extent, rules included, belief unread.

  A stored-but-disbelieved answer is what a caller wants here when it is about the
  *contents* of a context rather than about what holds in it: a teardown that must remove
  every record it finds, an ancestor set sweep that fetches each record and decides on the record,
  a level-1 diagnostic reporting what the root holds."
  [index context]
  (p/sentexes-in-context index context))

(defn as-stored-with-functor
  "Handles of fact sentexes whose functor is `pred`, any arity, either polarity — belief
  unread.

  The candidate-set read: a caller narrowing by predicate almost always fetches each
  record and decides on its polarity, its context and its belief together, and doing so
  one handle at a time is cheaper than two passes over the same set.  A caller whose
  filter is belief alone takes `believed-with-functor` instead."
  [index pred]
  (p/sentexes-with-functor index pred))

(defn as-stored-with-arg
  "Handles of fact sentexes holding `term` at 1-based argument `pos` — belief unread.

  The argument root is scoped by predicate, so this is the narrow read a pattern pinning
  an argument after a variable wants.  Same shape as `as-stored-with-functor`: a
  candidate set whose consumer decides per record."
  [index pos term]
  (p/sentexes-with-arg index pos term))

(defn as-stored-with-args
  "Handles with functor `pred` AND each `[pos term]` of `pos-terms`, belief unread:
  the intersection of `pred`'s argument-root nodes at the named positions, or the
  predicate extent when `pos-terms` is empty.  `pred` may be nil, for a
  variable-functor pattern."
  [index pred pos-terms]
  (p/sentexes-with-args index pred pos-terms))

(defn as-stored-predicates-at-arg
  "The predicates holding a **stored** fact, either polarity, with `term` at argument `pos`
  — the slot roster's entry, no handle read and no belief consulted — or nil for an index
  store that keeps no roster this can reach (`kv/slot-predicates`).

  A roster read rather than a posting read, so it names predicates where the other
  entry points here name handles.  A predicate enters with its first stored fact at the
  slot and leaves with its last, so a defeated claim keeps it listed: the answer is for a
  caller that must over-approximate which predicates a term could be claimed under."
  [index pos term]
  (kv/slot-predicates index pos term))

(defn as-stored-with-term
  "Handles the inverted term index keys by `term` — belief unread.

  Exact for a symbol; for a compound outside the indexed depth bounds it holds only the
  sentexes that nest it deep enough, so `kb/find-sentexes` is the exact read for one.  The
  postings are a candidate set in both cases: a term appears in a sentence the reader then
  has to look at."
  [index term]
  (p/sentexes-with-term index term))

(defn as-stored-with-terms
  "Handles the inverted term index keys by every one of `terms`, one intersection — belief
  unread.  A candidate set, as `as-stored-with-term`'s is."
  [index terms]
  (p/sentexes-with-terms index terms))

(defn as-stored-at-path
  "Handles whose trie path matches `pattern` — one walk, no records fetched, nothing
  interpreted.  A variable token in the path is a wildcard that fans over every child.

  The rawest read the index has.  Level 0 of `vaelii.impl.levels` addresses the trie
  directly and interprets neither belief nor polarity, which is what makes it the floor
  the other levels are measured against, and `vaelii.impl.decide` reads one exact
  sentence under every context to find a stored converse."
  [index pattern]
  (p/lookup index pattern))

(defn believed-with-functor
  "Handles of fact sentexes with functor `pred` that the KB **believes** — the extent
  above, filtered by `jtms/in?`.

  Lazy, as the posting read is: the filter is applied as the seq is walked, so a consumer
  taking a prefix pays a TMS probe per handle it takes and not per handle in the root.  A
  superseded spelling drops out with a defeated one, since that is what `in?` answers."
  [kb pred]
  (let [tms (reasoning/tms kb)]
    (filter #(jtms/in? tms %) (p/sentexes-with-functor (:index kb) pred))))

(defn believed-with-args
  "Handles with functor `pred` AND each `[pos term]` of `pos-terms` that the KB
  **believes** — `as-stored-with-args` filtered by `jtms/in?`, lazily.

  The narrowing read's believed entry point: a caller that knows several of a sentence's terms
  and wants only what holds asks here rather than intersecting and then filtering by
  hand."
  [kb pred pos-terms]
  (let [tms (reasoning/tms kb)]
    (filter #(jtms/in? tms %) (p/sentexes-with-args (:index kb) pred pos-terms))))

;; ---- cardinalities: a posting set's size, and never its members -----------

(defn stored-count-in-context
  "How many sentexes are **stored** in `context` — one set-size read, O(1), nothing
  fetched and no belief consulted.  A defeated default still occupies its context."
  [index context]
  (p/count-in-context index context))

(defn stored-count-with-functor
  "How many fact sentexes are **stored** with functor `pred` — one set-size read, O(1).

  The gate in front of nearly every definitional check in the engine: a KB that declares
  none of a feature's predicates pays one integer read and stops, which is what keeps an
  unused feature off the assert path."
  [index pred]
  (p/count-with-functor index pred))

(defn stored-count-with-arg
  "How many fact sentexes **store** `term` at argument position `pos` — one O(1) set-size
  read per predicate declaring an argument at that slot, since the argument roots are
  scoped by predicate."
  [index pos term]
  (p/count-with-arg index pos term))

(defn stored-count-at
  "How many sentexes are **stored** under trie prefix `prefix` — the count-aware trie's
  own tally, no walk.  `[]` is the whole KB."
  [index prefix]
  (p/count-at index prefix))

(defn stored-count-children
  "How many child tokens sit under interior prefix `prefix` — the trie's distinct-value
  count at a position, answered without building the child set.

  What the planner's cost model divides by, so it must not scale with the KB:
  `(count (stored-children …))` would, and this does not."
  [index prefix]
  (p/count-children index prefix))

;; ---- the bodies stored in both polarities ----------------------------------

;; The opposed family (`kv/opposed-adds`) holds a body while a `(not B)` and a `B` are both
;; stored, in any contexts, and its members are the handles of both polarities.  A
;; negation nogood needs a body stored both ways, and a stored-but-disbelieved member
;; still forms one: the placement reads each member's belief itself.

(defn stores-opposed?
  "Is any body **stored** in both polarities?  One count read, belief unread."
  [index]
  (pos? (long (or (kv/opposed-count index) 0))))

(defn stored-opposed?
  "Is `body` **stored** in both polarities?  One membership read, belief unread."
  [index body]
  (boolean (kv/opposed-body? index (sx/canon body))))

(defn as-stored-opposed-bodies
  "Every body **stored** in both polarities, as a set."
  [index]
  (or (kv/opposed-bodies index) #{}))

(defn as-stored-opposed-members
  "The handles of `body`'s facts of both polarities while it is **stored** in both, in
  every context, belief unread; empty when it is not."
  [index body]
  (or (kv/opposed-members index (sx/canon body)) #{}))

(defn as-stored-opposed-in
  "The handles of the facts of every body **stored** in both polarities that are stated
  in a context of `contexts`, belief unread: |contexts| leaf reads."
  [index contexts]
  (or (kv/opposed-in index contexts) #{}))

;; ---- the shape roster, the terms of two unary predicates, the self tuples ----

(defn as-stored-self-tuples
  "The handles of the **stored** ground positive binary self tuples `(f a a)` of functor
  `f` stated in a context of `contexts` (every context when nil), belief unread
  (`kv/self-tuples`)."
  [index f contexts]
  (or (kv/self-tuples index f contexts) #{}))

(defn as-stored-shape-lengths
  "The lengths the positive facts of functor `f` are **stored** at, as a set, belief
  unread: one roster read (`kv/shape-lengths`).  A length leaves with its last fact."
  [index f]
  (or (kv/shape-lengths index f) #{}))

(defn as-stored-unary-multi-terms
  "The terms the unary roster lists two or more predicates of, as a set, belief unread
  (`kv/unary-multi-terms`): a superset of the terms holding two **stored** memberships."
  [index]
  (or (kv/unary-multi-terms index) #{}))

;; ---- the stored excepts and defeats ----------------------------------------
;; A positive `(except (sentexHandle H))` keys in the trie as `[except m sentexHandle H
;; ctx]`, `m` the arity marker of the handle term, so the level above the context answers
;; by target and in either polarity's place only the positive one is read: a `(not …)`
;; keys under `[:false …]`.  `defeat` keys the same way.

(def ^:private handle-mark (sx/subterm-mark 2))

(defn- naming-prefix
  "The trie prefix of the positive `(functor (sentexHandle h))` facts, one level above
  their contexts; with no `h`, the level whose children are the handles named."
  ([functor] [functor handle-mark sx/sentex-handle-functor])
  ([functor h] [functor handle-mark sx/sentex-handle-functor (long h)]))

(defn stores-any?
  "Is a positive `(functor …)` fact **stored** in any context?  One count read on the
  trie's `[functor]`, belief unread."
  [index functor]
  (pos? (p/count-at index [functor])))

(defn stores-in?
  "Does a context of `contexts` **store** a fact of functor `pred`, either polarity?  The
  predicate extent's children intersected with `contexts`, no leaf read
  (`kv/extent-contexts`), belief unread."
  [index pred contexts]
  (boolean (seq (or (kv/extent-contexts index pred contexts)
                    (p/sentexes-with-args index pred [] contexts)))))

(defn stored-naming?
  "Is a positive `(functor (sentexHandle h))` **stored** in any context?  One count read."
  [index functor h]
  (pos? (p/count-at index (naming-prefix functor h))))

(defn as-stored-named
  "The handles the positive `(functor (sentexHandle H))` facts **stored** in any context
  name, as a set: the children of the trie's `[functor m sentexHandle]` level.  Where the
  trie is a `KvIndexStore`'s the set is the one the backend holds (`kv/children-held`), so
  two reads with no write between them answer one object on the map backends."
  [index functor]
  (let [pre (naming-prefix functor)]
    (or (kv/children-held index pre) (set (p/children index pre)))))

(defn as-stored-naming-by-context
  "The positive `(functor (sentexHandle h))` facts **stored**, as one `[context handles]`
  pair per context stating one: the children under the prefix and the leaf under each."
  [index functor h]
  (let [pre (naming-prefix functor h)]
    (keep (fn [c] (let [hs (p/leaf-at index (conj pre c))] (when (seq hs) [c hs])))
          (p/children index pre))))

(defn as-stored-naming
  "The handles of the positive `(functor (sentexHandle h))` facts **stored** in a context
  of `contexts` (every context when nil), as a vector, or nil when there is none.  The
  children under the prefix are filtered by `contexts` before a leaf is read, so a context
  outside `contexts` costs a membership test."
  ([index functor h] (as-stored-naming index functor h nil))
  ([index functor h contexts]
   (let [pre (naming-prefix functor h)]
     (not-empty (into [] (comp (filter #(or (nil? contexts) (contains? contexts %)))
                               (mapcat #(p/leaf-at index (conj pre %))))
                      (p/children index pre))))))

;; ---- the vocabulary roster -----------------------------------------------

(defn stored-terms
  "Every symbol term the index is keyed by — the KB's vocabulary, unordered.

  A name is in this roster while some **stored** sentex mentions it, so it answers what
  the KB talks about rather than what it currently holds: defeating the one fact about a
  term does not unname the term."
  [index]
  (p/terms index))

(defn stored-term-count
  "How many distinct symbol terms the index is keyed by — the roster's own count, no
  walk over it."
  [index]
  (p/term-count index))

;; ---- the rule indexes ----------------------------------------------------

(defn as-stored-rules-by-antecedent
  "Handles of rules with an antecedent on `pred` — every rule, whatever its direction,
  belief unread.

  Belief for a **rule** is `resolution/rule-believed?` and not `jtms/in?`, which is why
  there is no believed entry point beside this one: a rule the TMS holds no node for is available
  rather than disbelieved, and a chainer asks that question of each handle it means to
  fire."
  [index pred]
  (p/rules-by-antecedent index pred))

(defn as-stored-rules-by-consequent
  "Handles of rules concluding `pred` — every rule, whatever its direction, belief unread.

  `resolution/rule-believed?` is the belief question, as for the antecedent entry point above.  A
  rule whose consequent functor is a variable files under `protocols/var-consequent-key`
  rather than under a canonical `?var0`, so a concrete goal's answer is this bucket
  unioned with that catch-all (`resolution/concluding-rule-handles`)."
  [index pred]
  (p/rules-by-consequent index pred))

(defn as-stored-rule-keys
  "The antecedent keys some **stored** rule takes (`rules/antecedent-key`), as a set: the
  root level of the `:rule-antecedent` trie (`kv/rule-keys`)."
  [index]
  (or (kv/rule-keys index) #{}))

(defn stored-rule-key?
  "Does a **stored** rule take the antecedent key `k`?  One membership test."
  [index k]
  (boolean (kv/rule-key? index k)))

(defn as-stored-rules-in
  "Handles of the **stored** rules of `kind` stated in one of `contexts` (every context
  when nil): `:rule` for every rule, `:solve` for the rules a solve reads
  (`rules/solve-sentex?`).  The rule extent ends in the context, so this costs
  min(|contexts stating one|, |contexts|) probes plus a leaf read per context kept."
  [index kind contexts]
  (or (kv/rule-extent index kind contexts) #{}))

(defn stores-rule-in?
  "Does a context of `contexts` **store** a rule?  The rule extent's children intersected
  with `contexts`, no leaf read."
  [index contexts]
  (boolean (seq (kv/rule-extent-contexts index :rule contexts))))

;; ---- the mint family ------------------------------------------------------
;; The records a **stored** argument-declaration justification concludes
;; (`special/post-mint!`), read by the settle's mint withdrawal.  A mint is a fact about a
;; stored justification and not about belief: a blocked or OUT mint stays filed, and the
;; withdrawal asks each candidate's belief itself (`special/withdrawable-mint`).

(defn stored-mint-count
  "How many records are filed as mints.  One count read."
  [index]
  (long (or (kv/mint-count index) 0)))

(defn as-stored-mint-terms
  "The terms some filed mint is about, as a set."
  [index]
  (or (kv/mint-terms index) #{}))

(defn stored-mint-term-count
  "How many terms some filed mint is about.  One count read."
  [index]
  (long (or (kv/mint-term-count index) 0)))

(defn stored-mint-term?
  "Is some filed mint about `term`?  One membership test."
  [index term]
  (boolean (kv/mint-term? index term)))

(defn as-stored-mints-about
  "Handles of the mints filed about `term`, in every context."
  [index term]
  (or (kv/mints-about index term) #{}))

(defn stored-mint?
  "Is record `h` filed as a mint about `term` in context `c`?  One membership test."
  [index term c h]
  (boolean (kv/mint-filed? index term c h)))

(defn as-stored-mint-contexts
  "The contexts some filed mint is stored in, as a set."
  [index]
  (or (kv/mint-contexts index) #{}))

(defn stored-mint-context-count
  "How many contexts some filed mint is stored in.  One count read."
  [index]
  (long (or (kv/mint-context-count index) 0)))

(defn as-stored-mints-in
  "Handles of the mints filed in context `c`.  One leaf read."
  [index c]
  (or (kv/mints-in index c) #{}))

;; ---- the watched-rule (exception re-check) roster -------------------------

(defn watched-rule?
  "Is `handle` in the exception/watched-rule roster — O(1) membership, the firing-path
  gate.

  The roster stores no truth value, so there is no second entry point: it answers which rules
  carry an `exceptWhen` at all, never whether one holds.  Whether the exception *fires* is
  `provers/exceptions-block?`, and whether the rule itself is believed is
  `resolution/rule-believed?`."
  [index handle]
  (p/exception-rule? index handle))

(defn watched-rules
  "Handles of every rule carrying a re-check condition — an exception, an `(unknown S)`
  antecedent, an aggregate, a closed-extent negative or a `different` antecedent
  (`rules/rechecked?`).

  Read to **queue re-checks**, which is why belief is not filtered: over-queueing costs a
  query at the next settle and under-queueing leaves a conclusion standing on evidence
  that has moved.  A trigger is conservative in the direction the answer is."
  [index]
  (p/exception-rules index))

(defn watched-rules-on
  "Handles of rules whose re-check condition mentions `pred` — the predicate-scoped slice
  of `watched-rules`, and unfiltered for its reason."
  [index pred]
  (p/rules-with-exception-on index pred))

;; ---- reads scoped to the contexts a reader sees ---------------------------

(defn as-stored-with-functor-in
  "`as-stored-with-functor` restricted to the facts stated in one of `contexts` — a
  reader's ancestor set, or nil for every context.  The predicate extent ends in the
  context, so this costs min(|contexts stating one|, |contexts|) membership probes plus
  one leaf read per context kept (docs/indexing.md, \"By-context reads\")."
  [index pred contexts]
  (p/sentexes-with-args index pred [] contexts))

(defn as-stored-contexts-with-functor
  "`[seen n]`: the contexts of the set `contexts` (every context when nil) in which a fact
  with functor `pred` is **stored**, either polarity, and how many contexts state one — the
  predicate extent's children, no handle read and no belief consulted — or nil for an
  index store that keeps no extent this can reach (`kv/extent-census`).  Costs one count
  read, then min(|contexts stating one|, |contexts|) membership probes when it is not
  zero.  A defeated fact keeps its context listed, so the answer is for a caller that must
  over-approximate where `pred` is stated."
  [index pred contexts]
  (kv/extent-census index pred contexts))

(defn stored-count-with-functor-in
  "How many facts with functor `pred` are **stored** in the contexts of `contexts`: one
  leaf count per context stating one, or nil where `as-stored-contexts-with-functor` is
  nil."
  [index pred contexts]
  (kv/extent-count-in index pred contexts))

(defn stored-count-with-arg-in
  "How many facts with functor `pred` and `term` at argument `pos` are **stored** in the
  contexts of `contexts`: one leaf count per context the argument node lists and
  `contexts` holds, or nil where `as-stored-contexts-with-functor` is nil."
  [index pred pos term contexts]
  (kv/arg-count-in index pred pos term contexts))

(defn stored-census-with-arg
  "`[n k]`: how many facts with functor `pred` and `term` at argument `pos` are **stored**,
  in every context, and in how many contexts, or nil where
  `as-stored-contexts-with-functor` is nil.  Two count reads."
  [index pred pos term]
  (kv/arg-census index pred pos term))

;; ---- the taxonomy's supporter families -------------------------------------

(defn as-stored-supporters
  "The **stored** supporters of taxonomy key `k` (`[:genl a b]`, `[:genlCx a b]` or a
  flat-cache key) as `{handle ctx}`, belief unread (`kv/supporters`): the taxonomy decides
  an entry's belief from them, and a disbelieved supporter stays listed so that its revival
  can bring the entry back.  `{}` for an index store this finds no roots store in."
  [index k]
  (or (kv/supporters index k) {}))

(defn stored-supporter-count
  "How many **stored** handles support taxonomy key `k`: one count read."
  [index k]
  (or (kv/supporter-count index k) 0))

(defn as-stored-installed-keys
  "The taxonomy keys **stored** handle `h` installs, as a set, belief unread: the keys a
  reconcile re-examines when `h`'s label moves.  One read."
  [index h]
  (or (kv/installed-keys index h) #{}))

(defn as-stored-supporter-map
  "Every taxonomy key with a **stored** supporter, as `{k {handle ctx}}`, by a walk of the
  whole store (`kv/all-supporters`): a raw taxonomy's reads, whose private store holds the
  supporter families and nothing else."
  [index]
  (or (kv/all-supporters index) {}))

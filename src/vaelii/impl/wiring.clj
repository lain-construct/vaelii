(ns vaelii.impl.wiring
  "The write path and the prover registry as the layers *beneath* them see it — the whole
  inventory of calls the require graph cannot express, in one file.

  Everything else in the engine is layered, and every edge is a static require the
  compiler checks: kb <- checks <- special <- integrate <- chain <- settle <- vaelii.core.
  Exactly two calls run the other way:

    `assert-sentence` — the full assertion path, called from `vaelii.impl.nat` (a reified
    NAT stores its `(termOfUnit K E)` map and its materialized types) and from
    `vaelii.impl.skolem` (a firing mints its witness).  Storing is a *whole* assert —
    naming, the definitional checks, the index, chaining, settle — so the write path runs
    chaining, and chaining calls back here to mint a constant (docs/skolem.md).

    `solve-goal` — the prover registry, called from `vaelii.impl.resolution` to discharge
    a deferred antecedent (`different` / `evaluate` / `unknown`).  Backward chaining is a
    leaf the registry dispatches to, and `unknown` runs the registry back over its own
    argument, so negation-as-failure is mutually recursive with the chainer that asked
    for it (docs/naf.md).

  Both are genuine mutual recursion: the cycle is in the **behaviour**, neither is a
  misplaced function, and no arrangement of the code removes either.  Why they are
  gathered here rather than left at their call sites, what `lein lint`'s **E8** enforces,
  and why each is a `delay` rather than a dynamic var — docs/namespaces.md, \"The
  layering\"."
  (:refer-clojure :exclude [assert]))

;; ---- the write-path mode flag --------------------------------------------
;; It lives here rather than with the write path because both sides of the recursion read
;; it: `vaelii.core`'s assert decides whether to settle by it, and `skolem` binds it around
;; a mint to say "not now — I am inside the fixpoint you are about to settle".  Down here
;; both can see it without either naming the other.

(def ^:dynamic *defer-settle?*
  "When true, the assert path does **not** `settle` after storing — belief is left
  un-reconciled for the caller to settle once, later.  Two callers bind it:

  - a rule firing minting a skolem NAT mid-fixpoint (`vaelii.impl.skolem`): the nested
    `(termOfUnit K E)` assert is monotonic bookkeeping and the enclosing firing settles
    once when it finishes, so settling per mint would be redundant churn — and worse,
    would relabel belief inside the running chain (docs/skolem.md);
  - `with-deferred-settle` / `assert-many`, which run a whole batch of asserts under it
    and settle once at the end, so a bulk load pays one belief reconciliation instead of
    N.  Chaining still runs per assert (only the `settle` is deferred), so the final
    settle sees the same stored state a per-assert settle would have, and order
    independence guarantees the same beliefs.

  Retraction settles eagerly regardless — reviving a defeated default is not part of an
  assert batch."
  false)

;; ---- the two cuts ---------------------------------------------------------

(def ^:private core-assert
  (delay (requiring-resolve 'vaelii.core/assert)))

(def ^:private provers-solve-goal
  (delay (requiring-resolve 'vaelii.impl.provers/solve-goal)))

(defn assert-sentence
  "`vaelii.core/assert` — store `sentence` in `context` under `opts`, returning its handle.
  See the namespace docstring for why this is not a require."
  [kb sentence context opts]
  (@core-assert kb sentence context opts))

(defn solve-goal
  "`vaelii.impl.provers/solve-goal` — the registry's raw solution bindings for `goal` in
  `context`.  See the namespace docstring for why this is not a require."
  [kb goal context]
  (@provers-solve-goal kb goal context))

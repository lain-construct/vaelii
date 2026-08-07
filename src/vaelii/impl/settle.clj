;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.settle
  "Belief settling: relabel the TMS, resolve soft contradictions on the one axis
  (defeat-class), report the represented dilemmas, and run the `exceptWhen`
  re-check queue to a joint fixpoint with belief.

  Top engine layer (kb <- checks <- special <- integrate <- chain <- settle <-
  vaelii.core): settling reads believed content (kb), garbage-collects what a newly
  blocked justification was supporting (integrate's removal choke point tears it
  down), and re-derives what a released exception was suppressing (chain fires it
  again)."
  (:require [clojure.set :as set]
            [taoensso.trove :as trove]
            [vaelii.impl.chain :as chain]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.feed :as feed]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.integrate :as integrate]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.kb :as kb]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.solve :as solve]
            [vaelii.impl.special :as special]
            [vaelii.impl.strength :as strength]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.violations :as violations]))

;; ---- belief settling: soft, prioritized contradictions ------------------
;; After chaining, `settle` relabels the TMS and resolves contradictions.  A
;; contradiction is a *nogood* — a set of believed sentexes that cannot all hold.
;; Today the nogoods are S vs (not S) pairs; disjointness/functional remain hard
;; constraints (see assert).  Resolution never throws:
;;   * different defeat-class      -> defeat the weaker (no solver needed)
;;   * a :default/:default tie      -> a dilemma; both sides stay believed, and the
;;                                     pair is reported by `contradictions`
;;   * an irreducible :monotonic clash -> report it (the "solve result")

(def ^:dynamic *incremental-negations*
  "Memoize the P/¬P pairing **per opposed body** — the default, and what a KB runs.

  Incremental pairing is one narrowing of an exhaustive question, *which believed
  negations pair with which believed positives*: only the opposed bodies this settle
  could have moved are re-derived (`moved-bodies`), and every other body's answer is
  carried forward from the last settle verbatim.  It is a claim that what it skips could
  not have changed the answer — and a wrong one is a silently *different* answer, never a
  crash: a dilemma that goes unreported, or a defeat that is not applied.

  Bound to `false`, every opposed body is re-derived on every call and nothing is carried,
  which is the definition the narrowing approximates.  That is the reference
  `negation_oracle_test` proves it against, and it is O(standing contradictions) belief
  queries per settle *round* — a measurement harness, not a mode to run a KB in.  The
  separation is 12x on `lein perf`'s `negation-arbitration`."
  true)

(defn- body-nogoods
  "The nogoods one opposed body currently yields: every believed `(not body)` paired with
  every believed `body` whose two contexts have a non-empty common down-closure.

  Belief-filtered, so a body whose positive side is currently defeated yields nothing and
  leaves the memo — which is what makes revival work rather than something to compensate
  for.  Reviving is a relabel (`clear-defeats!`), the relabel puts the handle in the
  settle's moved region, and the region is what asks for this body again.

  Read **as stored** rather than through `query`, because this is an iteration over the
  engine's own coincidence set and not a question about the world.  `query` rewrites a
  goal to its class representative, so a body an equality has since retired would hand
  back the representative's sentexes and be reported under the retired spelling — one pair
  reported twice, under two names, one of them naming content nothing believes.  A
  superseded body answers nothing here, which is the correct reading of a spelling that
  has been restated (docs/equality.md)."
  [kb body share-a-view?]
  (let [tms (:tms kb)]
    (into #{}
          (for [nx (kb/sentexes-matching-as-stored kb (list 'not body) '?ctx) ; believed (not body)
                :let [ctxN (:context nx)]
                sx (kb/sentexes-matching-as-stored kb body '?ctx)             ; believed body
                :let [ctxX (:context sx)]
                :when (and (not= (:id sx) (:id nx))
                           (share-a-view? ctxN ctxX))]
            (let [p (max (strength/rank-of (jtms/defeat-class tms (:id nx)))
                         (strength/rank-of (jtms/defeat-class tms (:id sx))))]
              {:nogood #{(:id nx) (:id sx)} :priority p
               :sentence (list 'contradicts body (:sentence nx))})))))

(defn- moved-bodies
  "Which opposed bodies this settle could have changed the pairing of — the memo's
  invalidation set, and the whole of it.

  Two inputs, and neither subsumes the other:

  - **the relabelled region** — `jtms/touched`, a superset of every handle whose belief
    flipped.  It covers an *arrival* (a stored premise is relabelled as it lands) and it
    is the only thing that covers a belief change with no store behind it at all: a
    second justification arriving from a `:monotonic` premise lifts a derived
    conclusion's defeat class, which moves a standing pair's `:priority` while nothing is
    written about either side of it.  A touched handle names its body through the record.
  - **`:dirty`** — the bodies a store or a removal posted since the last settle drained it
    (`kb/note-opposed!`).  What only this covers is a **removal**: the record is deleted
    by the time a settle looks, so the handle in the region can no longer be asked what
    body it was about.  A body left opposed by such a removal — three sentexes across two
    contexts, one retracted — would otherwise lose its entry and never be re-derived,
    since `note-opposed!` drops the entry on the way past.

  Both are filtered to bodies that are actually opposed, which on a KB with a handful of
  contradictions is nearly none of what either input offers.

  A genlContext edge is the third way, and it is not narrowed: joint visibility is read
  through that closure for every pair at once, so its generation retires the whole memo
  instead (`negation-nogoods`)."
  [kb opposed dirty]
  (into (into #{} (filter opposed) dirty)
        (comp (keep #(p/get-sentex (:records kb) %))
              (map #(kb/body-under-not (:sentence %)))
              (filter opposed))
        (jtms/touched (:tms kb))))

(defn- opposed-bodies-of
  "The opposed bodies `handles` name — the handles whose body is not stored in both
  polarities drop out, which on a KB with a handful of contradictions is nearly all of
  them."
  [kb handles]
  (let [opposed @(:opposed kb)]
    (when (seq opposed)
      (into #{} (comp (keep #(p/get-sentex (:records kb) %))
                      (map #(kb/body-under-not (:sentence %)))
                      (filter opposed))
            handles))))

(defn- note-supersession-flips!
  "Post the opposed bodies of the handles whose supersession just flipped to the
  `:negations` memo's dirty set.

  Supersession is the one belief change that leaves **no relabel** to record it: `in?`
  subtracts the superseded set, so a spelling an equality merge displaces stops matching
  — and stops pairing — while its label never moved.  `moved-bodies` reads the
  relabelled region and the store choke points, and neither sees this, so the flip is
  handed over by hand here, exactly as the taxonomy reconcile below is handed the same
  handles for the same reason.

  Posted rather than acted on, because this runs *after* the settle's rounds have
  decided: un-merging revives a spelling whose pair is then found by the next settle, and
  that one-settle lag is the same one the reconcile below accepts.

  **A narrow window, and `negation_oracle_test` does not reach it** — worth saying rather
  than leaving as an apparent redundancy.  Displacing a body normally *carries* its entry
  rather than dropping it: migration writes the twins on the representative's body, so
  nothing stores, removes or relabels on the displaced one, and the stale entry sits there
  until the un-merge makes it live again — `resolve-contradictions` filters on belief, so
  it does no harm meanwhile and needs no help coming back.  What this covers is the case
  where something *does* re-derive the displaced body during the window: it derives
  nothing (a superseded spelling is not believed), the entry is dropped, and then only
  this says the pair is back.  The hand-off costs one map read per settle on a KB with no
  merges, and it is the same one the two reconciles below take for the same reason."
  [kb before after]
  (let [flipped (into (into #{} (remove after) (keys before))
                      (remove before)
                      (keys after))]
    (when-let [bodies (seq (opposed-bodies-of kb flipped))]
      (swap! (:negations kb) update :dirty (fnil into #{}) bodies))))

(defn- negation-nogoods
  "Believed contradictions: every believed `(not X)` paired with a believed `X` when
  **some context sees both** — i.e. the two contexts have a non-empty common
  down-closure.

  `sees?` either way is too weak a test: it only catches a *comparable* pair.  Two
  incomparable contexts can still share a descendant, and from that descendant both
  the positive and the negation are visible — the clash is real there, and reporting
  it only when one context happens to sit above the other would silently exempt every
  sibling context.  The common-descendant test strictly generalises `sees?`
  (if K sees Y then K is itself a common descendant), so nothing `sees?` catches is
  lost.

  The pair test is **memoized per call**: two believed facts of the same opposed body
  form a pair each, so re-answering the common-descendant question per pair would
  repeat work.  Contexts are few and repeat constantly, so the memo collapses it back
  to one computation per distinct context pair.

  **Discovery is driven off the maintained opposed set, not a scan.** A nogood needs a
  body asserted in *both* polarities, and most negative facts have no positive twin.
  Scanning every stored negation each settle to find the few that clash is O(all
  negations) per settle — quadratic over a negation-heavy load, since a settle runs
  after every mutation.  `kb`'s `:opposed` set already holds exactly the doubly-stored
  bodies, maintained O(1) per mutation (`kb/note-opposed!`), so a KB with no
  contradiction at all does one emptiness read here and nothing else.  `lein perf`'s
  `negation-load` is the gate on that.

  **Pairing is memoized per body**, and it is a separate claim that needs a separate
  gate.  Iterating the opposed set is proportional to the *standing* contradictions
  rather than to the change, and each body iterated costs two belief-filtered `query`
  calls and a cross product — per settle *round*, and a settle follows every mutation.
  That makes loading N dilemmas Θ(N²) even when no two of them share a term, which is
  exactly the shape `clash-nogoods` carries its own answers forward to avoid.  So this
  re-derives only the bodies `moved-bodies` names and carries the rest verbatim out of
  `:negations`; `negation-arbitration` is the gate, and it separates the two by 12x.

  Carrying is sound for the same reason it is there: a carried entry's pairs and their
  `:priority` are functions of two handles' belief and defeat classes, and neither can
  move without the handles entering a relabelled region.  What a carried entry is *not*
  is live — a member defeated later in this settle leaves it standing — so
  `resolve-contradictions` filters on belief before deciding anything.

  The whole memo is retired when the genlContext generation moves, since joint
  visibility is read through that closure for every pair at once and a new context edge
  can make a pair visible that no handle of either side went near.

  The opposed set cannot miss a symmetric pair: `sentex/sentex` normalizes a fact's body
  *before* the `not` wraps it, so `(not (siblingOf Ann Bob))` and `(siblingOf Ann
  Bob)` store the same sorted body and both polarities key under it.  Membership is
  structural (storage, not belief); the exact belief-and-visibility pairing in
  `body-nogoods` is what actually forms a nogood, so a body with no *believed* pair
  costs only two empty queries, never a missed clash.

  Each nogood carries a priority (the stronger class involved) and a readable
  sentence.

  The memo is written back with a **CAS**, not a `reset!`.  `kb/note-opposed!` posts to
  the same atom from the store and removal choke points, and a post landing between the
  read and the write would be overwritten — the body it dropped from `:by-body` restored,
  and the body it added to `:dirty` lost, so the next settle would never re-derive a
  pairing that had moved.  The write therefore carries every post it finds, and the
  entries for those bodies go with them.  `drain-recheck!` is the same shape.

  The one arm that still resets outright is the empty-`:opposed` one, and it is not the
  same case: it leaves no `:vocab`, so the next settle reads the memo as stale and
  re-derives the whole of `:opposed` regardless of what `:dirty` said."
  [kb]
  (let [opposed @(:opposed kb)]
    (if (empty? opposed)
      ;; nothing is stored in both polarities, so nothing can pair — and this is the one
      ;; place the whole memo can be dropped rather than re-examined, exactly as
      ;; `constraint-nogoods` drops `:clashes` when nothing separates anything
      (do (reset! (:negations kb) {}) #{})
      (let [tax   (:taxonomy kb)
            prev  @(:negations kb)
            vocab (tax/relation-gen tax :genlContext)
            stale? (or (not *incremental-negations*) (not= vocab (:vocab prev)))
            moved  (if stale? opposed (moved-bodies kb opposed (:dirty prev)))
            share-a-view? (memoize (fn [ca cb] (tax/common-descendant? tax [ca cb])))
            by-body (reduce (fn [m b]
                              (let [ngs (body-nogoods kb b share-a-view?)]
                                ;; a body that has stopped pairing leaves the memo, or it
                                ;; would be re-derived on every settle for the rest of the
                                ;; KB's life
                                (if (seq ngs) (assoc m b ngs) (dissoc m b))))
                            (if stale? {} (:by-body prev {}))
                            moved)]
        (loop []
          (let [cur    @(:negations kb)
                ;; `:dirty` only grows between the read of `prev` and this write, and
                ;; only this fn clears it — so the difference is exactly the posts that
                ;; landed while the bodies above were being re-derived
                posted (set/difference (set (:dirty cur)) (set (:dirty prev)))
                next   {:vocab   vocab
                        :by-body (apply dissoc by-body posted)
                        :dirty   posted}]
            (if (compare-and-set! (:negations kb) cur next)
              (into #{} cat (vals (:by-body next)))
              (recur))))))))

(defn- decide-nogood
  "Decide a nogood from its members' defeat-classes alone: defeat the strictly-weaker
  member; a defeasible tie is a **dilemma**; an equal monotonic clash is hard
  (reported, never thrown).

  A default/default clash is not arbitrated.  Neither rule named the other's case and
  neither out-ranks the other, so both sides stay believed at `:default` and the pair
  is reported by `contradictions`.  Undercutting an assumption is what `exceptWhen`
  is for; rebutting one with an equally good argument is a state of the world, and
  deciding it arbitrarily would destroy the very thing an application wants to rank
  (docs/exceptions.md, \"What surfaces where\").

  There is one axis, defeat-class.  Specificity is structural, not a tie-break:
  `penguin ⇒ ¬flies` beating `bird ⇒ flies` is expressed by the bird rule stating its
  own `exceptWhen` exception and never firing for a penguin, so there is no
  contradiction to arbitrate in the first place."
  [kb {:keys [nogood] :as ngmap}]
  (let [tms      (:tms kb)
        [a b]    (vec nogood)
        ca       (jtms/defeat-class tms a)
        cb       (jtms/defeat-class tms b)
        ra       (strength/rank-of ca) rb (strength/rank-of cb)]
    (cond
      (< ra rb)                 {:defeat a}
      (< rb ra)                 {:defeat b}
      (strength/defeasible? ca) {:dilemma ngmap}
      :else                     {:hard ngmap})))

(defn- contested-content
  "What each contested handle asserts, for the solver.  A tie-break must key on the
  *content* of a datum, never on its handle — handles are allocated in assertion
  order, so a handle-keyed choice would make the outcome depend on the order the
  knowledge arrived (see `solve/content-key`)."
  [kb handles]
  (into {} (keep (fn [h]
                   (when-let [s (p/get-sentex (:records kb) h)]
                     [h {:sentence (:sentence s) :context (:context s)}])))
        handles))

(defn- check-solver-eligible
  "Guard the solver's *input*: every contested handle must be a plain `:default`.

  `decide-nogood` already guarantees it — a tie is contested only when both members
  are defeasible and equal in class — but nothing enforced it, and the cost of a
  regression is not a wrong answer, it is the engine handing away content it knows
  to be true.  `:monotonic` is the fixed background a solve reasons *from*; a solver
  that could withdraw it would be deciding the premises.

  Classes are read here, before any defeat lands, because `defeat-class` reports nil
  once a datum is OUT — after the fact the check is unavailable."
  [kb contested]
  (let [tms (:tms kb)]
    (when-let [bad (seq (remove #(strength/defeasible? (jtms/defeat-class tms %)) contested))]
      (throw (ex-info "known-true content reached the edge solver"
                      {:type     :not-defeasible
                       :handles  (vec bad)
                       :classes  (mapv #(jtms/defeat-class tms %) bad)
                       :expected :default})))))

(defn- accepted-defeat
  "Guard the solver's *output*: keep only defeats the program actually offered.

  Returns the accepted set, warning if anything was dropped — a solver naming a
  handle outside its own assumptions is a bug in that solver, and the engine should
  neither obey it nor fail because of it."
  [prog defeat]
  (let [assumptions (:assumptions prog)
        accepted    (into #{} (filter assumptions) defeat)]
    (when-let [dropped (seq (remove assumptions defeat))]
      ;; handles only — the KB and the Program carry the whole TMS, and a warning
      ;; nobody can read is a warning nobody reads
      (trove/log! {:level :warn :id ::solver-overreach
                   :msg  (str "solver returned defeats outside its assumptions; ignoring "
                              (pr-str (vec dropped)))
                   :data {:dropped (vec dropped) :offered (count assumptions)}}))
    accepted))

(defn- live-nogood?
  "Are both members of a nogood still believed?

  **Every** nogood is filtered through this before it is decided, and neither source can
  be trusted to arrive live.  A round that defeats one member must not be handed the same
  pair again — `defeat-class` reports nil for an OUT datum, which ranks 0, which would
  read as \"defeat it again\" and never terminate.  The definitional nogoods are computed
  once for the settle, so a later round's defeat leaves them stale; the negation nogoods
  are carried per body across settles (`negation-nogoods`), so a defeat leaves the carried
  entry standing until the region that moved asks for its body again.  Two different
  reasons, one filter, and it costs two map reads."
  [tms {:keys [nogood]}]
  (every? #(jtms/in? tms %) nogood))

(defn- believed-excepts
  "The believed visibility-`except` handles, as a set — the instrument the settle
  loop diffs across a pass to catch a *belief* flip on one.  Gated on the functor
  count, so a KB using no `except` pays one index read."
  [kb]
  (let [idx (:index kb)]
    (if (pos? (p/count-with-functor idx sx/except-functor))
      (into #{} (filter #(jtms/in? (:tms kb) %))
            (p/sentexes-with-functor idx sx/except-functor))
      #{})))

(defn- recheck-flipped-excepts
  "Queue the re-check for every visibility `except` in `handles` and return the rule
  handles it marked.  A *belief* flip on an except — defeated by this settle's
  resolution, or revived by `clear-defeats!` — changes which handles are hidden
  exactly as its arrival or departure does, and the store/removal chokepoints that
  ordinarily call `recheck-except` cannot see a flip: without this, defeating an
  except revives nothing it hid, and which belief set a KB ends with depends on the
  order the except and its defeater arrived.  The returned rules force the loop's
  productive branch — a reveal has no blocked justification to move and no refusal
  record to release, so nothing else marks the pass productive."
  [kb handles]
  (into #{}
        (comp (keep #(p/get-sentex (:records kb) %))
              (filter #(= sx/except-functor (nm/functor (:sentence %))))
              (mapcat #(special/recheck-except kb %)))
        handles))

(defn- resolve-contradictions
  "Resolve the nogoods to a fixpoint, returning
  `{:violated [hard...] :dilemmas [ngmap...]}`.

  Two sources, one resolution.  `negation-nogoods` is asked every round, since defeating
  one pair can change which others are believed — it answers from its per-body memo, so a
  round that moved nothing re-derives nothing.  `constraint` — the definitional clashes —
  is computed once for the settle and passed in: its discovery walks the moved region, and
  a defeat only ever *removes* belief, so a round can retire one of these pairs but never
  create one.  Both are filtered to the pairs still believed before each decision, and
  neither may skip that filter (`live-nogood?` says why).

  `solver-violated` accumulates only the solver's one-shot reports across defeat
  rounds; the hard (irreducible) clashes and the dilemmas are collected once, at the
  terminal iteration — otherwise a clash that persists alongside another round's work
  would be re-counted every round.

  **The `:contested` branch is reachable only from a nogood a custom `decide-nogood`
  contests.** The built-in decision reports a default/default tie as a `:dilemma`
  instead of handing it to the edge solver.  The branch is kept because the solver seam
  is public — `set-solver` takes any implementation, and `last-program` /
  `asp.edge/classify` are written against this shape."
  [kb constraint]
  (loop [solver-violated []]
    (let [active (seq (into #{}
                            (filter #(live-nogood? (:tms kb) %))
                            (concat constraint (negation-nogoods kb))))]
      (if-not active
        {:violated solver-violated :dilemmas []}
        (let [decisions (map #(decide-nogood kb %) active)
              clears    (into #{} (keep :defeat decisions))]
          (if (seq clears)
            (do (jtms/defeat (:tms kb) clears) (recur solver-violated))
            (let [contested (into #{} (mapcat :contested decisions))
                  hard      (vec (keep :hard decisions))
                  dilemmas  (vec (keep :dilemma decisions))]
              (if (empty? contested)
                {:violated (into solver-violated hard) :dilemmas dilemmas}
                (let [_    (check-solver-eligible kb contested)
                      prog (solve/program contested active (contested-content kb contested))
                      _    (reset! (:program kb) prog)   ; the tie, before belief erases it
                      res  (solve/solve @(:solver kb) prog)
                      ;; A solver decides only what it was handed.  `set-solver`
                      ;; takes any implementation, and an unclamped :defeat would
                      ;; let a third-party one withdraw known-true content the
                      ;; program never offered it — the exact failure the
                      ;; assumptions/fixed split exists to prevent.
                      defeat (accepted-defeat prog (:defeat res))]
                  (if (seq defeat)
                    (do (jtms/defeat (:tms kb) defeat)
                        (recur (into solver-violated (:violated res))))
                    {:violated (into (into solver-violated hard) (:violated res))
                     :dilemmas dilemmas}))))))))))

(defn- clash-report
  "A standing clash as data: the coexisting pair with both handles, both sentences, and
  the justifications behind each side — which is what an application needs in order to
  rank an argument the engine deliberately declines to decide.

  **The same shape for both readings.**  `contradictions` reports the defeasible
  dilemmas and `conflicts` the irreducible known-true clashes, and the two differ only
  in *why* they were left standing — not in what a caller needs to know about them.
  Reporting the harder case with less material than the easier one is backwards: a
  `:monotonic` clash is precisely the one where the engine has declined hardest and the
  application has the most to do.

  `:kind` is what the pair clashes *on* — `:disjoint` / `:functional` / `:asymmetric`
  for a definitional clash, and nil for a plain rebuttal, where the sentence being its
  own negation is the whole story.  Without it the two read alike, and they are not
  alike: a rebuttal is two claims about the world, where a definitional clash is a
  violation of what the KB says its own vocabulary means.

  Nothing here is stored.  A clash is a **report** recomputed from current belief each
  settle, never a sentex: `(contradicts X Y)` asserted would be a premise needing truth
  maintenance of its own, and it would go stale the moment either side moved
  (resources/kb/CoreContext.txt says so of the predicate itself)."
  [kb {:keys [nogood priority sentence kind]}]
  (let [tms   (:tms kb)
        recs  (:records kb)
        ;; Ordered by **content**, the same rule `clash-nogoods` orders the pair inside
        ;; `:sentence` by, and for the same reason: a handle is allocated in assertion
        ;; order, so sorting the sides by one would make "which side is first?" an
        ;; answer about which was typed first while `:sentence` beside it said the same
        ;; thing either way.  The context separates one sentence clashing with itself
        ;; across two contexts; the handle is the last resort, for a pair a reader
        ;; cannot tell apart anyway.
        sides (->> nogood
                   (map (fn [h]
                          (let [s (p/get-sentex recs h)]
                            {:handle h :sentence (:sentence s) :context (:context s)
                             :defeat-class (jtms/defeat-class tms h)
                             :justifications (vec (keep #(p/get-justification recs %)
                                                        (jtms/supports tms h)))})))
                   (sort-by (juxt (comp pr-str :sentence) (comp pr-str :context) :handle))
                   vec)]
    {:nogood nogood :priority priority :sentence sentence
     :handles (mapv :handle sides)
     :kind kind
     :sides sides}))

(defn- record-clashes!
  "Publish the settle's two readings, rebuilding only the reports that could have moved.

  A `clash-report` reads its two handles and nothing else — their sentences, their
  contexts, their defeat classes, and the justifications supporting them.  Standing
  clashes are the case that matters: a settle follows every mutation, so rebuilding all
  of them per settle is a per-assert cost proportional to how many are standing, and
  loading a KB that holds them is quadratic in exactly the way `docs/nmtms.md` records
  for the defaults phase.

  A pair the settle's region does not hold has the report it had last settle, and that
  claim rests on the region covering **every** input to one — which took making the
  region cover a little more than belief.  Sentences come off two immutable records;
  defeat classes move only by relabelling; `:priority` and `:sentence` are read off those
  same two handles by the nogood.  The **supporting justifications** are the part belief
  alone does not cover: a *redundant* justification is precisely the write the JTMS
  declines to relabel for (an already-believed conclusion gaining a second derivation
  that confers no stronger a class, the fast path that collapses a recursive forward load
  from O(derived²)), so a side gains a reason while its label sits still — and in a
  dilemma the engine declines to decide, the reasons are the whole answer a caller is
  given.  `jtms/add-just*` therefore notes the consequence as touched on that path, which
  is O(1) at the write where asking every standing pair for its support count here is
  O(standing) per settle — a 19% worse growth ratio on `lein perf`'s
  `negation-arbitration` at 800 standing dilemmas, against no measurable change for the
  O(1) route.

  `:kind` is compared as well, because it is the one field a nogood reads off the
  **vocabulary** rather than off the pair — a keyword identity test, and cheap insurance
  against a pair two of the definitional checks could each convict.

  The memo is rebuilt from what is reported *now*, so it holds the standing set rather
  than accumulating every pair the KB has ever had.  Must run before
  `jtms/reset-touched!` — the region is what says which reports to keep."
  [kb violated dilemmas touched]
  (let [prev  @(:reports kb)
        moved (set touched)
        build (fn [ng]
                (or (when-not (some moved (:nogood ng))
                      (when-let [r (get prev (:nogood ng))]
                        (when (= (:kind ng) (:kind r)) r)))
                    (clash-report kb ng)))
        ;; The *list* is ordered by the same rule the sides inside each report are:
        ;; content, never handles.  The reports come off a hash set of handle-keyed
        ;; nogoods, so an unsorted vector puts `(first (contradictions kb))` at the
        ;; mercy of assertion order — the leak `clash-report` closes one level down.
        ;; The key rides the report's *metadata*, computed once when the report is
        ;; built and carried with it through the memo: `pr-str`ing every side of
        ;; every standing report per settle is O(standing) string work on the path
        ;; whose whole memo exists to avoid exactly that (`clash-arbitration` gates
        ;; it), and metadata stays off the wire and out of `=`.
        rkey  (fn [r] (or (::order (meta r))
                          (mapv (juxt (comp pr-str :sentence) (comp pr-str :context))
                                (:sides r))))
        keyed (fn [r] (cond-> r (nil? (::order (meta r)))
                              (vary-meta assoc ::order (rkey r))))
        vs    (vec (sort-by rkey (map (comp keyed build) violated)))
        ds    (vec (sort-by rkey (map (comp keyed build) dilemmas)))]
    (reset! (:reports kb) (into {} (map (juxt :nogood identity)) (concat vs ds)))
    (reset! (:conflicts kb) vs)
    (reset! (:contradictions kb) ds)))

;; ---- the exception fixpoint ---------------------------------------------
;; Belief and blocking are mutually dependent: a level-6 exception query reads
;; believed facts, and which facts are believed depends on which justifications are
;; blocked.  So `settle` iterates — relabel, re-evaluate the exceptions the triggers
;; queued, relabel again if the blocked set moved.

(def ^:private max-settle-passes
  "Hard bound on the exception fixpoint.

  Stratification is what makes the loop *terminate*, and it is enforced at assert time
  rather than assumed here — `checks/check-stratified`, `check-exceptWhen-stratified`
  and `check-edge-stratified` refuse a cycle through negation before it can be stored.
  This bound is the backstop under that: it makes a bug unable to hang the engine.
  Realistic content converges in one productive pass (docs/exceptions.md), so a run
  that exhausts this bound is a defect and says so in the log rather than spinning."
  16)

(defn- drain-recheck!
  "Take the queued `{rule-handle -> triggers}` map and clear the queue, so a re-check
  is never done twice and a rule queued *during* a pass is picked up by the next one.

  One CAS rather than deref-then-`reset!`.  The reset shape silently discarded any
  `swap!` landing between the two, which under incidental concurrency — a REPL thread
  beside the web handler, which `lein browser` starts by default — dropped queued
  re-checks outright rather than merely delaying them.  `vaelii.impl.jtms` carries the
  same fix and the reason it was needed; this queue had been left behind."
  [kb]
  (let [a (:recheck kb)]
    (loop []
      (let [old @a]
        (if (compare-and-set! a old {})
          old
          (recur))))))

;; ---- narrowing the re-check to the firings a trigger can reach ----------
;;
;; The index is keyed by rule, which is right: a rule handle is an antecedent of every
;; justification it licenses, so nothing per-firing has to be stored.  But *evaluating*
;; every firing of a queued rule costs one level-6 query each, so a rule that has fired
;; N times paid N queries per relevant fact arrival — quadratic in its firing count,
;; and measurably so (docs/exceptions.md, "The cost is in re-checking").
;;
;; The narrowing below runs **before** any query and touches nothing but memory:
;; substituting the firing's bindings into the rule's exception conjuncts is pure
;; structure manipulation, and both tests it then applies — argument agreement and the
;; `specs` closure — read the in-memory taxonomy.  A candidate that survives runs the
;; query; a candidate that does not was unreachable from anything that changed.
;;
;; It is an **over-approximation by construction**, and has to be: a spurious re-check
;; costs one query, a missed one is a conclusion that should have been swept and
;; wasn't.  Every "cannot tell" below answers *keep*.

(defn- peel-negation
  "A literal with any `not` wrappers stripped.  Polarity is deliberately dropped: the
  question here is only which content a trigger is *about*, and `(flies X)` coming and
  going is about the same content as `(not (flies X))`."
  [s]
  (if (and (sequential? s) (= 'not (first s)) (= 2 (count s)))
    (recur (second s))
    s))

(defn- literal-shape
  "`[predicate {argument -> count}]` of a flat literal — the shape a stored fact must
  have for level 6 to answer that literal from it — or **nil** when the literal is not
  flat and ground, which is exactly when no shape test can be trusted.

  Arguments are compared as a *multiset* rather than a vector so a symmetric
  predicate's mirrored fact still matches: `(siblingOf Bob Ann)` is the same content as
  `(siblingOf Ann Bob)`, and level 6 probes both orders."
  [lit]
  (let [body (peel-negation lit)]
    (when (and (sequential? body) (symbol? (nm/functor body)))
      (let [as (nm/args body)]
        (when (and (seq as)
                   (not-any? sequential? as)               ; a nested subterm: cannot tell
                   (not-any? #(and (symbol? %) (sx/variable? %)) as))
          [(nm/functor body) (frequencies as)])))))

(defn- cross-argument-predicate?
  "Is `pred` one whose truth a level-6 prover can derive from content with *different*
  arguments?  Then argument agreement proves nothing about it and every candidate is
  kept.

  These are exactly the provers that reason across arguments: the `genl` /
  `genlContext` closures, disjointness (closed under genl), a predicate declared
  transitive or reflexive or holding an inverse, one with a **preserved argument
  position**, and the evaluables — computed rather than stored, so no fact can move
  them at all, but cheaper to wave through than to reason about.

  Argument-position preservation is the one that has to be read per KB rather than
  listed: `(argPreserving P n R)` makes a stored `(P … W …)` answer `(P … A …)` for
  every `A` in `W`'s reach, so a trigger about `dog` flips an exception written about
  `poodle` and the two literals agree on **no argument at all**.  Which predicates
  those are is a property of the content (`special/recheck-preserving-along` reads the
  same declarations to close the trigger side of the same channel), so the O(1) gate
  in front of the real read is what is asked here.

  The property reads are **global on purpose**: over-keeping a candidate costs one
  re-evaluation, under-keeping one is a missed withdrawal."
  [kb pred]
  (let [tx (:taxonomy kb)]
    (or (contains? provers/transitive-predicates pred)
        (contains? provers/evaluable-predicates pred)
        (= 'evaluate pred)
        (= 'disjoint pred)
        (tax/has-prop? tx :transitive pred)
        (tax/has-prop? tx :reflexive pred)
        (some? (tax/inverse-of tx pred))
        (inherit/declared-about? kb pred))))

(defn- trigger-shapes
  "The shapes of a rule's queued triggers, or `:all` when the rule was queued
  unconditionally or any trigger has no readable shape."
  [triggers]
  (if (= :all triggers)
    :all
    (let [ss (map literal-shape triggers)]
      (if (some nil? ss) :all (set ss)))))

(defn- firing-reachable?
  "Could any trigger of shape in `shapes` have flipped this firing's exception?

  The firing's `bindings` are substituted into each exception conjunct — closure makes
  that ground — and the conjunct is compared with each trigger.  A trigger can answer a
  conjunct only when their arguments agree **and** the trigger's predicate lies in the
  conjunct predicate's `specs` closure: an exception on `flightless` is satisfied by a
  stored `(penguin Opus)` when `(genl penguin flightless)`, so a bare equality test on
  the predicate would silently miss the case the taxonomy exists for.  That is the same
  test `recheck-on-predicate` keys the index on, read in the other direction, so this
  narrows *within* what the index already selected and never past it.  Both read the
  **global** spec closure, deliberately: the two sides must agree, and a
  context-narrowed read here would under-select — a missed withdrawal, not a wasted
  re-check.

  Any conjunct reaching is enough: the exception is a conjunction, so moving one
  conjunct can move the whole.

  `cross?` is `cross-argument-predicate?` memoized for the whole pass, and the memo is
  the caller's rather than this function's because the question is asked once per
  conjunct per **firing** while its answer ranges over the handful of predicates the
  queued rules' exceptions mention — substituting bindings never moves a functor.  One
  of its arms is an index read on a KB that declares a preserved position, and paying
  that per firing would put a store access back inside the filter whose whole claim is
  that it touches nothing but memory."
  [kb except bindings shapes cross?]
  (boolean
   (some (fn [lit]
           (if-let [[lp la] (literal-shape (res/substitute lit bindings))]
             (or (cross? lp)
                 (let [specs (tax/specs (:taxonomy kb) lp)]
                   (some (fn [[tp ta]] (and (= la ta) (contains? specs tp))) shapes)))
             true))                                       ; unreadable conjunct: keep
         except)))

(defn- exception-candidates
  "The justifications whose exception the queued triggers could have flipped.

  One record fetch per **rule**, never per firing — the point of the narrowing is that
  deciding it costs no store access — and `:all` skips it entirely, since an
  unnarrowable rule keeps all of its firings anyway.  `cross?` is memoized here, across
  every rule of the pass, for the reason `firing-reachable?` records."
  [kb queued]
  (let [tms    (:tms kb)
        cross? (memoize #(cross-argument-predicate? kb %))]
    (into #{}
          (mapcat (fn [[rh triggers]]
                    (let [firings (jtms/dependents tms rh)
                          shapes  (trigger-shapes triggers)
                          rsx     (when-not (= :all shapes) (p/get-sentex (:records kb) rh))
                          ;; both block conditions narrow the same way — an exception's
                          ;; conjuncts and an `unknown` antecedent's inner queries are all
                          ;; literals a trigger could have moved (docs/naf.md).  The
                          ;; exception conjuncts come from the belief-following exceptWhen
                          ;; meta-sentexes (block-if-any); flattening them for the
                          ;; over-approximating narrowing is sound (any conjunct reaching keeps).
                          ;; an aggregate's body joins them: it is a literal a trigger
                          ;; could have moved, and it always mentions the reduction
                          ;; variable, so it is never ground and always keeps (which is
                          ;; the safe direction — over-keeping costs a re-evaluation,
                          ;; under-keeping is a missed withdrawal)
                          block-lits (when rsx
                                       (concat (apply concat (provers/rule-exceptions kb rh))
                                               (rules/naf-queries rsx)
                                               (rules/aggregate-queries rsx)))]
                      (if (seq block-lits)
                        ;; the firing's bindings live on the *record* — the network
                        ;; keeps only what belief is computed from (`jtms/graph-just`)
                        (filter (fn [jid]
                                  (if-let [j (p/get-justification (:records kb) jid)]
                                    (firing-reachable? kb block-lits (:bindings j) shapes
                                                       cross?)
                                    false))
                                firings)
                        firings))))                        ; :all, or nothing to read
          queued)))

(defn- exception-blocked-set
  "The blocked set after re-evaluating the exceptions of the firings the queued
  triggers could have reached.

  The rule handle is an antecedent of every justification it licenses, so
  `jtms/dependents` reaches every firing of a rule with no per-firing bookkeeping —
  that structural fact is what lets the re-check index be keyed at *rule* granularity.
  `exception-candidates` then narrows those firings to the ones the triggering
  sentences could actually have moved, so the level-6 queries below are paid per
  *affected* firing rather than per firing the rule ever made.

  `jtms/set-blocked` is a **replace**, so this states the whole answer: blocks on
  justifications outside the candidate set are carried forward untouched (nothing
  relevant to them changed), and every candidate is re-decided from scratch.  Nothing
  remembers that a justification was blocked a pass ago, so belief cannot depend on
  the order the exceptions were discovered in."
  [kb queued]
  (let [tms   (:tms kb)
        cands (exception-candidates kb queued)
        held  (into #{} (remove cands) (jtms/blocked tms))]
    (into held
          (filter (fn [jid]
                    ;; the record, not the network's graph entry: deciding whether a
                    ;; firing is excepted re-runs its exception query, which needs the
                    ;; firing's bindings
                    (when-let [j (p/get-justification (:records kb) jid)]
                      (chain/justification-excepted? kb j))))
          cands)))

(def ^:dynamic *touched-sink*
  "An atom holding a set, or nil.  When bound, every settle folds the datums whose
  region it relabelled into it before clearing them — the affected region of whatever
  the caller just did, which would otherwise be discarded at the end of each settle.
  `core/preview` binds it and diffs belief over that set alone."
  nil)

(def ^:dynamic *touched-in-sink*
  "The companion of `*touched-sink*`: which of those datums were **believed before**
  (`jtms/touched-in`).  A caller binding both learns which way each one moved, which the
  region alone cannot say — most of a relabelled region does not move at all.

  `core/edit!`'s consequence report binds both.  `preview` binds only the region, because
  its rollback lets it read belief-before off the restored KB instead."
  nil)

(def ^:dynamic *sweep?*
  "Does a settle **delete** what a newly-blocked justification was solely supporting?

  True everywhere except inside `core/preview`, which has to hand the KB back exactly
  as it found it: the sweep is the one settle effect a rollback cannot undo at the same
  handles, since putting a deleted conclusion back means deriving it again and a
  re-derivation lands on a fresh handle.  Suppressing it costs nothing semantically —
  a swept datum is already OUT and ungroundable, so leaving it stored moves no label
  and it still matches nothing.  The rollback runs with the sweep back **on**, which is
  what collects a conclusion the preview's own removals brought into being."
  true)

(defn- sweep-excepted!
  "Garbage-collect what the newly-blocked justifications were solely supporting.

  A blocked justification is not a defeated conclusion — it is simply *invalid*, so
  the conclusion is unsupported and the ordinary dependency-directed sweep **deletes**
  it along with everything resting on it.  Each deleted fact is itself a re-check
  trigger: removing it may release some *other* rule's exception."
  [kb newly-blocked]
  (let [tms   (:tms kb)
        seeds (when *sweep?*
                (into #{} (keep #(:consequence (jtms/justification tms %))) newly-blocked))]
    (when (seq seeds)
      (let [{:keys [removed-sentexes removed-justifications]} (jtms/sweep! tms seeds)]
        ;; fetch before tearing down: the JTMS hands back handles, and
        ;; `sentex-removed!` is what deletes the record
        (doseq [d removed-sentexes
                :let [sx (p/get-sentex (:records kb) d)]
                :when sx]
          (integrate/sentex-removed! kb sx))
        (doseq [jid removed-justifications] (p/delete-justification! (:records kb) jid))))))

(defn- released-rules
  "The rules whose exception this pass **lifted** — the informants of the justifications
  that were blocked and are not any more.

  Those, and only those, have a conclusion that was deleted and now has to be derived
  again.  A justification that was *newly* blocked has nothing to revive: its
  conclusion is what the sweep is about to collect.

  Read before the sweep runs, so a justification the sweep is about to delete is still
  there to be asked for its informant."
  [kb was new]
  (let [tms (:tms kb)]
    (into #{}
          (keep (fn [jid]
                  (let [inf (:informant (jtms/justification tms jid))]
                    (when (integer? inf) inf))))
          (remove new was))))

(defn- released-refusals
  "What the queued triggers may have **released** among the firings that were refused
  before they could become justifications: `{:free [[rule-handle entry] …] :overflow
  [rule-handle …]}`.

  `released-rules` above reads a release off the blocked set, which only ever names
  firings that were placed.  A firing `chain/place-conseq` refused left no justification
  to be blocked, so its release has to be found by re-asking the question it was refused
  on — one level-6 query per recorded refusal, in place of a join over the whole extent
  (docs/exceptions.md, \"A refused firing is remembered as bindings\").

  Narrowed exactly as `exception-candidates` narrows a rule's justifications, with the
  same filter and the same memo: substituting a refusal's bindings into the rule's block
  literals is the same structure manipulation, and a trigger that could not reach the
  substituted literal could not have released the firing either.

  Dead entries are **pruned as they are read** — retiring one is not a belief decision,
  so it may happen whenever the record is walked, and leaving them would let a rule's
  record overflow on firings whose support is long gone.

  A rule whose record overflowed keeps no entries to re-ask, so it is named instead: the
  caller re-joins it, which is the coarse fallback the cap buys its way out of."
  [kb queued]
  (let [refused @(:refused kb)]
    (if (empty? refused)
      {:free [] :overflow []}
      (let [cross? (memoize #(cross-argument-predicate? kb %))]
        (reduce
         (fn [acc [rh triggers]]
           (let [recs (get refused rh)]
             (cond
               (nil? recs)        acc
               (= :overflow recs) (update acc :overflow conj rh)
               :else
               (let [shapes (trigger-shapes triggers)
                     rsx    (when-not (= :all shapes) (p/get-sentex (:records kb) rh))
                     ;; the same two block conditions the refusal record covers, and the
                     ;; same flattening `exception-candidates` uses: any literal reaching
                     ;; keeps the entry, which is the safe direction
                     lits   (when rsx
                              (concat (apply concat (provers/rule-exceptions kb rh))
                                      (rules/naf-queries rsx)))]
                 (reduce (fn [acc e]
                           (case (chain/refusal-state kb rh e)
                             :free (update acc :free conj [rh e])
                             :dead (do (chain/drop-refusal! kb rh e) acc)
                             acc))
                         acc
                         (if (seq lits)
                           (filter #(firing-reachable? kb lits (:bindings %) shapes cross?)
                                   recs)
                           recs))))))
         {:free [] :overflow []}
         queued)))))

(defn- blanket-recheck-rules
  "The queued rules with no triggering sentence (`:all` — a taxonomy edge moved, or the
  rule was just indexed).  Those keep the coarse re-chain: with no sentence to read,
  nothing says whether the move blocked or released, so the re-derivation has to be
  attempted either way."
  [queued]
  (keep (fn [[rh triggers]] (when (= :all triggers) rh)) queued))

(defn- aggregate-recheck-rules
  "The queued rules carrying an **aggregate** antecedent, which need the join run again
  whatever the blocked set did.

  Every other re-check condition is a *block*: releasing one shows up as a
  justification leaving the blocked set, and re-chaining is owed exactly to the rules
  that released.  An aggregate is not, because it binds a **value**.  A count going
  1 ⇒ 2 makes a firing that never existed — there is no blocked justification to
  release, nothing moves in the blocked set, and without this the pass would converge
  having derived nothing.  (2 ⇒ 3 is the other half, and that one *is* a block: the
  old firing is withdrawn above.  Both halves happen in the same pass.)

  One record fetch per queued rule, which `exception-candidates` has already paid for
  every rule it narrowed."
  [kb queued]
  (keep (fn [[rh _]]
          (when-let [rsx (p/get-sentex (:records kb) rh)]
            (when (and (rules/rule? rsx) (rules/has-aggregate? rsx)) rh)))
        queued))

(defn rechain-exception-rules
  "Re-derive what a released exception was suppressing.

  Revival under `exceptWhen` costs a **re-derivation**, not a flipped bit: the
  conclusion was deleted, so there is nothing to relabel back into belief and the rule
  has to fire again.  Re-firing a rule whose conclusion still stands is a no-op
  (`has-justification?` dedups it), and re-firing one whose exception still holds is a
  no-op too (`derive-conclusion` checks before placing).

  Cheap per rule, but **not** cheap per call: seeding `chain` with a rule handle joins
  that rule over the whole fact extent, so re-chaining a rule that released nothing
  costs one firing — and one level-6 exception query — per fact it has ever matched.
  Handing it every rule the pass touched is therefore quadratic in a rule's firing
  count all on its own, which is why the caller passes the *released* rules rather than
  the queued ones.

  `chain`, not `chain-all`: the violations ledger is scoped to the caller's run and
  must not be cleared from inside settling."
  [kb rule-handles]
  (let [live (filter (fn [rh]
                       (let [rsx (p/get-sentex (:records kb) rh)]
                         (and rsx (rules/rule? rsx) (rules/forward-sentex? rsx)
                              (jtms/in? (:tms kb) rh))))
                     rule-handles)]
    (when (seq live) (chain/chain kb live nil))))

(defn rechain-seeds
  "Re-derive from `seeds` — datum handles a teardown put back on the agenda.  The one
  caller is `special/resubsumption-seeds`: a firing names *one* witness for the `genl`
  path it subsumed through, so removing that witness sweeps the conclusion even when
  the reachability survives, and the facts under the edge have to be re-joined to get
  it back.  Filtered to what is still stored and believed, since the sweep that
  produced them may also have collected some.

  `chain`, not `chain-all`, for the same reason `rechain-exception-rules` uses it: the
  violations ledger is scoped to the caller's run and must not be cleared from inside
  settling."
  [kb seeds]
  (let [live (filter (fn [h] (and (p/get-sentex (:records kb) h) (jtms/in? (:tms kb) h)))
                     seeds)]
    (when (seq live) (chain/chain kb live nil))))

;; ---- exposure: the clash no single writer could see ----------------------
;;
;; The definitional checks are scoped to the writer's own cone, so two memberships
;; each admissible where stated can still be a real contradiction: some context
;; sees both of them *and* a disjointness separating their types.  Seeing a clash
;; and being blamed for one are different questions — the writer is refused only on
;; grounds it can see, and the joint question is answered here, at settle, as a
;; `:disjoint` entry in the violations ledger.  Settle is the route-agnostic point:
;; a membership arriving, a declaration arriving, a genl or genlContext edge moving,
;; and a belief revival all expose the same clash, and reporting only the route that
;; happened to run last would read as arbitrary.
;;
;; **Narrowed to the settle's moved region, like every other settle mechanism.**
;; Only a believed ingredient entering the region can newly expose a clash, so the
;; candidate terms are read off `jtms/touched` — never a KB scan — and the whole
;; pass is behind an O(1) gate (no disjoint pairs and no metatypes ⇒ nothing could
;; ever be exposed).  The ledger is append-only: retracting the ingredient that
;; exposed a clash does not withdraw the entry, and an ingredient that leaves and
;; revives files it again — each exposure is an event, stamped with its run.

(defn- believed-at-arg1
  "The believed, positive sentexes posted on `term`'s **argument-1 root** — one posting
  read per term, and the read every partner rule in this namespace goes through.

  A partner is what a sentex could clash *with*, and all three arbitrable kinds name
  theirs by an argument in position 1: a second membership of the same term, a second
  filler of the same functional slot, the converse of an asymmetric claim.  So one read
  serves the exposure pass, the retroactive sweeps and the arbitration vantages alike,
  and a narrowing applied to one of them is applied to all.

  A non-symbol has no root to read — a number or a compound is not an indexable term —
  and comes back empty rather than as a scan."
  [kb term]
  (when (symbol? term)
    (into [] (comp (keep #(p/get-sentex (:records kb) %))
                   (filter #(jtms/in? (:tms kb) (:id %)))
                   (filter #(= :true (:truth %))))
          (p/sentexes-with-arg (:index kb) 1 term))))

(defn- believed-memberships
  "The believed positive unary memberships of `x`, as `[type context handle]` triples,
  in content order.  The handle is what lets a caller tell an *arbitrated* pair from an
  exposed one — the same two memberships, asked about by two different mechanisms."
  [kb x]
  ;; `compare` on the symbols directly: the keyfn runs per comparison, so building two
  ;; Strings and a vector in it allocated three objects per comparison per candidate
  ;; term of the budgeted sweep.  Symbols are Comparable and order by ns then name,
  ;; which is the same content order the Strings gave.
  (sort (fn [[t1 c1] [t2 c2]]
          (let [r (compare t1 t2)] (if (zero? r) (compare c1 c2) r)))
        (into []
              (keep (fn [s]
                      (let [sen (:sentence s)]
                        (when (and (sequential? sen) (= 2 (count sen))
                                   (symbol? (first sen))
                                   (= x (second sen)))
                          [(first sen) (:context s) (:id s)]))))
              (believed-at-arg1 kb x))))

(defn- exposure-probes
  "The two questions the sweep asks about a *pair* of held memberships, memoized for
  the life of one pass: is this pair of types disjoint at all, and — if so — which
  contexts see the whole clash.

  Both are pure functions of the types and their contexts, and of a taxonomy that does
  not change while a settle runs.  The term is in the reported *message* and nowhere
  else in the answer, so thousands of individuals holding the same two types in the
  same two contexts ask one question rather than thousands.  That is the whole
  point: candidates are counted in instances, but distinct type/context pairs are
  counted in vocabulary.

  The visibility answer is also **gated on the question it is about to search for**,
  and that is what makes the pass affordable rather than merely cheaper.  The search
  behind it is a derivation enumeration — `disjointness-witnesses` is one witness per
  ancestor *path* per separated pair per supporter choice, exponential in a
  multiply-inheriting hierarchy — and a pair that turns out **not** to be jointly
  visible exhausts every one of them to discover it.  That is the case a large ontology
  is mostly made of, and it is unbounded.

  But whether any witness can succeed is answerable without enumerating one.  A
  context K sees a complete derivation exactly when the *scoped* `disjoint? t1 t2 K`
  holds: the scoped read walks only edges some believed supporter asserts from K's
  cone, so it is true precisely when some genl path to each separated type, and the
  separating declaration, are all visible from K.  So the gate is `∃K ∈
  common-descendants(c1, c2)` proving it — the same predicate the enumeration is
  looking for, computed off the cached closures.

  The enumeration is kept for the *answer*, because the entry reports which contexts
  the clash is visible from and that is the witness's own maximal common descendants.
  It now runs only when it is known to succeed, so it stops at a witness rather than
  running out of them.  Witnesses are deduped on the way in: several derivations
  routinely impose the same set of context choices, and the answer depends on the set
  alone."
  [tax]
  (let [dj  (volatile! {})
        vis (volatile! {})
        memo (fn [v k f]
               (if-let [e (find @v k)]
                 (val e)
                 (let [r (f)] (vswap! v assoc k r) r)))]
    {:disjoint?
     (fn [t1 t2] (memo dj [t1 t2] #(tax/disjoint? tax t1 t2)))
     :visible-from
     (fn [t1 c1 t2 c2]
       (memo vis [t1 c1 t2 c2]
             #(when (some (fn [k] (tax/disjoint? tax t1 t2 k))
                          (tax/common-descendants tax [c1 c2]))
                (some (fn [w]
                        (let [m (tax/maximal-common-descendant-contexts
                                 tax (into [c1 c2] w))]
                          (when (seq m) m)))
                      (distinct (tax/disjointness-witnesses tax t1 t2))))))}))

(defn- exposed-clashes-for-term
  "The jointly-visible disjointness clashes `x`'s believed memberships form, among
  the pairs `focus` implicates: `:all`, or a small set of type **roots** — a pair
  counts when either held type sits at-or-below one (tested through the memoized
  global closure, never by materializing a root's down-closure).  A standing clash
  whose ingredients did not move is therefore not re-examined, let alone re-filed.
  For each implicated pair of held types, the **global** `disjoint?` is the
  monotone ceiling (no reader can see a disjointness the whole edge set does not
  hold), and a pair under it is exposed iff some witness derivation's contexts
  share a common descendant with the two memberships' own — the first such witness
  wins, and the maximal common descendants are the entry's `:visible-from`.  Both
  of those are asked through `probes`, which memoizes them per pair for the pass.

  The held types' up-closures are read once each rather than once per pair: `focus`
  is tested against every pair a term's memberships form, which is quadratic in them
  where the closures are not."
  [kb x focus {:keys [disjoint? visible-from]} arbitrated]
  (let [tax (:taxonomy kb)
        ms  (believed-memberships kb x)
        gs  (when (not= :all focus) (mapv (fn [[t _]] (tax/genls tax t)) ms))
        implicated? (fn [i j]
                      (or (= :all focus)
                          (let [g1 (nth gs i) g2 (nth gs j)]
                            (boolean (some #(or (contains? g1 %) (contains? g2 %))
                                           focus)))))]
    (for [i (range (count ms))
          j (range (inc i) (count ms))
          :let  [[t1 c1 h1] (nth ms i)
                 [t2 c2 h2] (nth ms j)]
          :when (and (not= t1 t2)
                     (implicated? i j)
                     ;; a pair `settle` arbitrated is not *exposed* — it is decided, and
                     ;; reporting it here as well would have the ledger and
                     ;; `contradictions` both claim the same clash while meaning
                     ;; different things by it
                     (not (contains? arbitrated #{h1 h2}))
                     (disjoint? t1 t2))
          :let  [mx (visible-from t1 c1 t2 c2)]
          :when mx]
      {:violation :disjoint
       :detail    {:term         x
                   :held         [[t1 c1] [t2 c2]]
                   :visible-from mx
                   :message      (str "disjointness clash exposed: " x " holds " t1
                                      " (in " c1 ") and " t2 " (in " c2
                                      "), jointly visible from " (pr-str (vec (sort-by str mx))))}})))

(def ^:dynamic *rebuilding?*
  "Is this settle **restoring** a KB rather than reacting to a change to one?

  Bound by `core/recover`, and it turns the exposure pass off.  That pass reports the
  disjointness clashes the settle's moved region *newly* makes jointly visible — two
  memberships each admissible where written, contradictory from a context below both —
  and on a rebuild the claim is vacuous: nothing is newly visible, the whole KB is
  arriving at once because it was already there.  Left on, the region is every stored
  sentex and a bounded incremental check becomes an unbounded full audit: 27% of an
  OpenCyc import, silently, because the membership route is exact and unbudgeted (one
  probe per membership) and a rebuild's region holds every membership there is.

  Which is not to say the audit is worthless — it is the same question asked of the
  whole KB rather than of a change to it.  But it is a *choice*, and paying it inside
  every `recover` and `reindex` is not one anybody made."
  false)

(def ^:dynamic *exposure-instance-budget*
  "How many candidate instances one settle's exposure pass will enumerate for the
  extent-sweeping routes — a separating declaration, a metatype membership, a genl
  edge, and a genlContext edge each implicate every instance below their types (or
  in their cone), and on a large corpus that is the extent, not the region.  A
  sweep cut short files a single `:exposure-truncated` entry naming its trigger, so
  the cap is never silent.  The membership route is exact and unbudgeted — it is
  O(1) per moved membership, and it is the route ordinary writes take."
  4096)

(defn- instances-below
  "The terms holding a believed membership in any subtype of `types` — the
  candidates a separating declaration or a new genl edge can put in a clash.  Lazy,
  so a budgeted consumer realizes only what it takes.  The global down-closure on
  purpose: an over-approximated candidate merely checks and yields nothing."
  [kb types]
  (let [tax (:taxonomy kb)]
    (for [t     types
          :when (symbol? t)
          t'    (tax/specs tax t)
          s     (keep #(p/get-sentex (:records kb) %)
                      (p/sentexes-with-functor (:index kb) t'))
          :when (and (jtms/in? (:tms kb) (:id s))
                     (= :true (:truth s))
                     (= 1 (count (rest (:sentence s))))
                     (symbol? (second (:sentence s))))]
      (second (:sentence s)))))

(defn- members-in-cone
  "The membership terms stored in the contexts `sub` now sees — the candidates a
  genlContext edge's visibility move can newly put in joint sight.  Lazy, for the
  same budgeted consumer."
  [kb sub]
  (let [tax (:taxonomy kb)]
    (for [c     (tax/context-up tax sub)
          s     (keep #(p/get-sentex (:records kb) %)
                      (p/sentexes-in-context (:index kb) c))
          :let  [sen (:sentence s)]
          :when (and (jtms/in? (:tms kb) (:id s))
                     (= :true (:truth s))
                     (sequential? sen) (= 2 (count sen))
                     (symbol? (first sen)) (symbol? (second sen)))]
      (second sen))))

;; ---- what a declaration reaches back over --------------------------------
;;
;; A declaration changes what already-stored content *means*, so the settle that
;; admits one has to re-examine content written before it — or the KB would answer
;; differently depending on whether the separation or the memberships were written
;; first, which is the invariant docs/nmtms.md opens with.
;;
;; The reach is two questions, and keeping them apart is what makes a bounded sweep
;; buy real coverage:
;;
;;   * **what to enumerate** — one record fetch per instance below the declared
;;     types, which on a real ontology is the *extent* rather than the region.  This
;;     is what `*exposure-instance-budget*` bounds.
;;   * **what an enumerated term is a candidate for** — a `believed-memberships`
;;     read plus a probe per pair it forms, and behind that a witness enumeration.
;;     Far more expensive per term, and needed only for the terms that could really
;;     be convicted.
;;
;; The extent below one side of a separation is **not** the candidate set: a
;; disjointness clash needs a membership from *each* side, so the terms `(disjoint A
;; B)` implicates are those below A **and** below B.  Enumerating the union and
;; calling all of it candidates spends the budget on terms that were never going to
;; convict, and on a large corpus the budget runs out before the first real one.

(defn- spec-closure
  "The union of the down-closures of `types` — the type labels a membership must carry
  to sit below any of them."
  [tax types]
  (into #{} (comp (filter symbol?) (mapcat #(tax/specs tax %))) types))

(defn- extent-size
  "How many **stored** facts sit under an already-computed spec `closure` —
  `count-with-functor` per member, so one side of a separation can be sized without
  enumerating it.

  Stored rather than believed, and over whatever arity the functor has: this only
  picks which side to walk, and a miscount costs a worse choice of side, never an
  answer."
  [kb closure]
  (transduce (map #(p/count-with-functor (:index kb) %)) + 0 closure))

(defn- holds-below?
  "Does `term` hold a believed unary membership whose type is in `closure`?  Read off
  the argument-1 root — the posting `kb/types-of` reads — so it is one seek per term
  rather than a walk of the other side's extent."
  [kb closure term]
  (boolean
   (some (fn [h]
           (when-let [s (p/get-sentex (:records kb) h)]
             (let [sen (:sentence s)]
               (and (sequential? sen) (= 2 (count sen))
                    (contains? closure (first sen))
                    (= :true (:truth s))
                    (jtms/in? (:tms kb) (:id s))))))
         (p/sentexes-with-arg (:index kb) 1 term))))

(defn- holds-two-members?
  "Does `term` hold believed memberships below **two distinct** members of a metatype?
  `owner` is a `type -> #{member}` map over the members' spec closures, so one pass
  over the term's own argument-1 root answers it.

  Stops at the second, which is the whole question — a term below fifty members is as
  much a pair as a term below two, and counting them all would be a record fetch each."
  [kb owner term]
  (> (count (reduce (fn [seen h]
                      (if-let [s (p/get-sentex (:records kb) h)]
                        (let [sen (:sentence s)]
                          (if (and (= 2 (count sen)) (= :true (:truth s))
                                   (jtms/in? (:tms kb) (:id s)))
                            (let [seen' (into seen (owner (first sen)))]
                              (if (> (count seen') 1) (reduced seen') seen'))
                            seen))
                        seen))
                    #{}
                    (p/sentexes-with-arg (:index kb) 1 term)))
     1))

(defn- member-owners
  "`type -> #{metatype member}` over the members' spec closures, so one pass over a
  term's memberships says how many distinct members it holds.  Built once per
  declaration rather than per candidate."
  [tax members]
  (reduce (fn [m mem]
            (reduce (fn [m t] (update m t (fnil conj #{}) mem)) m (tax/specs tax mem)))
          {} (filter symbol? members)))

(defn- pairable?
  "Could `term` be half of a clash at all?  A clash needs two facts about it at
  argument 1, so the O(1) cardinality of its own argument root answers it.

  Deliberately **over-approximating**, like `could-clash?`: the root is not
  belief-filtered and spans every predicate and either polarity, so a count above one
  is only evidence that a pair is possible — one is proof that it is not."
  [kb term]
  (> (p/count-with-arg (:index kb) 1 term) 1))

(defn- two-sided-reach
  "The reach of a separation between the type sets `as` and `bs`: the terms holding a
  believed membership below **both**, which is what a clash between them needs.

  The **cheaper side is enumerated** — sized off the roots, so choosing costs no walk —
  and each of its terms is probed against the other side's closure.  Work is `min` of
  the two extents where sweeping below either side paid their sum, and every survivor
  genuinely holds one of each rather than merely sitting under one of them.

  A side whose spec closure is **empty** has no membership below it and therefore no
  clash above it, so the reach is empty outright.  That is the case a separation naming
  a non-symbol names — OpenCyc declares thousands against a reified NAT like `(AbnormalFn
  chromosome)` — and it is said here rather than left to fall out of the sizing
  arithmetic picking the empty side, because what makes it true is a coupling two
  functions away: `believed-memberships` reads a clash half only from a sentence whose
  functor is a symbol, so a compound-functor membership could not be one end of a pair
  even if it were enumerated."
  [kb as bs roots]
  (let [tax (:taxonomy kb)
        ca  (spec-closure tax as)
        cb  (spec-closure tax bs)]
    (if (or (empty? ca) (empty? cb))
      {:enumerate nil :keep? (constantly false) :roots roots}
      ;; the cheaper side's **roots** are what is enumerated (`instances-below` walks
      ;; each root's closure itself, so handing it the closure would enumerate a term
      ;; once per ancestor path and spend the budget on duplicates), and the other
      ;; side's **closure** is what each enumerated term is probed against
      (let [[near far] (if (<= (extent-size kb ca) (extent-size kb cb)) [as cb] [bs ca])]
        {:enumerate (instances-below kb near)
         :keep?     #(holds-below? kb far %)
         :roots     roots}))))

(defn- declaration-reach
  "What a believed declaration in the moved region puts back in question:

      {:enumerate <lazy seq of terms>   ; what the instance budget bounds
       :keep?     (fn [term] …)         ; which of them could really be convicted
       :roots     (#{type …} | :all)}   ; the type roots to focus a candidate on

  `nil` when the sentence declares nothing that reaches back over stored content.

  Per kind, and each `keep?` is **exact for its own trigger** — it never drops a term
  the declaration could put in a clash:

  * `(disjoint A B)` — the terms below *both* sides.  The cheaper side is enumerated
    (sized off the roots, so choosing costs no walk) and each of its terms probed
    against the other's closure.  Work is `min` of the two extents where the union
    rule paid their sum, and every survivor is a term that genuinely holds one of
    each.
  * `(disjointMetatype M)` — the members are pairwise disjoint, so a candidate is a
    term below **two distinct members**.  Every member's extent still has to be
    enumerated (the clash may be between any two of them), but only the
    double-holders come out.
  * `(M T)`, a new member of a disjoint metatype — the terms below `T` that also hold
    one of `M`'s *other* members.
  * `(genl A B)` — `A`'s instances gain `B`'s ancestors, so the second half of a
    clash could be any other membership they hold: the O(1) `pairable?` gate is all
    that can be said without knowing which.
  * `(genlContext Sub Super)` — visibility itself moved, so the roots are `:all` and
    the same gate applies."
  [kb sen]
  (let [tax (:taxonomy kb)
        f   (nm/functor sen)]
    (case f
      disjoint
      (let [[_ a b] sen] (two-sided-reach kb [a] [b] #{a b}))

      disjointMetatype
      (let [[_ mt]  sen
            members (tax/metatype-members tax mt)
            owner   (member-owners tax members)]
        {:enumerate (instances-below kb members)
         :keep?     #(holds-two-members? kb owner %)
         :roots     (set members)})

      genl
      (let [[_ a _] sen]
        {:enumerate (instances-below kb [a])
         :keep?     #(pairable? kb %)
         :roots     #{a}})

      genlContext
      (let [[_ sub _] sen]
        {:enumerate (members-in-cone kb sub)
         :keep?     #(pairable? kb %)
         :roots     :all})

      nil)))

(defn- metatype-member-reach
  "The reach of `(M T)` where `M` is a disjoint metatype: `T` is now separated from
  every *other* member, so this is the two-sided reach between `T` and them.

  Separate from `declaration-reach` because the sentence is an ordinary unary
  membership — only the taxonomy says it declares anything at all."
  [kb mt t]
  (two-sided-reach kb [t] (disj (set (tax/metatype-members (:taxonomy kb) mt)) t) #{t}))

;; ---- definitional clashes as nogoods -------------------------------------
;;
;; Disjointness, functionality and asymmetry each convict by naming a **second believed
;; sentex**, which is a nogood in exactly the sense `negation-nogoods` produces one.  So
;; they are arbitrated here rather than refused at the door or dropped at the firing:
;; the weaker side is defeated, an equal defeasible pair is a represented dilemma, and
;; an equal known-true pair is the irreducible clash `conflicts` reports.  One theory of
;; contradiction, whichever door the content came through (docs/nmtms.md).
;;
;; Discovery is **a function of current state, never an accumulation of past ones**, and
;; that is what makes it order-independent.  A pair is found by re-running the
;; definitional checks over the settle's moved region, so which sentence arrived last
;; cannot change the answer:
;; whichever of the two memberships, or the declaration separating them, or the `genl`
;; edge closing it, moved into the region this settle, the pair is re-derived from
;; current belief.  A pair whose ingredient is retracted or defeated simply stops being
;; re-derived, and a revived one comes back — the same discipline belief itself follows.
;;
;; The answer for a pair is *carried forward* when this settle cannot have changed it —
;; neither member moved and the vocabulary deciding clash-ness did not either — which is
;; a memo on a recomputation, not an accumulation: the carried value is exactly what
;; re-deriving would produce.  Without it a settle costs one check per standing pair,
;; and since a settle runs after every mutation that is quadratic in the clashes a load
;; creates.
;;
;; The candidate set is the region, plus what a *declaration* in the region implicates
;; about content already stored: `(disjoint dog cat)` arriving after both memberships
;; has to reach them, or the answer would depend on whether the separation was written
;; first.  Those sweeps draw on the same instance budget the exposure pass uses, and
;; behind the same O(1) gate — a KB that separates nothing pays one set read.

(def ^:private clash-declaration-functors
  "Sentence functors whose arrival implicates content already stored.  A membership or
  a relation fact needs no entry here: it is its own candidate, found in the region."
  '#{disjoint disjointMetatype genl genlContext functional asymmetric})

(defn- metatype-member?
  "Is `sen` a term **joining** a disjoint metatype — `(M T)` where the taxonomy already
  holds `M` as one?

  The one implicating declaration a vocabulary of functors cannot name, which is why it
  is a predicate beside the set above rather than an entry in it: the sentence is an
  ordinary unary membership and its functor is whatever the metatype happens to be
  called, so only the taxonomy says it declares anything at all.  What it declares is
  a separation — `T` is now disjoint from every member already there, and the memberships
  those members' instances hold were admissible until this arrived.

  `exposure-candidates` reads the taxonomy the same way for the same sentence.  The two
  passes answer one question about one KB, so a shape one of them reaches and the other
  does not is a pair *reported* as visible by one mechanism and never *decided* by the
  other."
  [kb sen]
  (and (sequential? sen)
       (= 2 (count sen))
       (let [f (nm/functor sen)]
         (and (symbol? f) (symbol? (second sen))
              (tax/disjoint-metatype? (:taxonomy kb) f)))))

(defn- membership-sentexes
  "The believed unary-membership sentexes of `term` — its candidate side of a
  disjointness pair.  Read off the argument root, so it is one posting per term."
  [kb term]
  (filter #(= 2 (count (:sentence %))) (believed-at-arg1 kb term)))

(defn- predicate-sentexes
  "The believed facts of predicate `p` — the candidates a `functional` or `asymmetric`
  declaration implicates when it arrives after them."
  [kb pred]
  (when (symbol? pred)
    (for [s     (keep #(p/get-sentex (:records kb) %)
                      (p/sentexes-with-functor (:index kb) pred))
          :when (and (jtms/in? (:tms kb) (:id s)) (= :true (:truth s)))]
      s)))

(defn- declaration-implicates
  "The stored sentexes a believed declaration in the moved region puts back in
  question.  Lazy, so the budgeted caller realizes only what it takes.

  The type-separating declarations read `declaration-reach`, the same candidate rule
  the exposure pass runs — the two answer one question about one KB, so a pair one of
  them reaches and the other does not would be reported as *visible* by one mechanism
  and *decided* by the other depending on which route ran.  `functional` and
  `asymmetric` have no type reach: they implicate the extent of the predicate they
  name, which is already exactly its candidates.

  `budget` bounds the **enumeration**, and `:enumerated` reports what it spent — never
  the survivors.  Budgeting survivors instead would make a `keep?` that rejects
  everything walk the whole extent looking for one, which is precisely the shape a
  large ontology is mostly made of."
  [kb sen budget]
  (let [[f a] sen
        ;; both type-separating shapes end the same way: bound the enumeration, keep the
        ;; terms that could really be convicted, and take their memberships
        implicated (fn [{:keys [enumerate keep?]}]
                     (let [terms (into [] (take budget) enumerate)]
                       {:enumerated (count terms)
                        :sentexes   (mapcat #(membership-sentexes kb %) (filter keep? terms))}))]
    (cond
      (contains? '#{disjoint disjointMetatype genl genlContext} f)
      (implicated (declaration-reach kb sen))

      (contains? '#{functional asymmetric} f)
      (let [ss (into [] (take budget) (predicate-sentexes kb a))]
        {:enumerated (count ss) :sentexes ss})

      ;; `(M T)` — the shape the taxonomy names rather than the vocabulary, and a `cond`
      ;; rather than a `case` arm for exactly that reason: there is no functor to
      ;; dispatch on
      (metatype-member? kb sen)
      (implicated (metatype-member-reach kb f a))

      ;; total on purpose: the caller decrements its budget by `:enumerated`, so a
      ;; functor added to `clash-declaration-functors` without an arm here would
      ;; otherwise subtract nil rather than sweep nothing
      :else {:enumerated 0 :sentexes nil})))

(defn- content-order
  "Sentexes in **content** order — the sentence, then the context.

  Every budgeted sweep over a moved region walks in this order, `report-arity-reach!`'s
  `sorted-set` of predicates included.  A region arrives as a handle *set*, and a handle
  is allocation order, so a sweep that walked it as it came would spend one
  `*exposure-instance-budget*` on different members depending on which order the same
  knowledge arrived in — and past the budget the nogoods minted, and therefore what the
  KB believes, would differ with it.  Order independence is a property, not a tendency
  (docs/nmtms.md)."
  [sentexes]
  (sort-by (juxt #(pr-str (:sentence %)) #(str (:context %))) sentexes))

(defn- clash-candidates
  "The believed sentexes whose definitional checks this settle re-runs.

  **The moved region always.**  That is the content a rule firing just placed, and it
  is the route `place-conclusion` hands here: a conclusion that clashes is admitted and
  arbitrated rather than dropped, so the pair has to be found in the same settle.

  **The retroactive sweeps only under this KB's constraint policy**
  (`checks/arbitrating?` — `:arbitrate`, or the process default).  A *declaration*
  arriving — a separation, a `genl` edge closing one, a predicate property — puts
  content stored long before it back in question, and content that was admitted by an
  `assert` the declaration had not yet arrived to refuse.  Arbitrating those is the
  other half of the same policy: under `:refuse`, a clash nobody could see when they
  wrote it stays the exposure pass's business (a report naming the contexts it is
  visible from, `expose-clashes!`), and only content this settle *derived* is
  arbitrated.  Under `:arbitrate`, every route agrees and a violating set lands on the
  same answer in every arrival order.

  **Plus both members of every pair already known to clash.**  `contradictions` is
  recomputed from scratch each settle, and the region is only what *this* settle moved —
  so a standing dilemma whose ingredients sat still would be reported once and then
  silently vanish on the next unrelated assert.  `:clashes` is the maintained candidate
  set that fixes it, in the same spirit as `:opposed`: membership is keyed on **storage**
  (a pair survives while both records do, defeated or not, so a revival is re-reported),
  and whether it is currently a nogood is recomputed from belief every time.  Which
  pairs the region happens to surface is therefore no longer what is reported — it is
  only how a pair is *discovered*, and discovery accumulates.

  **Plus `revisit`** — handles of previously-known pairs the caller has decided it can
  no longer take on trust.  Which those are is `clash-nogoods`' question, not this one's.

  The sweep half is budgeted exactly as the exposure pass's is — over-sweeping costs
  re-checks, under-sweeping would miss a clash."
  [kb touched revisit]
  (let [believed (comp (keep #(p/get-sentex (:records kb) %))
                       (filter #(jtms/in? (:tms kb) (:id %)))
                       (filter #(= :true (:truth %))))
        ;; `revisit` ahead of `touched` and each half in content order: the sweep below
        ;; is budgeted, so which members it reaches must not depend on the handle order
        ;; either set came back in (`content-order`)
        moved (into (vec (content-order (into [] believed revisit)))
                    (content-order (into [] believed touched)))
        left  (volatile! (long *exposure-instance-budget*))
        swept (when (checks/arbitrating? kb)
                (mapcat (fn [s]
                          (let [sen (:sentence s)]
                            (when (and (sequential? sen)
                                       (or (contains? clash-declaration-functors (nm/functor sen))
                                           (metatype-member? kb sen))
                                       (pos? (long @left)))
                              (let [{:keys [enumerated sentexes]}
                                    (declaration-implicates kb sen (long @left))]
                                (vswap! left - enumerated)
                                sentexes))))
                        moved))]
    (into (set moved) swept)))

(def ^:dynamic *incremental-clashes*
  "Discover definitional clashes **incrementally** — the default, and what a KB runs.

  Incremental discovery is three narrowings of one exhaustive question, *which pairs of
  believed sentexes clash*: only the settle's moved region and the pairs already known
  are examined (`clash-candidates`), only a sentex that could pair at all is checked
  (`could-clash?`), and a known pair neither of whose members moved is carried forward
  rather than re-derived (`clash-nogoods`).  Each is a claim that what it skips could
  not have changed the answer — and a wrong one is a silently *different* answer, never
  a crash: a dilemma that goes unreported, or a defeat that is not applied.

  Bound to `false`, every believed sentex is a candidate on every settle and nothing is
  carried, which is the definition the three narrowings approximate.  That is the
  reference `clash_oracle_test` proves them against, and it is O(believed) checks per
  settle — a measurement harness, not a mode to run a KB in."
  true)

(defn- all-believed
  "Every believed, positive, stored sentex — the exhaustive candidate set
  `*incremental-clashes*` false substitutes for the region."
  [kb]
  (into [] (comp (keep #(p/get-sentex (:records kb) %))
                 (filter #(= :true (:truth %))))
        (jtms/in-datums (:tms kb))))

(defn- clash-vocabulary
  "Everything a clash's existence depends on **beyond the two sentexes themselves**: the
  separations, the metatypes whose members separate each other, the two predicate
  properties, and the generation of the two closures a separation is read through.

  Cheap to compute and cheap to compare — four small sets and two counters, none of them
  proportional to the KB — which is what lets `clash-nogoods` separate *nothing that
  decides clash-ness has moved* from *something has*, without re-deriving anything in
  order to find out."
  [tax]
  [(tax/disjoint-pairs tax)
   (tax/disjoint-metatypes tax)
   (tax/props tax :functional)
   (tax/props tax :asymmetric)
   (tax/relation-gen tax :genl)
   (tax/relation-gen tax :genlContext)])

(defn- could-clash?
  "Could this believed sentex be one half of a definitional clash?  A cheap,
  deliberately **over-approximating** gate in front of the real check, which is a full
  `constraint-problem` pass and far too expensive to run per sentex of a rebuild's
  region.

  Two shapes can pair, and each is answered without a record fetch:

  * a **unary membership** `(T x)`, which needs `x` to hold a second membership to
    clash with — read as the O(1) cardinality of `x`'s argument-1 root rather than by
    walking it.  The root spans every predicate and either polarity and is not
    belief-filtered, so a count above one is only evidence that a pair is *possible*;
    one is proof that it is not.
  * a **binary fact** whose predicate is declared `functional` or `asymmetric`, both
    O(1) property reads.

  Everything else — a declaration, a rule, an n-ary fact of an ordinary predicate — can
  convict nothing here and is dropped before the check runs."
  [kb s]
  (let [sen (:sentence s)]
    (and (sequential? sen)
         (symbol? (nm/functor sen))
         (let [as (rest sen)]
           (case (count as)
             1 (let [x (first as)]
                 (and (symbol? x) (> (p/count-with-arg (:index kb) 1 x) 1)))
             2 (let [tax (:taxonomy kb) f (nm/functor sen)]
                 (or (tax/has-prop? tax :functional f)
                     (tax/has-prop? tax :asymmetric f)))
             false)))))

(defn- partner-contexts
  "The contexts holding a believed sentex that could be the **far half** of a pair with
  `s` — its term's other memberships for a separation, the other fillers of the slot for
  a `functional` predicate, the converse for an `asymmetric` one.

  Read off the argument-1 roots (`believed-at-arg1`), which is one posting per term and
  the same rule `exposed-clashes-for-term` selects the pairs it probes with.  For a
  binary fact both arguments are read and the postings narrowed to the sentence's own
  functor: a functional partner shares argument 1, an asymmetric one holds it in
  argument 2, and neither can be a fact of some other predicate.

  Over-approximating on purpose, exactly as `could-clash?` is: a context named here that
  turns out to convict nothing costs one check that finds nothing, where a context left
  out is a pair nobody weighs.

  **Exact and unbudgeted**, for the reason `*exposure-instance-budget*` gives about the
  membership route it bounds nothing of: this is O(1) postings per candidate rather than
  an extent sweep, and the candidate set is the settle's region, which the budget already
  bounds where it came from a declaration reaching back.  There is no enumeration here
  for a budget to cut short, and cutting one short would drop a pair rather than defer
  it."
  [kb s]
  (let [sen (:sentence s)
        as  (vec (nm/args sen))
        own (:id s)]
    (case (count as)
      1 (into #{} (comp (remove #(= own (:id %))) (map :context))
              (membership-sentexes kb (first as)))
      2 (let [f (nm/functor sen)]
          (into #{} (comp (remove #(= own (:id %)))
                          (filter #(= f (nm/functor (:sentence %))))
                          (map :context))
                (concat (believed-at-arg1 kb (first as))
                        (believed-at-arg1 kb (second as)))))
      #{})))

(defn- clash-vantages
  "The contexts `s`'s definitional question is asked **from**, beyond its own.

  The checks are scoped to the context they are asked in, and rightly — a context is
  convicted only on grounds it can see (`checks/disjoint-problems`).  But a pair whose
  halves sit in two contexts is visible from neither of them alone: `GenContext` is
  general, `SpecContext` sees it, and only `SpecContext` has both memberships in view.
  Asking each arriving sentex from its own context therefore answers the pair's question
  from whichever side happened to arrive last, and one of the two sides cannot answer it
  at all — so the same knowledge lands on a defeat or on two coexisting claims according
  to the order it was written in.

  This chooses the **asker**, and widens nothing: each vantage is a context that already
  sees both halves, and what it convicts on is what it can see.  The vantage is the
  *maximal* common descendant rather than any of them, which is the conservative end —
  the least specific context that has the whole clash in view is the one whose grounds
  the arbitration rests on, so a narrow context's separation never reaches back over
  a general claim it was never about.  Where one context sees the other the maximum is
  that context, which is the ordinary case and one `sees?` probe."
  [kb s]
  (let [tax (:taxonomy kb)
        c   (:context s)]
    (into #{}
          (comp (remove #(= c %))
                (mapcat #(tax/maximal-common-descendant-contexts tax [c %]))
                (remove #(= c %)))
          (partner-contexts kb s))))

(defn- clash-askers
  "`s`'s own context, then the vantages that see a pair it could form, in content order.

  Ordered rather than a set, because the checks run in it and the entries are collected
  in that order; each is keyed on the handle pair and collapses whichever vantage found
  it, so the order decides nothing — but it may not be the order a posting came back in
  either, which is arrival order.

  **The vantages run under the KB's constraint policy** (`checks/arbitrating?`), like the
  retroactive sweeps and for the same reason.  A pair split across a visibility edge was
  admissible to both writers — neither could see the other half — so under `:refuse` it
  is exactly the clash nobody could see when they wrote it, and that is the exposure
  pass's business: a ledger entry naming the contexts it is visible from, with belief
  untouched (`disjoint_test/a-general-context-may-be-given-what-a-specific-one-forbids`
  is the acceptance criterion).  Under `:arbitrate` every route agrees instead, and the
  pair is weighed wherever it can be seen whole.  A KB under `:refuse` therefore pays
  nothing here: the gate is read before the argument roots are."
  [kb s]
  (cons (:context s)
        (when (checks/arbitrating? kb) (sort-by str (clash-vantages kb s)))))

(defn- clash-nogoods
  "The definitional clashes the settle's moved region holds, as nogoods.

  Each is re-derived by asking the very checks the assert path asks
  (`checks/arbitrable-violation`), so the two can never drift about what constitutes a
  clash — the discovery here and the refusal there read one implementation.  It is asked
  from every context that can see the pair (`clash-askers`), never only from the
  arriving sentex's own.

  **A pair is found once, however many of its members the region holds.**  Both sides
  convict each other, so a region holding both mints the entry twice; and which sides
  the region holds is a property of the arrival order, so a set that told the two
  entries apart would report one clash or two depending on it — order-dependence in
  the *reporting* even while belief was stable, which is what
  `constraint_nogood_test`'s permutation cases catch.  So the entry is keyed on the
  handle pair and made a function of the **pair's content alone**: the two sentences
  are ordered by their printed form rather than by which side was walked, and a pair
  reached from both sides collapses to one identical map.

  Priority sits **above** every rebuttal: a definitional clash is a violation of what
  the KB says the vocabulary *means*, where `S` against `(not S)` is two claims about
  the world.  `negation-nogoods` ranks 1–2, so these rank 3–4 and a solver handed both
  satisfies the definitional ones first."
  [kb touched]
  (let [tms   (:tms kb)
        recs  (:records kb)
        vocab (clash-vocabulary (:taxonomy kb))
        prev  @(:clashes kb)
        ;; A pair already known to clash is re-derived only when this settle could have
        ;; changed the answer: one of its members moved (belief is computed from the
        ;; relabelled region, so an untouched member's label is exactly what it was), or
        ;; the vocabulary that decides clash-ness moved.  Everything else is carried
        ;; forward from the last settle verbatim — its `:priority` reads defeat classes
        ;; that did not move either.
        ;;
        ;; Re-deriving all of them is what `*incremental-clashes*` false does, and it is
        ;; correct and quadratic: a settle runs after every mutation, so an
        ;; `arbitrable-violations` call per standing pair per settle makes loading N
        ;; clashing facts O(N²) — 36ms per assert at 300 standing clashes against 8ms at
        ;; 50, the shape docs/nmtms.md records for the defaults phase.  The memo is what
        ;; keeps the cost proportional to the region; `lein perf` is what holds it there.
        stale?  (or (not *incremental-clashes*) (not= vocab (:vocab prev)))
        stored? (fn [pr] (every? #(some? (p/get-sentex recs %)) pr))
        live    (into #{} (filter stored?) (:pairs prev))
        moved?  (let [t (set touched)] (fn [pr] (boolean (some t pr))))
        revisit (if stale? live (into #{} (filter moved?) live))
        carried (if stale?
                  {}
                  (into {} (filter (fn [[pr _]] (and (contains? live pr)
                                                     (not (contains? revisit pr)))))
                        (:nogoods prev)))
        cands   (if *incremental-clashes*
                  (clash-candidates kb touched (into #{} (mapcat identity) revisit))
                  (all-believed kb))
        entries
        (mapcat (fn [s]
                  (when (or (not *incremental-clashes*) (could-clash? kb s))
                    (mapcat
                     (fn [asker]
                       (keep (fn [v]
                               (let [opp (:opposing-handle v)]
                                 (when (and (not= opp (:id s)) (jtms/in? tms opp))
                                   (let [other (:sentence (p/get-sentex (:records kb) opp))
                                         [a b] (sort-by pr-str [(:sentence s) other])]
                                     {:nogood   #{(:id s) opp}
                                      :kind     (:type v)
                                      :priority (+ 2 (max (strength/rank-of
                                                           (jtms/defeat-class tms (:id s)))
                                                          (strength/rank-of
                                                           (jtms/defeat-class tms opp))))
                                      :sentence (list 'contradicts a b)}))))
                             (checks/arbitrable-violations kb (:sentence s) asker)))
                     (clash-askers kb s))))
                cands)]
    ;; one entry per handle pair, chosen by content — two sides can convict on
    ;; different `:kind`s in principle, and which of them wins may not depend on
    ;; traversal
    (let [derived (into {} (map (fn [[pr es]] [pr (first (sort-by pr-str es))]))
                        (group-by :nogood entries))
          answer  (merge carried derived)
          ngs     (into #{} (vals answer))
          found   (into #{} (keys answer))]
      ;; Remember the pairs, so the next settle re-examines them whether or not its own
      ;; region happens to touch either side — and **forget the ones that have stopped
      ;; clashing**, or the set only ever grows and every settle pays an
      ;; `arbitrable-violations` call per pair the KB ever had.
      ;;
      ;; A pair is only dropped when it was actually re-examined and came back clean:
      ;; both members believed (so the checks could see them whole) and no clash
      ;; between them.  A pair with a *defeated* member is retained instead, since a
      ;; check cannot see past the defeat to say whether it would still clash, and
      ;; dropping it would mean a revival went unreported.  Anything genuinely new
      ;; re-enters through the region, which is how it was found the first time.
      (reset! (:clashes kb)
              {:vocab   vocab
               :nogoods answer
               :pairs   (into found
                              (filter (fn [pr]
                                        (or (contains? found pr)
                                            (not (every? #(jtms/in? tms %) pr)))))
                              live)})
      ngs)))

(defn- constraint-nogoods
  "`clash-nogoods`, behind the O(1) gate that makes it free for a KB declaring none of
  the three features — which is most of them, and every KB that declares none pays one
  set-emptiness read per settle.

  **Deliberately not gated on `*rebuilding?*`**, unlike the exposure pass beside it,
  and the difference is what the two produce.  Exposure files an *event* — \"this
  settle newly made that clash jointly visible\" — which is vacuous on a rebuild, where
  nothing is new because everything is arriving at once.  A nogood is **state**: belief
  depends on it, so a rebuild that skipped it would come up with the loser of a decided
  clash believed again and the dilemma unreported, and the KB would answer differently
  either side of a restart.  `could-clash?` is what keeps that affordable — on a
  rebuild the region is every stored sentex, and the gate drops all but the few that
  could possibly pair."
  [kb]
  (let [tax (:taxonomy kb)]
    (if-not (or (seq (tax/disjoint-pairs tax))
                (seq (tax/disjoint-metatypes tax))
                (seq (tax/props tax :functional))
                (seq (tax/props tax :asymmetric)))
      ;; Nothing separates anything and no predicate is declared functional or
      ;; asymmetric, so no pair can clash — which makes this the one place the whole
      ;; candidate set can be dropped rather than re-examined.  It has to be dropped
      ;; here: the gate short-circuits `clash-nogoods`, so retracting the last
      ;; separation would otherwise leave its pairs remembered with nothing ever able
      ;; to look at them again.
      (do (reset! (:clashes kb) {}) #{})
      (clash-nogoods kb (jtms/touched (:tms kb))))))

(defn- merge-focus
  "Merge one ingredient's focus into a term's — `:all`, or a small set of type
  **roots**.  Roots, never closures: `exposed-clashes-for-term` tests a held type
  against a root through the memoized global `genls`, so nothing here ever
  materializes a down-closure into the candidates map."
  [m term focus]
  (update m term (fn [f]
                   (cond (= :all f)     :all
                         (= :all focus) :all
                         :else          (into (or f #{}) focus)))))

(defn- exposure-candidates
  "`{:candidates {term focus} :truncated [sentence …]}` for the settle's moved
  region: which terms could be in a newly jointly-visible clash, and which type
  roots the moved ingredient implicates (`:all` when visibility itself moved).  Per
  ingredient kind: a membership focuses its own term on its type — exact and
  unbudgeted; a separating declaration, metatype membership, or genl edge focuses
  the instances below its types on those types; a genlContext edge focuses the
  moved cone's memberships on everything.  The extent-sweeping routes draw on one
  shared instance budget, and a trigger whose sweep is cut short is returned in
  `:truncated`."
  [kb touched]
  (let [tax    (:taxonomy kb)
        left   (volatile! (long *exposure-instance-budget*))
        trunc  (volatile! [])
        ;; `terms` is what the budget bounds — a record fetch each, and the extent
        ;; rather than the region — while `keep?` decides which of them is a
        ;; *candidate*, at a `believed-memberships` read and a pairwise probe apiece.
        ;; Bounding the first and sharpening the second is what makes a bounded sweep
        ;; buy real coverage rather than a bounded quantity of terms that were never
        ;; going to convict.  The filter runs *after* the take, so a `keep?` that
        ;; rejects everything costs the budget and not the extent.
        sweep  (fn [m sen terms keep? roots]
                 (let [n     (long @left)
                       ;; one past the budget, so `taken` says both how much was
                       ;; wanted and whether there was more.  Still realized when the
                       ;; budget is gone: a trigger whose extent is *empty* was swept
                       ;; in full by looking at nothing, and reporting it as cut short
                       ;; would inflate the count with triggers that implicate no
                       ;; instance at all (183,397 against a true 41,500 on OpenCyc).
                       taken (into [] (take (inc n)) terms)
                       cut?  (> (count taken) n)
                       seen  (if cut? (take n taken) taken)]
                   (vswap! trunc #(if cut? (conj % sen) %))
                   (vreset! left (if cut? 0 (- n (count taken))))
                   (reduce #(merge-focus %1 %2 roots) m (filter keep? seen))))]
    {:candidates
     (reduce
      (fn [m s]
        (let [sen (:sentence s)
              f   (nm/functor sen)]
          (cond
            ;; A declaration first, and `disjointMetatype` is why the order matters:
            ;; it is a *unary* sentence whose argument is a symbol, so the membership
            ;; arm below would otherwise claim it and file the metatype itself as a
            ;; term holding a type — leaving an arriving metatype declaration with no
            ;; sweep at all.
            (contains? '#{disjoint disjointMetatype genl genlContext} f)
            (let [{:keys [enumerate keep? roots]} (declaration-reach kb sen)]
              (sweep m sen enumerate keep? roots))

            (and (symbol? f) (= 1 (count (rest sen))) (symbol? (second sen)))
            (cond-> (merge-focus m (second sen) #{f})
              (tax/disjoint-metatype? tax f)
              (as-> m' (let [{:keys [enumerate keep? roots]}
                             (metatype-member-reach kb f (second sen))]
                         (sweep m' sen enumerate keep? roots))))

            :else m)))
      {}
      ;; content order, so a budgeted sweep reaches the same triggers however the region
      ;; came back — the same reason `report-arity-reach!` sorts its predicates
      (content-order
       (into []
             (comp (keep #(p/get-sentex (:records kb) %))
                   (filter #(jtms/in? (:tms kb) (:id %)))
                   (filter #(= :true (:truth %))))
             touched)))
     :truncated @trunc}))

(defn exposed-clashes
  "Every jointly-visible disjointness clash the KB **currently** holds — the whole-KB
  question, asked on demand and returning its answer rather than filing it.

  The settle pass beside this one answers a different question: what did the change
  just made *newly* expose.  That is what makes it incremental and what makes it
  vacuous on a rebuild (`*rebuilding?*`), and it leaves nobody able to ask the standing
  question — of an imported KB, whose ledger arrives empty, least of all.  So it is
  asked here instead, and by a caller who chose to.

  **Complete by construction, and cheaper than the incremental pass would be at this
  size.**  A term is a candidate iff it holds two believed memberships, so every
  candidate is found by walking the memberships themselves — no extent sweeps, hence
  no instance budget and no truncation to report.  The sweeps exist only to work out
  which *instances* a changed declaration or edge implicates; when every membership is
  already in hand they can only re-find what is already there.  Cost is the believed
  memberships, plus a pair test per term holding several, over probes memoized for the
  whole call.

  Returns the same entry shape `violations` reports (`{:violation :disjoint :detail
  {...}}`), so a caller renders both with one renderer.  Reads only: nothing is stored,
  nothing is filed, and belief does not move."
  [kb]
  (let [tax    (:taxonomy kb)
        probes (exposure-probes tax)
        terms  (into #{}
                     (comp (keep #(p/get-sentex (:records kb) %))
                           (filter #(jtms/in? (:tms kb) (:id %)))
                           (filter #(= :true (:truth %)))
                           (keep (fn [s]
                                   (let [sen (:sentence s)]
                                     (when (and (sequential? sen) (= 2 (count sen))
                                                (symbol? (first sen))
                                                (symbol? (second sen)))
                                       (second sen))))))
                     (p/sentex-ids (:records kb)))]
    (if-not (or (seq (tax/disjoint-pairs tax)) (seq (tax/disjoint-metatypes tax)))
      []                                             ; nothing separates anything
      (into [] (comp (mapcat #(exposed-clashes-for-term kb % :all probes #{}))
                     (distinct))
            (sort-by str terms)))))                  ; content order, so the answer is stable

(defn- expose-clashes!
  "File the disjointness clashes the settle's moved region newly makes jointly
  visible — behind the O(1) no-separations gate, deduped within the pass.  A sweep
  the instance budget cut short files `:exposure-truncated` naming its trigger, so
  bounded work never reads as full coverage.  Off entirely while `*rebuilding?*`,
  where *newly* has no meaning.

  `arbitrated` is the pairs this settle handed to the nogood machinery instead — those
  are *decided*, not merely visible, so they are reported by `conflicts` /
  `contradictions` and must not be filed here as well."
  [kb touched arbitrated]
  (let [tax (:taxonomy kb)]
    (when (and (not *rebuilding?*)
               (seq touched)
               (or (seq (tax/disjoint-pairs tax))
                   (seq (tax/disjoint-metatypes tax))))
      (let [{:keys [candidates truncated]} (exposure-candidates kb touched)
            probes  (exposure-probes tax)
            entries (into []
                          (comp (mapcat (fn [[term focus]]
                                          (exposed-clashes-for-term kb term focus probes
                                                                    arbitrated)))
                                (distinct))
                          candidates)
            ;; **One entry for the pass, not one per trigger.**  The budget is the
            ;; pass's, so the first few triggers spend it and every trigger after them
            ;; is cut short by arithmetic rather than by anything about itself — on a
            ;; corpus load's closing settle that was 41,500 identical complaints, which
            ;; both drowned the :warn stream and evicted every real violation from a
            ;; ledger that keeps the newest 1000.  What a reader needs is that the pass
            ;; was bounded and how much it did not look at.
            entries (cond-> entries
                      (seq truncated)
                      (conj {:violation :exposure-truncated
                             :detail    {:triggers (count truncated)
                                         :sample   (vec (take 3 truncated))
                                         :budget   *exposure-instance-budget*
                                         :message  (str "exposure sweep cut short at "
                                                        *exposure-instance-budget*
                                                        " instances: " (count truncated)
                                                        " trigger(s) went unswept, so clashes"
                                                        " they implicate are unreported")}}))]
        (when (seq entries)
          (violations/report kb entries))))))

;; ---- the arity declaration that arrives after the facts ------------------
;;
;; `arity` is the one definitional check whose retroactive half neither refuses nor
;; arbitrates.  It cannot refuse — that would make the *declaration's* arrival order
;; decide, which is the objection docs/nmtms.md opens with — and it cannot arbitrate,
;; because the sentex it would pair with is the vocabulary entry the conviction is read
;; through (the comment above `checks/arbitrable-kinds` has the measurement).  What is
;; left is to say so: the facts a late declaration convicts are named in the ledger,
;; where a KB author can find them, instead of standing believed and unmentioned.

(defn- arity-declared-of
  "The predicate whose arity this sentence declares, or nil.  Both spellings, since
  `checks/declared-arity` reads both: `(arity P n)`, and the predicate-type membership
  `(binaryPredicate P)` that says the same thing."
  [sen]
  (let [f (nm/functor sen)
        as (rest sen)]
    (when-let [pred (cond
                      (= 'arity f)                                (when (= 2 (count as)) (first as))
                      (contains? checks/predicate-type-arities f) (when (= 1 (count as)) (first as)))]
      (when (symbol? pred) pred))))

(defn- any-arity-declared?
  "Has the KB declared *any* predicate's arity, in either spelling — the O(1) gate that
  makes the pass below free for a KB that has not?

  The taxonomy's arity table alone is not the answer: it holds the `(arity P n)` sentexes,
  and a KB loaded without CoreContext's derivation rules has only the predicate-type
  membership, which `checks/declared-arity` reads and this table never sees.  So the three
  memberships are asked too, as index cardinalities."
  [kb]
  (or (seq (tax/arity-declarations (:taxonomy kb)))
      (boolean (some #(pos? (p/count-with-functor (:index kb) %))
                     (keys checks/predicate-type-arities)))))

(defn- report-arity-reach!
  "File the wrong-arity facts an `arity` declaration entering the moved region convicts —
  content stored before the declaration existed to refuse it, and therefore admitted by
  an `assert` that could not have known.

  Reports and decides nothing.  The facts stay stored and believed, exactly as they were;
  what changes is that `(violations kb)` names the finding, with `:declared-after` carrying
  the declaration's own handle — the same convention the disjointness exposure uses to mark
  an entry as a *finding about stored content* rather than a dropped conclusion.

  **One entry per declaration, not per convicted fact**, carrying the `:count` and a
  `:sample`.  Per fact would put the ledger's size at the mercy of one predicate's extent:
  a declaration over 4,096 wrong-arity facts would file 4,096 entries into a ledger that
  keeps the newest 1,000, evicting every other violation in it — which is the failure
  `expose-clashes!` already had and fixed for its truncation notices.  Nothing is lost by
  summarizing, and that is what separates this from a disjointness exposure: an exposure
  reports a *visibility* that took a change to create, while the wrong-arity facts of `P`
  are re-derivable from the store at any time by anyone who wants the list.  The entry says
  which declaration, how many, and enough of them to recognize.

  **Not gated on the constraint policy.**  `:refuse` versus `:arbitrate` is a question
  about whether a writer is told no and about whose belief moves; nothing here moves
  belief or refuses anybody, so both policies get the report.

  Off while `*rebuilding?*`, like the exposure pass beside it and for the same reason: the
  entry says a declaration *newly* convicted stored content, and on a rebuild everything
  arrives at once, so there is no newly.  Budgeted off the same instance budget — a
  declaration over a predicate with a large extent implicates all of it — and an entry
  whose sweep was cut short carries `:truncated`, so bounded work never reads as full
  coverage.

  Free for a KB that declares no arity at all (`any-arity-declared?`)."
  [kb touched]
  (when (and (not *rebuilding?*)
             (seq touched)
             (any-arity-declared? kb))
    (let [left  (volatile! (long *exposure-instance-budget*))
          ;; content order, so which predicates a bounded pass reaches is a function of
          ;; the vocabulary rather than of the handle order the region came back in
          preds (into (sorted-set)
                      (comp (keep #(p/get-sentex (:records kb) %))
                            (filter #(jtms/in? (:tms kb) (:id %)))
                            (filter #(= :true (:truth %)))
                            (keep #(arity-declared-of (:sentence %))))
                      touched)
          ;; one past the budget, so `taken` says both how much was wanted and whether
          ;; there was more — the same accounting `exposure-candidates`' sweep uses
          sweep (fn [entries pred]
                  (let [n     (long @left)
                        taken (into [] (take (inc n)) (predicate-sentexes kb pred))
                        cut?  (> (count taken) n)
                        ;; no candidate is ever the trigger: a declaration's functor is
                        ;; `arity` (or a predicate type), never the predicate it names
                        found (into []
                                    (keep #(some->> (checks/arity-violation
                                                     kb (:sentence %) (:context %))
                                                    (vector %)))
                                    (if cut? (take n taken) taken))]
                    (vreset! left (if cut? 0 (- n (count taken))))
                    (if-not (seq found)
                      entries
                      (let [[s v] (first found)]
                        (conj entries
                              {:violation :arity
                               :sentence  (:sentence s)
                               :context   (:context s)
                               :detail    {:predicate      pred
                                           :expected       (:expected v)
                                           :count          (count found)
                                           :sample         (mapv (comp :sentence first)
                                                                 (take 3 found))
                                           :declared-after (:opposing-handle v)
                                           :truncated      cut?
                                           :budget         (when cut?
                                                             *exposure-instance-budget*)
                                           :message
                                           (str "arity declared after the facts: " pred
                                                " is declared with " (:expected v)
                                                " argument" (when (not= 1 (:expected v)) "s")
                                                " and " (count found)
                                                " stored fact(s) of it disagree"
                                                (when cut?
                                                  (str " — the sweep was cut short at "
                                                       *exposure-instance-budget*
                                                       " facts, so there may be more")))}})))))]
      (let [entries (reduce sweep [] preds)]
        (when (seq entries)
          (violations/report kb entries))))))

(defn- settle-finish
  "Reconcile the derived caches with settled belief and record the readings.

  `belief-moved?` gates the `refresh-beliefs` reconcile of the genl / genlContext
  closures and the four flat caches.  That reconcile exists to catch a *supporter's
  label flipping* while its sentex stays put, and the only things that flip a label in
  a settle are defeat, revival (`clear-defeats!` reviving a previously-defeated node),
  and `exceptWhen` block changes.  A brand-new or *retracted* declaration does not go
  through here at all — it installs into or leaves the caches straight through the
  `special` integrate/disintegrate hook (`tax/add-genl` / `del-genl!` and friends) on
  the assert/retract path — so a settle that defeated nothing, revived nothing, and
  moved no block leaves those caches already consistent, and the O(vocabulary) scan is
  pure waste.  Skipping it is what makes the common assert (no contradiction anywhere)
  do no taxonomy work at all.

  `refresh-supersessions` is **not** gated the same way, and deliberately.  The
  equality closure also changes on retraction — un-merging a class revives the
  spelling its twin displaced — and that path moves no label, so `belief-moved?` would
  miss it and leave a stale supersession.  It is already proportional to the merged
  set (tiny), not to the KB, so there is nothing to save by gating it; it runs every
  settle."
  [kb passes moved violated dilemmas belief-moved? arbitrated]
  ;; A batch of asserts under `with-deferred-settle` leaves the taxonomy's depth
  ;; potential loose — repairing it per edge is proportional to that edge's
  ;; descendants, which is what the deferral exists to avoid — so the one repair the
  ;; batch owes is paid here, in one O(V+E) pass.  Free when nothing deferred.
  (tax/restore-depths (:taxonomy kb))
  ;; Belief may have moved; reconcile the cached transitive closures with it.
  ;; A defeated `(genl dog animal)` must leave the closure, or `isa?` would keep
  ;; answering through an edge nothing believes any more — and a revived one must
  ;; come back.  This is the only place a supporter's label can flip without a
  ;; sentex being added or removed.
  ;; `jtms/touched` is a superset of every handle whose belief moved this settle (each
  ;; relabelled region), so passing it lets `refresh-beliefs` skip a cache no moved
  ;; supporter touches instead of rescanning the whole vocabulary (perf-review #11).
  (when belief-moved?
    (tax/refresh-beliefs (:taxonomy kb) #(jtms/in? (:tms kb) %) (jtms/touched (:tms kb)))
    ;; ...and repair again, because the reconcile itself can surrender the potential: an
    ;; edge leaving a strongly connected component dissolves it, and a revived one can
    ;; close a new one.  Left to the *next* settle, `:scc` reads empty in between, and
    ;; `:scc` is not only a pruning — `tax/placement-rep` collapses a mutually-visible
    ;; group of contexts to one name through it, so the same firing would place its
    ;; conclusion in `AlphaContext` or in `BetaContext` depending on how many settles had
    ;; run since a defeat touched the cycle, which is precisely the arrival-order
    ;; dependence that choice exists to remove (docs/contexts.md).  Free when nothing
    ;; went loose — every belief move that touches no cycle, which is nearly all of them.
    (tax/restore-depths (:taxonomy kb)))
  ;; ...and the equality closure's own derived state.  A merge whose supporter is no
  ;; longer believed has left the closure by now, so the spellings it displaced are
  ;; displaced no longer and this is where the caller's premise comes back
  ;; (docs/equality.md, "Supersede the original").  Ungated: retraction un-merges
  ;; without moving a label, so this must run even on a belief-quiet settle.
  ;; a supersession flip is a belief change with no relabel to record it, so it is
  ;; collected by hand here and folded into the readings at the end, for the same reason
  ;; the reconcile below is.  Two locals rather than a write straight into the sinks:
  ;; three destinations now want the same answer — the caller's two sinks and the change
  ;; feed — and what "the region this settle moved" is should be decided in one place.
  (let [extra    (volatile! #{})     ; region members no relabel recorded
        extra-in (volatile! #{})     ; ...of which these were believed until this settle
        note!  (fn [m] (vswap! extra into (keys m)))
        before (doto (jtms/superseded (:tms kb)) note!)]
    (special/refresh-supersessions kb)
    ;; A datum superseded *by this settle* was believed until it was, and no relabel
    ;; says so — the flip subtracts from reported belief without moving a label.  So a
    ;; caller diffing belief is told by hand, or a merge would read as "nothing left".
    (vswap! extra-in into (clojure.core/remove before) (keys (jtms/superseded (:tms kb))))
    ;; Supersession is *also* a belief change `belief-moved?` does not see: a
    ;; type/predicate merge (docs/equality.md, round two) supersedes a `genl` /
    ;; `disjoint` / metadata **declaration**, dropping its `in?` while no label was
    ;; defeated, blocked, or revived.  The genl closure and the flat caches must then
    ;; be reconciled or they outlive belief — `isa?` would keep answering through a
    ;; retired type's edge.  So reconcile whenever supersession is (or just was) in
    ;; play; `refresh-supersessions` ran first, so `in?` now reflects the un/newly
    ;; superseded declaration.  Gated on the superseded set, so a KB with no merges
    ;; (the overwhelming common case) pays nothing.  Runs even when `belief-moved?`
    ;; already reconciled once above: that pass read `in?` *before* supersession was
    ;; recomputed, so a settle that both defeated something and moved a supersession
    ;; needs this second, post-supersession reconcile.  The moved set is the relabelled
    ;; regions *plus* every superseded handle (old and new), since a supersession flip
    ;; leaves no relabel to record it (perf-review #11).
    (let [after (jtms/superseded (:tms kb))]
      (note! after)
      ;; the negation memo needs the same hand-off, and for the same reason: a
      ;; supersession flip moves what pairs without moving a label
      (note-supersession-flips! kb before after)
      (when (or (seq before) (seq after))
        (tax/refresh-beliefs (:taxonomy kb) #(jtms/in? (:tms kb) %)
                             (into (jtms/touched (:tms kb))
                                   (concat (keys before) (keys after))))))
    ;; The cross-context exposure reads the same moved region, after the reconciles —
    ;; `:edge-ctxs` and `:cache-ctxs` now reflect settled belief, which is what the
    ;; witnesses walk.
    (expose-clashes! kb (jtms/touched (:tms kb)) arbitrated)
    ;; ...and the other retroactive finding a declaration makes about stored content: an
    ;; arity declared after the facts.  Same region, same budget discipline, and reports
    ;; rather than decides — `arity` is not a nogood, for the reason recorded above
    ;; `checks/arbitrable-kinds`.
    (report-arity-reach! kb (jtms/touched (:tms kb)))
    ;; Both readings, before the region is cleared — it is what decides which of the
    ;; standing reports have to be rebuilt.
    (record-clashes! kb violated dilemmas (jtms/touched (:tms kb)))
    ;; What this settle moved, decided once and handed to everyone who wants it: the
    ;; relabelled regions plus the flips no relabel recorded.  The region is a superset
    ;; of every handle whose belief moved, and it is precisely the set `core/preview`
    ;; diffs — which is what keeps a preview, a consequence report and a feed event
    ;; proportional to what the batch touched rather than to the believed set.
    ;;
    ;; **Nobody asking means nothing built.**  The two sets are built only when a caller
    ;; bound a sink or a listener is registered — the whole of the assert path pays three
    ;; reads to find out that neither is true.  Assembling them first and then discovering
    ;; there was nowhere to put them would be two set constructions per settle, on the
    ;; hottest path in the engine, for a KB that never asked; and `lein perf` is
    ;; ratio-only, so a constant like that divides out of every check it has.
    (let [sink    *touched-sink*
          in-sink *touched-in-sink*
          ;; ...and the change feed, which unlike the sinks nobody had to bind: a listener
          ;; registered on this KB is asking to be told.  Not on a rebuild — `recover` and
          ;; `reindex` relabel everything, so a feed running through one would hand a
          ;; reconnecting application the whole KB as newly believed (the exposure pass
          ;; declines a rebuild for the same reason).
          fed?    (and (not *rebuilding?*) (feed/wants-region? kb))]
      (when (or sink in-sink fed?)
        (let [region (into @extra (jtms/touched (:tms kb)))
              was-in (into @extra-in (jtms/touched-in (:tms kb)))]
          (when sink    (swap! sink into region))
          (when in-sink (swap! in-sink into was-in))
          (when fed?    (feed/note-region! kb region was-in)))))
    ;; Clear the touched set now that everything has read it: the next settle's window
    ;; starts empty (perf-review #11).
    (jtms/reset-touched! (:tms kb))
    (swap! (:settle-stats kb)
           (fn [s] (-> s
                       (assoc :iterations moved :passes passes)
                       (update-in [:histogram moved] (fnil inc 0))))))
  ;; What this settle cost and what it found, once per settle and at the end of it.
  ;; `::exception-fixpoint` above speaks only when the joint fixpoint gives up, so
  ;; without this a settle that took nine passes and one that took a single pass report
  ;; the same nothing — and the pass count is the reading that says whether the KB's
  ;; exceptions have started fighting each other.
  (trove/log! {:level :debug :id ::settled
               :data {:passes     passes
                      :iterations moved
                      :moved?     belief-moved?
                      :conflicts  (count violated)
                      :dilemmas   (count dilemmas)
                      :arbitrated (count arbitrated)}})
  violated)

(defn- settle*
  "Relabel the TMS, resolve soft contradictions, and re-evaluate the `exceptWhen`
  exceptions the triggers queued — to a joint fixpoint.  Records the unsatisfiable
  clashes in `conflicts` and the represented dilemmas in `contradictions`, and returns
  the former.  `clear-defeats!` first, so a contradiction that is no longer present
  revives its previously-defeated member.

  The fixpoint test is `(= new-set (jtms/blocked tms))` because `set-blocked` replaces
  rather than accumulates: a pass that computes the same set has changed nothing, and
  the loop is done.  Passes that *do* move the set are counted as `:iterations` in
  `settle-stats` — the instrument the stratification question is decided from."
  [kb]
  ;; A supporter's label can flip three ways in a settle: revival (`clear-defeats!`
  ;; lifting a node this run defeated last run — so a non-empty defeated set *before*
  ;; the clear counts), a fresh defeat, and a block change (a moved pass).  Snapshot
  ;; the pre-clear defeated set now; `settle-finish` folds it with the post-resolve
  ;; defeated set and the moved count into the `belief-moved?` gate on the cache
  ;; reconcile.  Both reads are of the small defeated set, never the graph.
  (let [defeated-before  (jtms/defeated (:tms kb))
        defeated-before? (boolean (seq defeated-before))
        moved? (fn [moved] (or defeated-before?
                               (boolean (seq (jtms/defeated (:tms kb))))
                               (pos? moved)))]
    (jtms/clear-defeats! (:tms kb))
    ;; ...and reconcile the belief-derived caches with what that revived, **before**
    ;; anything asks them a question.  `clear-defeats!` lifts a defeat, so a `genl` or
    ;; `genlContext` edge defeated last settle is believed again as of this line — but
    ;; the cached closures still describe the KB without it until `refresh-beliefs` runs.
    ;; It must therefore run *here*, before `constraint-nogoods` below reads them, and not
    ;; only in `settle-finish`: discovery reading a vocabulary one settle out of date
    ;; leaves a `P`/`¬P` pair made jointly visible by the revived edge unarbitrated, and
    ;; `retract!` returns with both believed — a state the KB's own `recover` over the
    ;; same records disagrees with.
    ;;
    ;; Gated on there having *been* a defeat to lift, and scoped by `touched`, so a
    ;; settle with nothing defeated pays nothing — which is nearly all of them, and the
    ;; same reasoning `settle-finish`'s own `belief-moved?` gate states.
    (let [revival-flips (when defeated-before?
                          (tax/refresh-beliefs (:taxonomy kb) #(jtms/in? (:tms kb) %)
                                               (jtms/touched (:tms kb)))
                          (tax/restore-depths (:taxonomy kb))
                          ;; ...and an except among the revived is a visibility flip:
                          ;; what it hid is seeable again, and only this settle knows
                          ;; the defeat was lifted
                          (recheck-flipped-excepts kb defeated-before))]
      (loop [pass 1, moved 0, seen #{}, flips (or revival-flips #{})]
        ;; The definitional clashes are re-derived **per pass**, not per defeat round: a
        ;; pass can re-chain a released rule and put new content in the region, where a
        ;; defeat round only ever withdraws belief and so can retire a pair but never
        ;; make one.  `resolve-contradictions` filters the set to what is still believed
        ;; before each of its own rounds.
        (let [ngs    (constraint-nogoods kb)
              ;; accumulated across passes, because the exposure pass at the end has to
              ;; know about every pair this settle decided, not only the last pass's
              arbitrated (into seen (map :nogood) ngs)
              ex-before  (believed-excepts kb)
              {:keys [violated dilemmas]} (resolve-contradictions kb ngs)
              ;; a resolution that defeated (or revived) a visibility except flipped
              ;; what its cone can see — queue the same re-check its arrival or
              ;; departure queues, and carry the marked rules to the re-chain, since a
              ;; reveal moves no blocked justification for the drain to notice
              flips  (into flips
                           (recheck-flipped-excepts
                            kb (let [ex-after (believed-excepts kb)]
                                 (concat (set/difference ex-before ex-after)
                                         (set/difference ex-after ex-before)))))
              queued (drain-recheck! kb)]
          (if (empty? queued)
            (settle-finish kb pass moved violated dilemmas (moved? moved) arbitrated)
            (let [was  (jtms/blocked (:tms kb))
                  new  (exception-blocked-set kb queued)
                  ;; an aggregate rule is owed a re-join whether or not anything blocked
                  ;; — a count that rose licenses a firing no block ever suppressed
                  aggs (aggregate-recheck-rules kb queued)
                  ;; ...and so is a firing that was refused before it could be blocked:
                  ;; nothing about it is in `was` for `new` to differ from, so the blocked
                  ;; set is the wrong instrument for it and its own record is asked
                  ;; instead.  Decided before the sweep and re-decided after it.
                  {free :free over :overflow} (released-refusals kb queued)]
              (if (and (= new was) (empty? aggs) (empty? free) (empty? over) (empty? flips))
                (settle-finish kb pass moved violated dilemmas (moved? moved) arbitrated)   ; unproductive pass: converged
                ;; read before the sweep, which deletes justifications
                (let [released (released-rules kb was new)]
                  (jtms/set-blocked (:tms kb) new)
                  (sweep-excepted! kb (into #{} (remove was) new))
                  ;; A released refusal is re-derived from the bindings it recorded, not
                  ;; re-joined: `place-conclusion` with the firing's own conclusion,
                  ;; placement and antecedents.  The conclusions it places are new datums,
                  ;; so they go back on the agenda like any other.
                  (let [seeds (into [] (mapcat (fn [[rh e]] (chain/release-refusal! kb rh e)))
                                    free)]
                    (when (seq seeds) (rechain-seeds kb seeds)))
                  ;; What has to be chained again is what this pass *released* — plus the
                  ;; rules with no triggering sentence to read, the rules whose refusal
                  ;; record overflowed (no entries to re-ask, so the coarse re-join is what
                  ;; is left), and whatever the sweep queued, since deleting a fact can
                  ;; release some other rule's exception at derive time where no block ever
                  ;; existed to lift.  Not every rule the pass touched: seeding `chain`
                  ;; with a rule joins it over the whole extent, so a blanket re-chain is
                  ;; quadratic in the firing count.
                  (rechain-exception-rules kb (into released
                                                    (concat (blanket-recheck-rules queued)
                                                            aggs
                                                            over
                                                            flips
                                                            (keys @(:recheck kb)))))
                  (if (< pass max-settle-passes)
                    (recur (inc pass) (inc moved) arbitrated #{})
                    (do (trove/log! {:level :warn :id ::exception-fixpoint
                                     :msg  (str "exception re-check did not converge in "
                                                max-settle-passes " passes; giving up")
                                     :data {:passes pass :blocked (count new)}})
                        (settle-finish kb pass (inc moved) violated dilemmas (moved? (inc moved)) arbitrated))))))))))))

(defn settle
  "Settle belief (`settle*`), then hand the region it moved to whoever is listening.

  Returns the unsatisfiable clashes, as `settle*` does.  Delivery is here rather than
  inside `settle-finish` because a listener may **write**, and a write inside a relabel
  would relabel mid-relabel: by the time this runs the fixpoint is reached, the caches
  are reconciled, the readings are recorded and the touched set is cleared, so a
  listener's `assert` starts a fresh settle like any other caller's.  A KB nobody is
  listening to pays one deref (`feed/deliver!`)."
  [kb]
  (let [violated (settle* kb)]
    (feed/deliver! kb)
    violated))

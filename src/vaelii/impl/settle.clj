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
  "What one opposed body currently yields, as `{:nogoods … :neg … :pos …}`.

  `:nogoods` is every believed `(not body)` paired with every believed `body` whose two
  contexts have a non-empty common down-closure.

  `:neg` and `:pos` are the contexts each polarity was believed in, whether or not it
  paired — the whole of what a `genlCx` edge could change the pairing through.  The
  only thing the pairing reads through that relation is `share-a-view?` of one context
  from each side, so an entry every one of whose `:neg` × `:pos` verdicts still reads the
  same is an entry a context edge cannot have moved (`negation-nogoods`).  Collected here
  because this is the one pass that enumerates the body's sentexes, and re-reading the
  index to recover them is the O(standing) work the memo exists to avoid.

  Belief-filtered, so a body whose positive side is currently defeated yields no nogood —
  which is what makes revival work rather than something to compensate for.  Reviving is
  a relabel (`clear-defeats!`), the relabel puts the handle in the settle's moved region,
  and the region is what asks for this body again.

  Read **as stored** rather than through `query`, because this is an iteration over the
  engine's own coincidence set and not a question about the world.  `query` rewrites a
  goal to its class representative, so a body an equality has since retired would hand
  back the representative's sentexes and be reported under the retired spelling — one pair
  reported twice, under two names, one of them naming content nothing believes.  A
  superseded body answers nothing here, which is the correct reading of a spelling that
  has been restated (docs/equality.md)."
  [kb body share-a-view?]
  (let [tms (:tms kb)
        neg (vec (kb/sentexes-matching-as-stored kb (list 'not body) '?ctx)) ; believed (not body)
        pos (vec (kb/sentexes-matching-as-stored kb body '?ctx))]            ; believed body
    {:neg (into #{} (map :context) neg)
     :pos (into #{} (map :context) pos)
     :nogoods
     (into #{}
           (for [nx    neg
                 :let  [ctxN (:context nx)]
                 sx    pos
                 :let  [ctxX (:context sx)]
                 :when (and (not= (:id sx) (:id nx))
                            (share-a-view? ctxN ctxX))]
             (let [p (max (strength/rank-of (jtms/defeat-class tms (:id nx)))
                          (strength/rank-of (jtms/defeat-class tms (:id sx))))]
               {:nogood #{(:id nx) (:id sx)} :priority p
                :sentence (list 'contradicts body (:sentence nx))})))}))

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

  A genlCx edge is the third way, and it is not here: joint visibility is read
  through that closure rather than through either side's handles, so the edge moves no
  handle and posts no body.  `negation-nogoods` adds those separately, from the
  visibility verdicts each entry recorded (`moved-verdicts` and `bodies-crossing`)."
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

(defn- visibility-key
  "The order-free key for the joint-visibility question about two contexts.  Ordered
  structurally by `nm/compare-form` — never a printed `(compare (str a) (str b))` —
  since `common-descendant?` is symmetric and a key that was not would store the same
  verdict twice and compare the wrong one half the time.  Both contexts are symbols, so
  the order is the one the printed names gave, without the two Strings per call."
  [a b]
  (if (neg? (nm/compare-form a b)) [a b] [b a]))

(defn- visibility-pairs
  "The context pairs one memo entry's pairing is decided by: one context from each
  polarity, which is exactly what `body-nogoods` asks `share-a-view?` about."
  [{:keys [neg pos]}]
  (for [a neg, b pos] (visibility-key a b)))

(defn- visibility-views
  "The joint-visibility verdict for each of `ks`, the context pairs the memo's entries
  cross.  Keyed by the pair rather than by body, so a KB whose contradictions all sit in
  one context stores one boolean however many of them it holds — and re-reading them
  costs the **context vocabulary** rather than the standing set."
  [tax ks]
  (into {} (map (fn [[a b :as k]] [k (tax/common-descendant? tax [a b])])) ks))

(defn- moved-verdicts
  "The recorded verdicts that no longer read the way they read at the last stamp.

  This is the proportional form of the `genlCx` generation test, and it is exact
  rather than an over-approximation.  What a body's pairing reads through that relation
  is `common-descendant?` of one context from each polarity and nothing else, so an entry
  whose verdicts all stand yields the pairing it yielded last settle — whatever else
  moved in the relation, and however many edges moved.  A counter cannot say that: it
  reports that *some* edge moved and never which, so a lone edge under a context no
  contradiction is stated in retired every standing pair.

  Empty is the ordinary answer and the one worth naming, because it is what makes the
  narrowing cheap as well as right: no verdict moved, so no entry moved, and the memo is
  never walked at all."
  [tax views]
  (reduce-kv (fn [acc [a b :as k] v]
               (cond-> acc (not= v (tax/common-descendant? tax [a b])) (conj k)))
             #{} views))

(defn- bodies-crossing
  "The memoized bodies whose pairing reads one of `ks` — what `moved-verdicts` names, read
  back as the entries owing a re-derivation."
  [by-body ks]
  (into #{}
        (keep (fn [[body entry]]
                (when (some ks (visibility-pairs entry)) body)))
        by-body))

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

  **A genlCx edge is the third input, and it is narrowed by the cone rather than by
  a counter.**  Joint visibility is read through that closure, so a new context edge can
  make a pair visible that no handle of either side went near — the region and `:dirty`
  between them cannot see it, and neither knows the body.  What decides it is
  `share-a-view?` of one context from each polarity, which `body-nogoods` records as
  `:neg` / `:pos` while it is enumerating them anyway.  `moved-verdicts` re-reads those
  verdicts when the relation moves and `bodies-crossing` reads the entries owing a
  re-derivation back off them; a body whose verdict the memo does not hold re-derives,
  which is the safe direction.

  An entry with a polarity believed **nowhere** is dropped rather than kept, and that is
  not the same trade.  It pairs nothing for want of belief rather than for want of
  visibility — a relabel away, and a relabel is in the region — so no context edge can
  revive it, there is nothing for a verdict to protect, and keeping it would only make
  the memo grow.

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
  same case: it leaves no `:vocab`, so the next settle reads the memo as carrying nothing
  and re-derives the whole of `:opposed` regardless of what `:dirty` said."
  [kb]
  (let [opposed @(:opposed kb)]
    (if (empty? opposed)
      ;; nothing is stored in both polarities, so nothing can pair — and this is the one
      ;; place the whole memo can be dropped rather than re-examined, exactly as
      ;; `constraint-nogoods` drops `:clashes` when nothing separates anything
      (do (reset! (:negations kb) {}) #{})
      (let [tax   (:taxonomy kb)
            prev  @(:negations kb)
            vocab (tax/relation-gen tax :genlCx)
            ;; a memo with no stamp at all carries nothing — a fresh KB, a `recover`, or
            ;; the empty-`:opposed` reset above — so the whole opposed set is re-derived.
            ;; That is a different question from *what moved since* the stamp, which is
            ;; what the verdicts below answer.
            stale? (or (not *incremental-negations*) (nil? (:vocab prev)))
            views  (:views prev {})
            carry  (if stale? {} (:by-body prev {}))
            ;; The verdicts are re-read when the relation moved, and the **memo** is
            ;; walked only when one of them came back different.  So a context edge under
            ;; a context nothing here is stated in costs the recorded pairs — one, on a KB
            ;; whose contradictions share a context — rather than the standing set.
            shifted (when-not (or stale? (= vocab (:vocab prev)))
                      (moved-verdicts tax views))
            moved  (if stale?
                     opposed
                     (cond-> (moved-bodies kb opposed (:dirty prev))
                       (seq shifted) (into (bodies-crossing carry shifted))))
            share-a-view? (memoize (fn [ca cb] (tax/common-descendant? tax [ca cb])))
            by-body (reduce (fn [m b]
                              (let [{:keys [neg pos nogoods] :as entry}
                                    (body-nogoods kb b share-a-view?)]
                                ;; an entry a context edge could never revive leaves the
                                ;; memo, or it would only ever grow: a body with a believed
                                ;; side missing pairs nothing for want of *belief*, and
                                ;; belief comes back through the region
                                (if (or (seq nogoods) (and (seq neg) (seq pos)))
                                  (assoc m b entry)
                                  (dissoc m b))))
                            carry
                            moved)]
        (loop []
          (let [cur    @(:negations kb)
                ;; `:dirty` only grows between the read of `prev` and this write, and
                ;; only this fn clears it — so the difference is exactly the posts that
                ;; landed while the bodies above were being re-derived
                posted (set/difference (set (:dirty cur)) (set (:dirty prev)))
                kept   (apply dissoc by-body posted)
                next   {:vocab   vocab
                        :by-body kept
                        ;; The verdicts.  Re-read for the pairs already recorded, extended
                        ;; by whatever the entries re-derived here cross, and **enumerated
                        ;; over the whole memo only on a full re-derivation** — which is
                        ;; also the only settle that can drop a pair from the roster, so it
                        ;; is where the pruning belongs.  Every other settle pays the
                        ;; recorded pairs plus the bodies it touched, neither of which is
                        ;; the standing set.
                        :views   (if stale?
                                   (visibility-views
                                    tax (into #{} (mapcat visibility-pairs) (vals kept)))
                                   (merge views
                                          (visibility-views tax shifted)
                                          (visibility-views
                                           tax (into #{} (mapcat visibility-pairs)
                                                     (vals (select-keys kept moved))))))
                        :dirty   posted}]
            (if (compare-and-set! (:negations kb) cur next)
              (into #{} (mapcat :nogoods) (vals kept))
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

(defn- refresh-after-defeat
  "A defeat inside arbitration flips belief with no arrival for the taxonomy to see,
  and the reconcile otherwise waits for `settle-finish` — so everything the rest of
  this settle reads would walk closures holding the defeated edge.  The mirror of the
  revival refresh at the top of `settle*`, for the mirror reason, and scoped by
  `touched` the same way: the next defeat round's nogoods and the preserving re-joins
  this round queued must read belief as it is now."
  [kb]
  (special/reconcile-belief-change! kb (jtms/touched (:tms kb)))
  (tax/restore-depths (:taxonomy kb)))

(defn- preserved-rejoins-for
  "The forward rules whose preserving joins may have moved because arbitration
  defeated `handles` — with nothing arriving or leaving, so no trigger queues the
  re-join an arrival would.  The pass that receives these re-chains them like any
  blanket mark: a firing whose named witness went OUT re-derives through a route the
  one witness did not travel, or is withdrawn by its own re-check, instead of waiting
  for an unrelated arrival to move the predicate."
  [kb handles]
  (into #{}
        (comp (keep #(p/get-sentex (:records kb) %))
              (mapcat #(inherit/rejoin-rules kb (:sentence %))))
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
  (loop [solver-violated [], rejoin #{}]
    (let [active (seq (into #{}
                            (filter #(live-nogood? (:tms kb) %))
                            (concat constraint (negation-nogoods kb))))]
      (if-not active
        {:violated solver-violated :dilemmas [] :rejoin rejoin}
        (let [decisions (map #(decide-nogood kb %) active)
              clears    (into #{} (keep :defeat decisions))]
          (if (seq clears)
            (do (jtms/defeat (:tms kb) clears)
                (refresh-after-defeat kb)
                (recur solver-violated (into rejoin (preserved-rejoins-for kb clears))))
            (let [contested (into #{} (mapcat :contested decisions))
                  hard      (vec (keep :hard decisions))
                  dilemmas  (vec (keep :dilemma decisions))]
              (if (empty? contested)
                {:violated (into solver-violated hard) :dilemmas dilemmas :rejoin rejoin}
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
                        (refresh-after-defeat kb)
                        (recur (into solver-violated (:violated res))
                               (into rejoin (preserved-rejoins-for kb defeat))))
                    {:violated (into (into solver-violated hard) (:violated res))
                     :dilemmas dilemmas :rejoin rejoin}))))))))))

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
  (resources/kb/CxCore.txt says so of the predicate itself)."
  [kb {:keys [nogood priority sentence kind]}]
  (let [tms   (:tms kb)
        recs  (:records kb)
        ;; The list inside each side follows the same rule as the sides themselves:
        ;; `jtms/supports` is a set of allocation-ordered ids, so it is sorted by the
        ;; justification's content — literally the key `core/supporting-justifications`
        ;; reads through, so a side's derivations list identically however they arrived
        ;; and the two surfaces cannot drift apart into two orders
        jkey  (kb/justification-content-key kb)
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
                             :justifications (->> (jtms/supports tms h)
                                                  (keep #(p/get-justification recs %))
                                                  ;; `jkey` is a `get-sentex` per antecedent
                                                  ;; — built once per justification, not per
                                                  ;; comparison; a rule side lists the rule's
                                                  ;; whole firing history
                                                  (nm/sort-by-content-key jkey nm/compare-form))})))
                   (sort-by (juxt :sentence :context :handle) nm/compare-form)
                   vec)]
    {:nogood nogood :priority priority :sentence sentence
     :handles (mapv :handle sides)
     :kind kind
     :sides sides}))

(defn- report-order
  "One clash report's place in a reading, as content: each side's sentence then its
  context, in the side order `clash-report` already fixed.  A structural key, compared
  by `nm/compare-form` — never a printed one.  Handles are nowhere in it, which is the
  whole point: they are allocated in assertion order."
  [r]
  (mapv (juxt :sentence :context) (:sides r)))

(defn ranked
  "`reports` in content order — what `core/conflicts` and `core/contradictions` answer.

  The stored vectors are in arrival order (`record-clashes!` says why the sort is here
  rather than there), so this is where the reading stops being a fact about which pair
  was typed first.  Every reader of `(:conflicts kb)` or `(:contradictions kb)` owes
  this call; one that skips it reintroduces exactly the order dependence the sides
  inside each report are already sorted to remove.

  The key is read off metadata `record-clashes!` attached when the report was built, so
  this compares prepared keys rather than rebuilding every side's.  A report that
  arrives without one is keyed on the spot rather than trusted to be orderable.  The
  keys are structural forms, so they are compared by `nm/compare-form`."
  [reports]
  (vec (sort-by #(or (::order (meta %)) (report-order %)) nm/compare-form reports)))

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
        ;; **Stored in arrival order, and every reader owns its own ordering.**  These
        ;; two vectors come off a hash set of handle-keyed nogoods, so their order is
        ;; the order the pairs were typed in and nothing a caller may key on: `ranked`
        ;; is what puts a reading in content order, and `core/conflicts`,
        ;; `core/contradictions` and the preview's standing filter each call it.  A new
        ;; reader of either atom owes the same call — the sides inside one report are
        ;; already content-ordered by `clash-report`, and the list around them is the
        ;; other half of that same guarantee.
        ;;
        ;; Sorting *here* would put it on the settle path, which is every mutation:
        ;; O(standing log standing) comparisons per assert, on the path whose memo
        ;; exists to keep the per-pair term bookkeeping (`negation-arbitration` gates it
        ;; at 32x the standing dilemmas): 1.60 ms/assert at 800 standing dilemmas with
        ;; the sort here, 1.07 ms with it at the read.  A reading is asked for far more
        ;; rarely than the KB is written to, so the sort belongs where it is read.
        ;;
        ;; The key still rides the report's *metadata*, computed once when the report is
        ;; built and carried with it through the memo — so `ranked` compares keys rather
        ;; than `pr-str`ing every side of every standing report per call, and metadata
        ;; stays off the wire and out of `=`.
        keyed (fn [r] (cond-> r (nil? (::order (meta r)))
                              (vary-meta assoc ::order (report-order r))))
        vs    (mapv (comp keyed build) violated)
        ds    (mapv (comp keyed build) dilemmas)]
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
  `genlCx` closures, disjointness (closed under genl), a predicate declared
  transitive or reflexive or holding an inverse, one with a **preserved argument
  position**, and the evaluables — computed rather than stored, so no fact can move
  them at all, but cheaper to wave through than to reason about.

  Argument-position preservation is the one that has to be read per KB rather than
  listed: `(transitiveInArg P n R)` makes a stored `(P … W …)` answer `(P … A …)` for
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
        (seq (tax/inverses-under tx pred))
        (inherit/declared-about? kb pred))))

(defn- trigger-shapes
  "The shapes of a rule's queued triggers, or `:all` when the rule was queued
  unconditionally or any trigger has no readable shape."
  [triggers]
  (if (#{:all :all-rejoin} triggers)
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
                          ;; ...and the exception conjuncts are read **through their query
                          ;; frames** (`rules/watched-literals`, the same peel the re-check
                          ;; index keys on), because the shape test needs a literal a fact
                          ;; could carry.  An exception may itself be a query operator, and
                          ;; `(unknown (qskip PX7))` has no shape however ground it is — so
                          ;; unpeeled it falls through to "keep" every time, and the rule's
                          ;; whole firing history is re-decided on every arriving fact.
                          ;; Peeled, the conjunct tested is the one the query reads and the
                          ;; narrowing bites again.
                          block-lits (when rsx
                                       (concat (mapcat rules/watched-literals
                                                       (apply concat (provers/rule-exceptions kb rh)))
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

(def ^:dynamic *rebuilding?*
  "Is this settle **restoring** a KB rather than reacting to a change to one?

  Bound by `core/recover`, and two passes read it.  It turns the **exposure** pass off:
  that pass reports the disjointness clashes the settle's moved region *newly* makes
  jointly visible — two memberships each admissible where written, contradictory from a
  context below both — and on a rebuild the claim is vacuous, since nothing is newly
  visible and the whole KB is arriving at once because it was already there.  Left on,
  the region is every stored sentex and a bounded incremental check becomes an unbounded
  full audit: 27% of an OpenCyc import, silently, because the membership route is exact
  and unbudgeted (one probe per membership) and a rebuild's region holds every
  membership there is.

  Which is not to say the audit is worthless — it is the same question asked of the
  whole KB rather than of a change to it.  But it is a *choice*, and paying it inside
  every `recover` and `reindex` is not one anybody made.

  It turns the **revival** re-seed off for the sibling reason, which `revived-seeds`
  states: a rebuild relabels the whole graph, so most of what it believes reads as
  newly believed, and none of it is owed a re-derivation.  That covers both halves of
  the re-seed — the relabelled one and `*unmerged-sink*`'s."
  false)

(def ^:dynamic ^:private *unmerged-sink*
  "A volatile holding the spellings an **un-merge** gave back, or nil.

  The revival re-seed's other half, and it needs its own channel because the flip it
  reports is the one `jtms/revived` structurally cannot see.  Supersession moves belief
  with **no relabel behind it** — deliberately, since a superseded datum stays in `:in`
  so its twin's justification survives — so an un-merged spelling is in none of the three
  window sets.  `settle-finish` is where the answer exists (it brackets
  `special/refresh-supersessions` already, to tell a caller which way each handle moved),
  and by then the loop has converged.  So `settle` binds this, reads it, and settles
  again; see there for why that rather than moving the reconcile into the loop."
  nil)

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
                     ;; same flattening `exception-candidates` uses, frames peeled for the
                     ;; same reason: any literal reaching keeps the entry, which is the
                     ;; safe direction, and an unpeeled query operator reaches always.
                     ;; This is the population that shape is commonest in — an exception
                     ;; that is an `(unknown S)` holds exactly while `S` is absent, which
                     ;; is the state a firing gets *refused* in, so a rule of that shape
                     ;; keeps its whole history here rather than as justifications.
                     lits   (when rsx
                              (concat (mapcat rules/watched-literals
                                              (apply concat (provers/rule-exceptions kb rh)))
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

(defn- revived-seeds
  "The datums whose label went **OUT ⇒ IN** this settle, minus the ones an earlier pass
  has already put back on the agenda.

  The third instrument in the same pass, for the third shape of one defect, and the one
  that reads belief rather than a firing.  `released-rules` finds a release in the
  blocked set, which names only firings that were *placed*.  `released-refusals` re-asks
  the firings that were built and refused at placement.  Neither can see this one,
  because no firing was ever attempted: the join ran while an antecedent was OUT, and
  `chain/*matcher*` is belief filtered, so the OUT datum was not a match and the pair
  was never a candidate.  Nothing was suppressed — the combination was not enumerable.

  Extending the refusal record to cover it is the wrong shape and is not what this does:
  a refusal is one entry per refused firing, where the analogous record here would be
  one per *non-match*.  So the trigger is read where the belief actually moved,
  `jtms/revived`, which narrows the settle's own relabelled region to the datums that
  gained belief and were not created by this window.

  The seeds are **datums**, so re-chaining one costs what asserting it costs — one join
  per rule keyed by its predicate.  Seeding the *rules* instead would join each over the
  whole fact extent, which is the cost `rechain-exception-rules` exists to avoid paying
  per queued rule.

  **Not during a rebuild.**  `recover` relabels the whole graph and lands deliberately
  unblocked, so an excepted conclusion reads as revived until the settle withdraws it
  again — and none of them is owed a re-derivation, because the stored justifications
  the rebuild replays already carry everything the live KB derived."
  [kb done]
  (when-not *rebuilding?*
    (into [] (remove done) (jtms/revived (:tms kb)))))

(defn- blanket-recheck-rules
  "The queued rules with no triggering sentence (`:all` — a taxonomy edge moved, or the
  rule was just indexed).  Those keep the coarse re-chain: with no sentence to read,
  nothing says whether the move blocked or released, so the re-derivation has to be
  attempted either way."
  [queued]
  (keep (fn [[rh triggers]] (when (#{:all :all-rejoin} triggers) rh)) queued))

(defn- forced-recheck-rules
  "The unconditional rechecks that also owe a fresh join when blocking stayed still."
  [queued]
  (keep (fn [[rh triggers]] (when (= :all-rejoin triggers) rh)) queued))

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
  "Re-derive from `seeds` — datum handles something put back on the agenda.  Filtered to
  what is still stored and believed, since a sweep in between may have collected some.

  Four callers, all of them naming datums the ordinary arrival path never handed the
  chainer.  `special/resubsumption-seeds`: a firing names *one* witness for the `genl`
  path it subsumed through, so removing that witness sweeps the conclusion even when the
  reachability survives, and the facts under the edge have to be re-joined to get it
  back.  A released refusal's re-derivation, whose placed conclusions are new datums like
  any other.  `revived-seeds`, the datums whose belief came back this settle.  And
  `settle`'s un-merge round, which is the same revival reached by the one route with no
  relabel behind it (`*unmerged-sink*`).

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
;; a membership arriving, a declaration arriving, a genl or genlCx edge moving,
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
                                      "), jointly visible from "
                                      (pr-str (vec (sort nm/compare-form mx))))}})))

(def ^:dynamic *exposure-instance-budget*
  "How many candidate instances one settle's exposure pass will enumerate for the
  extent-sweeping routes — a separating declaration, a metatype membership, a genl
  edge, and a genlCx edge each implicate every instance below their types (or
  in their cone), and on a large corpus that is the extent, not the region.  A
  sweep cut short files a single `:exposure-truncated` entry naming its trigger, so
  the cap is never silent.  The membership route is exact and unbudgeted — it is
  O(1) per moved membership, and it is the route ordinary writes take.

  **Where a cut can see arrival order, and why it is left there.**  What orders the
  sweep is the **trigger** level: the moved region is walked in content order
  (`content-order`), which is affordable because a region is small.  Below that — the
  down-closure, the context cone, the posting list of one type or predicate — nothing
  is sorted, and the reason is the same at every level: the enumerations are lazy so a
  budgeted consumer realizes only its prefix, and sorting to choose that prefix forces
  the whole extent, which is the cost the cap was added to refuse.

  That is measured rather than assumed.  Sorting the context cone took
  `retract-context-cycle-scaling` from 0.08 to 0.28 ms/op at 2048 contexts — a 3.4x
  growth against a 2x bound — because a context cycle makes the cone the whole graph.
  The check exists to say a retraction is flat in the graph it is not about, and a sort
  is exactly what stops it being.

  What the residual is, stated exactly.  A cut sweep decides a content-dependent subset
  of the pairs its trigger implicates, and the rest go **undecided this settle** rather
  than decided the other way.  Two things carry them: discovery accumulates, so a pair
  a later settle's region surfaces is remembered in `:clashes` and re-examined every
  settle after (`clash-candidates`), and the standing whole-KB question takes no budget
  at all (`exposed-clashes`) — though that one reports rather than arbitrates, and
  disjointness only.  So the order-dependence past the cut is in *when* a pair is
  arbitrated, not in which way it goes."
  4096)

;; ---- the two halves every bounded pass is made of ------------------------
;;
;; Four passes spend `*exposure-instance-budget*`, over six enumerations between them,
;; and each is the same two steps: take what the budget still allows off an enumeration,
;; then say so if there was more.  Both steps live here once.  The arithmetic is subtle
;; enough to get wrong in a copy — one probe past the cap, and a debit that differs
;; between a sweep that fit and one that did not — and the notice is worse than subtle:
;; it fails **silently**, as a passing suite over a KB that looks clean.

(defn- take-budgeted
  "The prefix of `xs` the budget in `left` still allows, as `[taken cut?]`, debiting what
  it realized.  A vector, so a caller that counts it pays nothing for the count.

  **One past the budget is realized on purpose**, so `taken` says both how much was
  wanted and whether there was more: `cut?` is then exactly *there was something here I
  did not look at*, which at a budget of zero still costs one probe.  Deciding it on the
  budget being spent instead would file every trigger whose reach is **empty** as cut
  short — swept in full by looking at nothing — and `:triggers` is a number a reader
  acts on: 183,397 reported against a true 41,500 on an OpenCyc load.

  A cut leaves nothing for the enumerations after it, which is the arithmetic that makes
  the budget the *pass's* rather than each trigger's; one that fit debits what it took.
  So a caller holding one volatile across several enumerations spends them in order and
  does no arithmetic of its own: the first takes what it can and the next reads what is
  left, whether the two sit in one trigger's reach or in different triggers.

  **The tail past the prefix is unread**, which is what the cap buys and what a caller
  owes it: sorting an enumeration to choose that prefix would force the whole extent the
  cap exists to refuse, and `instances-below` carries the measurement.  That is a claim
  about the tail and about nothing else — **building** an enumeration is not free, and
  `subtree-facts` is the one to read it against, since it walks a spec closure and reads
  an index cardinality per member before it yields a first fact.  The cap bounds the
  postings, not the vocabulary above them.

  The budget bounds what is **enumerated** and never what survives a later test, so a
  caller filters after the take: a `keep?` rejecting everything then costs the budget
  rather than the extent."
  [left xs]
  (let [n     (long @left)
        taken (into [] (take (inc n)) xs)
        cut?  (> (count taken) n)]
    (vreset! left (if cut? 0 (- n (count taken))))
    [(if cut? (subvec taken 0 n) taken) cut?]))

(defn- cut-notice
  "The one ledger entry a bounded sweep owes when it did not finish — the kind, how many
  of its own units went unlooked-at, three of them to recognize, and the bound — or nil
  when nothing was cut, so a caller `cond->`s it on.

  **Filed off the cut and never off the findings**, and that asymmetry is the whole of
  it.  A sweep can spend the budget convicting nobody, and then there is no finding for a
  flag to ride on while every unit after it is bounded to zero and examines nothing: the
  content under those is neither refused, nor reported, nor counted, and the pass reads
  as full coverage.  That is the one thing a bounded pass may not do, so the notice is a
  function of the cut alone and of nothing the pass happened to find.

  **One entry for the pass, not one per unit.**  The budget is the pass's, so past the
  cut the units are dropped by arithmetic rather than by anything about themselves — on a
  corpus load's closing settle that was 41,500 identical complaints, which both drowned
  the `:warn` stream and evicted every real violation from a ledger that keeps the newest
  1,000.  What a reader needs is that the pass was bounded and how much it did not see.

  **The kinds stay apart, and so does the vocabulary each is read with**, because a
  reader acts on them differently: `unit` is what the budget counts, `noun` what went
  unswept, `consequence` what is lost by it — *unreported* is a different loss from
  *undecided* — and `count-key` the detail key the count is read under, `:triggers` where
  the budget is spent per trigger and whatever a sweep bounded over some other unit calls
  its own.  Folding them into one kind would cost exactly the difference they carry.

  A pass reporting **two** bounds in one entry builds its own instead, and both that do
  say so where they build it: the shape here is one bound, one unit and one consequence,
  and widening it to carry a second would reword a message a reader already reads."
  [kind cut {:keys [sweep unit noun consequence count-key]}]
  (when (seq cut)
    {:violation kind
     :detail    (array-map
                 count-key (count cut)
                 :sample   (vec (take 3 cut))
                 :budget   *exposure-instance-budget*
                 :message  (str sweep " sweep cut short at " *exposure-instance-budget*
                                " " unit ": " (count cut) " " noun "(s) went unswept, so "
                                consequence))}))

(defn- instances-below
  "The terms holding a believed membership in any subtype of `types` — the
  candidates a separating declaration or a new genl edge can put in a clash.  Lazy,
  so a budgeted consumer realizes only what it takes.  The global down-closure on
  purpose: an over-approximated candidate merely checks and yields nothing.

  **The closure is not sorted, and the laziness is the reason.**  A budgeted consumer
  takes a prefix, so sorting to order that prefix would force the whole down-closure
  before the first term came out — which is the cost the budget exists to refuse, and
  it is measured: the same sort over `members-in-cone`'s cone took
  `retract-context-cycle-scaling` from 0.08 to 0.28 ms/op at 2048 contexts, against a
  claim that a retraction is flat in the graph it is not about.  What orders the sweep
  is one level up, over the moved region, where the set is small enough to sort
  (`content-order`); within a trigger the type closure comes back as a set, whose
  iteration is a function of its elements rather than of when they were written.  The
  instance postings walked beneath it carry no such property — a posting can be
  handle-ordered, so a budget cut past `*exposure-instance-budget*` takes its prefix
  in an order the discovery accumulating in `:clashes` is what compensates for.

  Non-symbols are dropped rather than probed: a label the taxonomy holds need not be a
  symbol — OpenCyc separates thousands of reified NATs — and a compound heads no stored
  membership, so it could not be one end of a pair even if it were enumerated."
  [kb types]
  (let [tax (:taxonomy kb)]
    (for [t     (filter symbol? types)
          t'    (filter symbol? (tax/specs tax t))
          s     (keep #(p/get-sentex (:records kb) %)
                      (p/sentexes-with-functor (:index kb) t'))
          :when (and (jtms/in? (:tms kb) (:id s))
                     (= :true (:truth s))
                     (= 1 (count (rest (:sentence s))))
                     (symbol? (second (:sentence s))))]
      (second (:sentence s)))))

(defn- members-in-cone
  "The membership terms stored in the contexts `sub` now sees — the candidates a
  genlCx edge's visibility move can newly put in joint sight.  Lazy, for the
  same budgeted consumer — and left in the cone's own order for the reason
  `instances-below` records, which was measured here: a context cycle makes the cone the
  whole graph, so sorting it before the first term came out cost
  `retract-context-cycle-scaling` a 3.4x growth against a 2x bound."
  [kb sub]
  (let [tax (:taxonomy kb)]
    (for [c     (filter symbol? (tax/context-up tax sub))
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
  * `(genlCx Sub Super)` — visibility itself moved, so the roots are `:all` and
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

      genlCx
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
;; behind the same O(1) gate — the four set-emptiness reads `constraint-nogoods` names.

(def ^:private clash-declaration-functors
  "Sentence functors whose arrival implicates content already stored.  A membership or
  a relation fact needs no entry here: it is its own candidate, found in the region."
  '#{disjoint disjointMetatype genl genlCx functional asymmetric})

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

(defn- clash-marked-below
  "Every predicate a `functional` or `asymmetric` mark reaches — the marked ones and
  everything beneath them, as one set.

  **A mark is read down the hierarchy and not off the exact functor**, for the reason the
  checks read it that way: a `genl` edge says the sub's tuples *are* the super's, so
  `(functional parentOf)` convicts two `fatherOf` mothers of one child, and
  `checks/functional-clashes` and `checks/asymmetry-problems` both probe at the marked
  predicate.  Every pass that answers those two kinds gates on this same question, and
  gating one of them on the exact functor made it blind to the descension the checks
  implement: a pair whose only mark sat on a super-predicate was dropped before any check
  could see it, so a clash the assert door refuses was never weighed or reported.

  **Asked from the marked end, because the askers are per trigger.**  `f` is convictable
  iff some marked predicate sits at or above it; `specs` and `genls` are reflexive and
  mutually inverse, so that is exactly `f ∈ ⋃ specs(marked)`.  Asked the other way it is
  `genls(f)` per predicate asked about — and a batch of `genl` edges asks once per arriving
  edge, a batch being a hierarchy, so those walks nest and sum to n²/2 over a union holding
  n.  `tax/specs`' shape one relation over, and `closure-of`'s memo cannot span them, since
  it is keyed on the node a walk began at.

  Downward also survives what upward cannot.  A deferred batch leaves the relation
  `:loose?`, and `reachable-in?` withholds its depth potential while it is, so the pruned
  `genl?` that would answer *no mark above* in O(1) degenerates to a full walk in exactly
  the case the cost appears.  A descendant walk uses no potential at all.

  **Free on a KB that declares neither**, which is every bulk load: the rosters are read
  first and an empty pair seeds an empty walk."
  [tax]
  (tax/specs-of-all tax (into (tax/props tax :functional)
                              (tax/props tax :asymmetric))))

(def ^:dynamic *clash-marked-below*
  "A `delay` over `clash-marked-below` for the pass in flight, or nil.

  Bound once per pass rather than computed per asker, and a `delay` rather than a value
  because most passes never ask: a KB declaring no mark, or a region carrying no binary
  fact, pays nothing.  The taxonomy does not move inside a pass — every asker reads — so
  one answer serves all of them, and the next pass builds its own.

  **Lazy rather than hybrid, deliberately.**  Building costs the marked roster's
  descendants, which on a real KB is the roster: the shipped ontology declares ten
  predicates between `CxCore` and `kb/upper/`, and not one of them has a sub-predicate.
  Asking upward costs `genls(f)` per asker.  So the crossover sits near one asker, and
  what this loses on is a pass carrying a single trigger under a mark near the root of a
  wide hierarchy.
  Sizing both and picking — the way the `genlCx` cone's two ends are sized — would win that
  back and cost a threshold, and there is no measurement yet saying it is worth one."
  nil)

(defn- marks-above?
  "Is any `functional` or `asymmetric` mark at or above predicate `f`?

  The only thing any pass asks about a mark, and the reason the answer is a set membership
  rather than the marks themselves: every gate here wanted the boolean.  Unbound, it
  answers from a delay of its own, so correctness never rests on the binding."
  [tax f]
  (contains? @(or *clash-marked-below* (delay (clash-marked-below tax))) f))

(defn- predicate-sentexes
  "The believed facts of predicate `pred` — one posting list, belief-filtered.

  **What loops above it is the caller's, and every caller loops over the same thing:** a
  content-ordered spec subtree (`predicate-subtree`).  A constraint descends the predicate
  hierarchy, so what a declaration reaches back over is the subtree beneath the predicate
  it names and never this one list — a length declared of `parentOf` binds every
  `fatherOf` tuple, and a `functional` mark on `parentOf` convicts two `fatherOf` fillers
  of one slot.  A sweep reading the named predicate's own extent finds nothing at all
  where `parentOf` holds no facts of its own, which is the ordinary shape of a
  vocabulary's general spellings.

  No caller sorts the list itself, so a budget that cuts one cuts in handle order.  That
  is the residual `*exposure-instance-budget*` describes, at its widest — a predicate
  declared functional after more than the budget's worth of its facts were written."
  [kb pred]
  (when (symbol? pred)
    (for [s     (keep #(p/get-sentex (:records kb) %)
                      (p/sentexes-with-functor (:index kb) pred))
          :when (and (jtms/in? (:tms kb) (:id s)) (= :true (:truth s)))]
      s)))

(defn- predicate-subtree
  "The predicates at or below `pred` that hold stored facts, in content order — the
  vocabulary a declaration of `pred` binds, and what a retroactive sweep folds
  `predicate-sentexes` over.  `tax/specs` includes the root, so a predicate with nothing
  beneath it is the one-element subtree and the undescended reading is unchanged.

  A subtree can be most of an ontology and `genl` is the commonest edge in one, so the
  walk is filtered by index **cardinality** before it reads anything: a predicate with no
  stored facts has none to convict, and asking costs a count rather than a posting list
  and a record fetch each.  What is left to pay per trigger is one count per spec, against
  the whole subtree's extent without it.

  Content order, so which predicates a bounded sweep reaches is a function of the
  vocabulary rather than of the handle order the region came back in — `content-order`'s
  claim one level up, over a set of symbols rather than of sentexes.  Within a predicate
  nothing is sorted, for the reason `instances-below` records: the posting is lazy and a
  budgeted consumer takes a prefix of it.

  `report-arity-reach!` reads the same rule over its own roots, and has to: a length and a
  mark descend the same edge, so a pass reading either off the named predicate alone files
  its finding over `(parentOf …)` and not over `(fatherOf …)`."
  [kb pred]
  (into (sorted-set)
        (comp (filter symbol?)
              (filter #(pos? (p/count-with-functor (:index kb) %))))
        (when (symbol? pred) (tax/specs (:taxonomy kb) pred))))

(defn- subtree-facts
  "The believed facts of `pred` and of every predicate beneath it — the candidates a
  `functional` or `asymmetric` mark reaching `pred` implicates, whichever sentence
  carried it there.  Lazy, so the budgeted caller realizes only what it takes.

  Two triggers land here and the mark is what both are about: the **declaration** naming
  `pred`, and a `(genl pred super)` edge carrying a mark standing on `super` down to a
  subtree that never held one.  Both are the retroactive half of what `marks-above?`
  already gives the door, which reads every mark above a fact's own functor."
  [kb pred]
  (mapcat #(predicate-sentexes kb %) (predicate-subtree kb pred)))

(defn- declaration-implicates
  "The stored sentexes a believed declaration in the moved region puts back in
  question.  Lazy, so the budgeted caller realizes only what it takes.

  The type-separating declarations read `declaration-reach`, the same candidate rule
  the exposure pass runs — the two answer one question about one KB, so a pair one of
  them reaches and the other does not would be reported as *visible* by one mechanism
  and *decided* by the other depending on which route ran.

  `functional` and `asymmetric` have no type reach and a **predicate** reach rather than
  none: the mark descends (`marks-above?`, which is how the checks read it), so what the
  declaration implicates is the facts of the whole spec subtree beneath the predicate it
  names (`subtree-facts`).  Reading the named predicate's own extent instead is reading
  the one thing a general spelling is usually empty of, and it descends nothing while the
  door descends everything — `checks/functional-clashes` and `checks/asymmetry-problems`
  convict a `fatherOf` pair under `(functional parentOf)` whichever spelling arrives last.
  **And a pair this sweep does not reach is missed permanently rather than late**: the
  sweep is the only route in, so nothing puts the pair in `:clashes`, and `:clashes` is
  the whole of what makes a later settle re-examine one.

  **`(genl sub super)` therefore reaches twice**, and the two halves are about different
  content: `sub`'s instances gain `super`'s ancestors, which is the membership reading
  above, *and* a mark standing on `super` descends to a subtree that never held one,
  which is the same predicate reach the declaration has.  The second half is gated on a
  mark actually being up there — `genl` is the commonest edge in an ontology, and one
  under no marked predicate must cost the pass a `props-over` read and nothing else.

  The budget in `left` bounds the **enumeration** and is debited by what this trigger
  spends of it (`take-budgeted`) — never by the survivors.  Budgeting survivors instead
  would make a `keep?` that rejects everything walk the whole extent looking for one,
  which is precisely the shape a large ontology is mostly made of.  The `genl` arm's two
  reaches share that one volatile, so the membership half spends first and the predicate
  half reads what is left with no arithmetic between them.

  `:cut?` says the budget ran out **inside** this trigger's reach, which is what makes
  the difference between a trigger swept in full and one whose remaining instances were
  never looked at.  A caller that files bounded work as full coverage is the failure
  `cut-notice` exists to prevent on the reporting path, and this is the same reading for
  the deciding one."
  [kb sen left]
  (let [[f a] sen
        tax (:taxonomy kb)
        ;; both type-separating shapes end the same way: bound the enumeration, keep the
        ;; terms that could really be convicted, and take their memberships
        implicated (fn [{:keys [enumerate keep?]}]
                     (let [[terms cut?] (take-budgeted left enumerate)]
                       {:cut?     cut?
                        :sentexes (mapcat #(membership-sentexes kb %) (filter keep? terms))}))
        ;; ...and the predicate reach a descending mark has, which is the subtree's facts
        ;; rather than the named predicate's own posting list
        marked (fn [pred]
                 (let [[ss cut?] (take-budgeted left (subtree-facts kb pred))]
                   {:cut? cut? :sentexes ss}))]
    (cond
      (contains? '#{disjoint disjointMetatype genlCx} f)
      (implicated (declaration-reach kb sen))

      (contains? '#{functional asymmetric} f)
      (marked a)

      ;; the one trigger with both reaches, spending one budget between them: the
      ;; membership half first, the predicate half out of what it left
      (= 'genl f)
      (let [types (implicated (declaration-reach kb sen))]
        (if-not (marks-above? tax a)
          types
          (let [preds (marked a)]
            {:cut?     (or (:cut? types) (:cut? preds))
             :sentexes (concat (:sentexes types) (:sentexes preds))})))

      ;; `(M T)` — the shape the taxonomy names rather than the vocabulary, and a `cond`
      ;; rather than a `case` arm for exactly that reason: there is no functor to
      ;; dispatch on
      (metatype-member? kb sen)
      (implicated (metatype-member-reach kb f a))

      ;; total on purpose: a functor added to `clash-declaration-functors` without an arm
      ;; here sweeps nothing and spends nothing, which is a reading the caller can act on
      :else {:cut? false :sentexes nil})))

(defn- content-order
  "Sentexes in **content** order — the sentence, then the context.

  Every budgeted sweep over a moved region walks in this order, `report-arity-reach!`'s
  `sorted-set` of predicates included.  A region arrives as a handle *set*, and a handle
  is allocation order, so a sweep that walked it as it came would spend one
  `*exposure-instance-budget*` on different members depending on which order the same
  knowledge arrived in — and past the budget the nogoods minted, and therefore what the
  KB believes, would differ with it.  Order independence is a property, not a tendency
  (docs/nmtms.md).

  Ordered by `nm/compare-form`, structurally: no printed key, so no String is allocated
  per comparison and no ambient `*print-length*` can elide two long sentences to one
  prefix and drop the sweep back onto the region's iteration order.  Through
  `nm/sort-by-content-key`, so the `[sentence context]` key is built once per sentex and a
  region of one is left as it came."
  [sentexes]
  (nm/sort-by-content-key (juxt :sentence :context) sentexes))

(def ^:dynamic *arbitration-cut*
  "A volatile collecting the declarations whose retroactive **arbitration** sweep the
  instance budget did not finish, or nil — and a nil sink records nothing.

  The exposure pass files its `:exposure-truncated` entry from inside itself, because it
  runs once per settle and files once.  This sweep cannot: `constraint-nogoods` runs once
  per settle **pass**, so a sweep reporting where it was cut would file an entry per pass
  rather than per settle — and `cut-notice` carries what over-reporting a shared budget
  costs, measured at 41,500 entries against a ledger that keeps 1,000.  So the
  readings accumulate here and `settle-finish` files one, beside the exposure pass's.

  A volatile rather than an atom, for the reason `integrate/*removed-sink*` gives: the
  engine is single-writer, and this sits on the settle path."
  nil)

(defn- note-arbitration-cut!
  "Record `sen` as a declaration whose implicated content this settle did not finish
  examining — cut short mid-reach, or reached after the budget was already spent."
  [sen]
  (when-let [sink *arbitration-cut*] (vswap! sink conj sen)))

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
  re-checks, under-sweeping would miss a clash — and a trigger it did not finish is
  recorded in `*arbitration-cut*` rather than passed over in silence.

  **The sweep runs on a rebuild too, and that is not an oversight.**  Where the region
  really is every stored sentex the sweep is redundant — `moved` already holds every
  believed sentex, and everything the sweep can yield is a believed membership or fact —
  so skipping it there would be free.  But `*rebuilding?*` does not say the region is
  everything: `recover` binds it around two settles, and the second one's region is only
  what re-recording the refusals moved.  A declaration sitting in *that* region needs its
  sweep, and a KB that came up without it would disagree with one that never restarted —
  the same objection `constraint-nogoods` records for staying on through a rebuild.  So
  the flag gates the *report* (`report-arbitration-cut!`) and not the work: a cheap
  proxy is the wrong thing to hang belief on."
  [kb touched revisit]
  (let [believed (comp (keep #(p/get-sentex (:records kb) %))
                       (filter #(jtms/in? (:tms kb) (:id %)))
                       (filter #(= :true (:truth %))))
        sweeping? (checks/arbitrating? kb)
        ;; `revisit` ahead of `touched` and each half in content order: the sweep below
        ;; is budgeted, so which triggers it reaches must not depend on the handle order
        ;; either set came back in (`content-order`).
        ;;
        ;; **Ordered only when something reads the order.**  The sweep is the only reader
        ;; and it runs under `arbitrating?`; the other consumer is `(set moved)` on the
        ;; way out, which a sort cannot move.  So a `:refuse` KB — the default — sorted
        ;; the region twice per settle to feed a pass that was never going to run.
        ordered (if sweeping? content-order identity)
        moved (into (vec (ordered (into [] believed revisit)))
                    (ordered (into [] believed touched)))
        left  (volatile! (long *exposure-instance-budget*))
        swept (when sweeping?
                (mapcat (fn [s]
                          (let [sen (:sentence s)]
                            (when (and (sequential? sen)
                                       (or (contains? clash-declaration-functors (nm/functor sen))
                                           (metatype-member? kb sen)))
                              ;; A trigger reached after the budget is spent went unswept
                              ;; as surely as one cut off mid-reach, so it is asked the
                              ;; same question rather than filed on the arithmetic — which
                              ;; is what `take-budgeted`'s probe past the cap buys, and
                              ;; why a declaration whose reach is empty is not counted
                              ;; here as one this settle failed to finish.
                              (let [{:keys [cut? sentexes]}
                                    (declaration-implicates kb sen left)]
                                (when cut? (note-arbitration-cut! sen))
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
  "Everything a clash's existence depends on **beyond the two sentexes and the `genl`
  closure**: the separations, the metatypes whose members separate each other and *which
  types those members are*, the two predicate properties, and the generation of the
  context closure a separation is read through.

  Cheap to compute and cheap to compare — five small collections and one counter, none of
  them proportional to the KB — which is what lets `clash-nogoods` separate *nothing that
  decides clash-ness has moved* from *something has*, without re-deriving anything in
  order to find out.

  The five are **values**, so an unchanged separation set compares equal and a settle that
  moved none of them abandons nothing.  The membership map is here rather than only the
  metatype roster because a metatype separates by being *consulted*: `(disjointMetatype
  M)` stays marked while `(M b_t)` leaves, and the pair `(a_t X)` / `(b_t X)` that mark
  was separating stops being separated with nothing else moving at all — no declaration
  written, no closure touched, and neither member in the region.  A member *arriving* is
  its own sentex and reaches its pairs through the retroactive sweep
  (`metatype-member-reach`); a member leaving has no sentex left to sweep from, so this
  is what says the answer moved.

  The `genlCx` counter is not a value, and it is here anyway: an asker is a context
  that sees both halves of a pair, so which contexts can convict a pair is a question
  about the context relation as a whole rather than about either half's own reading of
  it.  The `genl` relation is the one whose reading *is* per type, and it is narrowed per
  pair instead (`genl-view`)."
  [tax]
  [(tax/disjoint-pairs tax)
   (tax/disjoint-metatypes tax)
   (into {} (map (juxt identity #(tax/metatype-members tax %)))
         (tax/disjoint-metatypes tax))
   (tax/props tax :functional)
   (tax/props tax :asymmetric)
   (tax/relation-gen tax :genlCx)])

(defn- genl-view-keys
  "The `[type context]` keys a known pair reads the `genl` closure at — one per member —
  or **nil** for a pair this narrowing cannot decide, which re-derives.

  A pair of unary memberships `(T x)` / `(U x)` is decided by `tax/disjoint?` of the two
  functors and nothing else the `genl` relation holds.  Both sides always convict through
  the *exact* stored membership rather than through an entailing one: disjointness is
  inherited downward, so a supertype of `U` separated from `T` leaves `U` separated from
  `T` too, and `U` is among the term's types because its membership is stored and
  believed.  So the two functors, read from the two contexts, are the whole of what a
  `genl` edge could move about the pair.

  Every other shape answers nil.  A `functional` or `asymmetric` pair is convicted
  through `res/matches-visible` over the predicate's **spec** closure and through
  argument-position preservation, so what it reads is not bounded by the names its two
  sentences carry, and the honest reading of that is that this cannot decide it."
  [recs pr]
  (reduce (fn [acc h]
            (if-let [sx (p/get-sentex recs h)]
              (let [sen (:sentence sx)]
                (if (and (sequential? sen) (= 1 (nm/arity sen)) (symbol? (nm/functor sen)))
                  (conj acc [(nm/functor sen) (:context sx)])
                  (reduced nil)))
              (reduced nil)))
          #{} pr))

(def ^:private scoped-reading
  "What `genl-view` answers where a member's own context sees less of the `genl` relation
  than the KB holds.  `clash-nogoods` treats it as *no reading*, so a pair holding one
  re-derives — two readings that each said **less than everything** did not thereby say
  the same thing."
  ::scoped)

(defn- genl-view
  "What `[t ctx]` reads through the `genl` closure, as a value: the global supertype
  closure of `t` where `ctx` already sees the whole of it, and `scoped-reading` where it
  does not.

  The global closure rather than `ctx`'s own, because the readers are the **askers** — a
  pair split across two contexts is convicted from a third that sees both — and an
  asker's reading is neither of the two.  What ties them is a squeeze.  Visibility is
  monotone: an asker `k` that sees `ctx` sees every context `ctx` does, so
  `genls(t, ctx) ⊆ genls(t, k) ⊆ genls(t)`, and an asker that convicts a pair through
  this member does see its context, since that is where the membership it names is
  stored.  So where the two ends of that sandwich are equal, every asker inside it reads
  the same set, and an unchanged reading is unchanged for all of them at once.

  Where they are not equal the sandwich says nothing about the middle — an edge some
  asker can see and `ctx` cannot may leave that asker's view while both ends stand — so
  the answer is the marker and the pair re-derives.  That is the rare case:
  `tax/visible-ctxs` hands back the global closure itself, the identical object, for any
  context that sees every context a `genl` edge was asserted from."
  [tax [t ctx]]
  (let [all (tax/genls tax t)]
    (if (= all (tax/genls tax t ctx)) all scoped-reading)))

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
             2 (marks-above? (:taxonomy kb) (nm/functor sen))
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
      2 (let [f   (nm/functor sen)
              tax (:taxonomy kb)
              ;; **The posting each property could hold a partner in, and only that one.**
              ;; A `functional` partner is another filler of the same slot, so it shares
              ;; argument 1; an `asymmetric` partner is the converse, whose argument 1 is
              ;; *this* sentence's argument 2.  Reading the other posting returns nothing
              ;; the functor filter keeps — and on a term shared across an extent that
              ;; posting *is* the extent, which turns a per-assert cost into one that
              ;; grows with the KB (`perf`'s `constraint-exposure-shared-arg`).  A
              ;; predicate carrying both properties reads both, which is the only case
              ;; that ever needed to.
              ;; Both marks read down the hierarchy (`marks-above?`), so a mark on a
              ;; super-predicate selects its posting exactly as one on the functor does.
              fun   (tax/props-over tax :functional f)
              asym  (tax/props-over tax :asymmetric f)
              marks (into (set fun) asym)
              srcs (cond-> []
                     (seq fun)  (conj (first as))
                     (seq asym) (conj (second as)))
              ;; **The partner need not share this sentence's functor.**  Under
              ;; `(functional parentOf)` a `motherOf` filler is a partner of a `fatherOf`
              ;; one — that is the whole of what descending the mark means — so the
              ;; exact-functor test dropped exactly the pairs the descension exists to
              ;; catch.  What it does have to be is a tuple of a predicate one of *these*
              ;; marks reaches, which is the narrowing the functor test was standing in
              ;; for while a mark could only sit on the functor itself.  The same functor
              ;; is the common case and still answers without a closure read.
              partner? (fn [p]
                         (let [g (nm/functor (:sentence p))]
                           (or (= f g)
                               (and (symbol? g)
                                    (let [up (tax/genls tax g)]
                                      (boolean (some #(contains? up %) marks)))))))]
          (into #{} (comp (mapcat #(believed-at-arg1 kb %))
                          (remove #(= own (:id %)))
                          (filter partner?)
                          (map :context))
                srcs))
      #{})))

(defn- clash-vantages
  "The contexts `s`'s definitional question is asked **from**, beyond its own.

  The checks are scoped to the context they are asked in, and rightly — a context is
  convicted only on grounds it can see (`checks/disjoint-problems`).  But a pair whose
  halves sit in two contexts is visible from neither of them alone: `CxGen` is
  general, `CxSpec` sees it, and only `CxSpec` has both memberships in view.
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
  pair is weighed wherever it can be seen whole.  Nothing *here* is paid under `:refuse`:
  the gate is read before the argument roots are.  The roots are read on that policy by
  another route — `expose-constraint-clashes!` computes the same vantages to report from
  — so this is where the arbitration stops paying, not where the KB does."
  [kb s]
  (cons (:context s)
        ;; vantages are contexts (symbols), so `compare-form` reduces to `compare` — a
        ;; bare sort gives the same order with no per-comparison form-rank dispatch
        (when (checks/arbitrating? kb) (sort (clash-vantages kb s)))))

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
  satisfies the definitional ones first.

  **A `genl` edge is weighed per pair, not per KB.**  Every edge activation and
  deactivation bumps one counter, so a counter in the vocabulary says *some* edge moved
  and never *which*, and a lone edge separating nothing would abandon the whole carry.
  What each pair actually reads through that relation is the supertype closure of the two
  types its sentexes name (`genl-view`), so the closures are what the memo stamps and
  compares — the reading is per type and per context, and a pair whose reading stands is
  a pair the edge was not about.  `taxonomy/moved-touches?` is the same move one file
  down: compare the region against what the cache rests on, rather than a stamp anything
  can bump."
  [kb touched]
  (let [tms   (:tms kb)
        recs  (:records kb)
        tax   (:taxonomy kb)
        vocab (clash-vocabulary tax)
        gen   (tax/relation-gen tax :genl)
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
        ;; ...and the `genl` half of it, per pair.  `:keys` is what each pair reads the
        ;; relation at, recorded when the pair was derived so no record has to be fetched
        ;; to recover it; `:views` is what those readings said at the last stamp.  A pair
        ;; with no recorded keys is one this cannot decide and re-derives.  The whole test
        ;; is skipped when the relation's generation stands, since then no reading can
        ;; have moved and the closures are the identical objects the memo holds.
        gen?    (not= gen (:gen prev))
        keys-of (:keys prev {})
        view-of (memoize (fn [k] (genl-view tax k)))
        views   (:views prev {})
        seen?   (fn [pr]
                  (if-let [ks (get keys-of pr)]
                    (every? (fn [k]
                              (let [v (view-of k)]
                                (and (not= scoped-reading v)
                                     (= (get views k ::gone) v))))
                            ks)
                    false))
        revisit (cond stale? live
                      gen?   (into #{} (filter (fn [pr] (or (moved? pr) (not (seen? pr))))) live)
                      :else  (into #{} (filter moved?) live))
        carried (if stale?
                  {}
                  (into {} (filter (fn [[pr _]] (and (contains? live pr)
                                                     (not (contains? revisit pr)))))
                        (:nogoods prev)))
        cands   (let [raw (if *incremental-clashes*
                            (clash-candidates kb touched (into #{} (mapcat identity) revisit))
                            (all-believed kb))]
                  ;; Examine a term's memberships consecutively: `disjoint-problems` reads
                  ;; every membership of the term (`types`) and its arg-1 postings
                  ;; (`membership-handles`) off disk for *each* membership it is asked of,
                  ;; so a term holding m types has its record set fetched ~m times.  Left
                  ;; in arrival order those m calls are scattered across the pass and the
                  ;; record LRU evicts between them, making the fetch O(m²); clustered by
                  ;; the arg-1 term they run back-to-back and every re-read after the first
                  ;; is a cache hit — O(m).  Order does not change the result: entries are
                  ;; keyed on the handle pair and content-ordered (below), which
                  ;; `constraint_nogood_test`'s permutation cases lock down.  Keyed on the
                  ;; term's hash — an int clusters equal terms with no per-record string.
                  (sort-by (fn [s] (let [sen (:sentence s)]
                                     (if (sequential? sen) (hash (first (nm/args sen))) 0)))
                           raw))
        entries
        (mapcat (fn [s]
                  (when (or (not *incremental-clashes*) (could-clash? kb s))
                    (mapcat
                     (fn [asker]
                       (keep (fn [v]
                               (let [opp (:opposing-handle v)]
                                 (when (and (not= opp (:id s)) (jtms/in? tms opp))
                                   (let [other (:sentence (p/get-sentex (:records kb) opp))
                                         [a b] (sort nm/compare-form [(:sentence s) other])]
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
    ;; traversal.  The entries for one pair share `:sentence` (its halves are already
    ;; content-ordered above) and `:priority`, so `:kind` then `:sentence` decides,
    ;; compared structurally rather than by a `pr-str` of the whole map.
    (let [derived (into {} (map (fn [[pr es]]
                                  [pr (first (sort-by (juxt :kind :sentence)
                                                      nm/compare-form es))]))
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
      (let [pairs (into found
                        (filter (fn [pr]
                                  (or (contains? found pr)
                                      (not (every? #(jtms/in? tms %) pr)))))
                        live)
            ;; ...and what each of them reads the `genl` relation at.  Read off the records
            ;; **only for a pair this settle derived**, and carried for every other: a
            ;; handle's functor and context never move, and a pair that was not derived
            ;; here was remembered last settle and brought its keys with it.  So this is
            ;; proportional to what was found rather than to what stands, which is the
            ;; property of the memo it belongs to.  `fresh` is what those pairs added, and
            ;; what the readings below have to be extended by.
            [ks fresh]
            (reduce (fn [[m nk] pr]
                      (if (contains? m pr)
                        [m nk]
                        (let [k (genl-view-keys recs pr)]
                          [(assoc m pr k) (if k (into nk k) nk)])))
                    [keys-of #{}] (keys derived))
            ;; ...and pruned only when a pair actually left.  The reduce can only have
            ;; added, and it added exactly the pairs `pairs` gained, so a count that still
            ;; agrees is a domain that still agrees.
            ks    (cond-> ks (not= (count ks) (count pairs)) (select-keys pairs))]
        (reset! (:clashes kb)
                {:vocab   vocab
                 :gen     gen
                 :nogoods answer
                 :pairs   pairs
                 :keys    ks
                 ;; The readings, and they are **taken over the whole memo only when the
                 ;; relation moved** — the settle that is already weighing every pair
                 ;; against them.  Every other settle carries them and adds only what the
                 ;; pairs it found ask for, so a KB writing no taxonomy edge pays for the
                 ;; region rather than for the standing set.  The carried half cannot be
                 ;; stale for the reason the whole test rests on: an unchanged generation
                 ;; is an unchanged closure, and `tax/genls` hands back the object it
                 ;; already had.
                 :views   (if gen?
                            (into {} (map (fn [k] [k (view-of k)]))
                                  (into #{} (comp (keep identity) cat) (vals ks)))
                            (reduce (fn [m k] (if (contains? m k) m (assoc m k (view-of k))))
                                    views fresh))}))
      ngs)))

(def ^:dynamic *skip-constraint-nogoods*
  "When true, `constraint-nogoods` takes the same branch a KB declaring no
  disjointness/functional/asymmetric feature takes — it derives no definitional-clash
  nogoods and resets `(:clashes kb)` to empty.  Sound to skip **only when the clash
  scan is belief-neutral**, i.e. every standing clash is a `:dilemma`/`:hard` tie that
  disbelieves neither side (`decide-nogood`): then the scan produces no defeat and
  omitting it changes no belief, only the recorded dilemmas a later `contradictions`
  read or solve would report.  A KB with a strength-differentiated clash-loser must
  NOT set this — the loser would be wrongly believed.  For the `meta.edn`-gated warm
  reload, whose stamp certifies `clash-losers = 0` for the fingerprinted records."
  false)

(defn- constraint-nogoods
  "`clash-nogoods`, behind the O(1) gate that makes it free for a KB declaring none of
  the three features — which is most of them.  Four set-emptiness reads and not one:
  disjointness is spelled two ways (`disjoint-pairs` and `disjoint-metatypes`) and the
  `functional` and `asymmetric` props are read separately, and a KB declaring none takes
  all four, since the `or` short-circuits only on a hit.

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
    (if (or *skip-constraint-nogoods*
            (not (or (seq (tax/disjoint-pairs tax))
                     (seq (tax/disjoint-metatypes tax))
                     (seq (tax/props tax :functional))
                     (seq (tax/props tax :asymmetric)))))
      ;; Nothing separates anything and no predicate is declared functional or
      ;; asymmetric, so no pair can clash — which makes this the one place the whole
      ;; candidate set can be dropped rather than re-examined.  It has to be dropped
      ;; here: the gate short-circuits `clash-nogoods`, so retracting the last
      ;; separation would otherwise leave its pairs remembered with nothing ever able
      ;; to look at them again.
      (do (reset! (:clashes kb) {}) #{})
      ;; one `clash-marked-below` for the pass, past the gate that already proved a mark
      ;; exists.  `could-clash?` asks per candidate and `declaration-implicates` asks per
      ;; `genl` trigger, so the askers scale with the region while the answer does not.
      ;; Clash detection reads `genls`/`specs` for every candidate but writes no edge — the
      ;; taxonomy is still for its span — so it holds each closure it walks in one pass cache
      ;; and never re-walks it, where the gen-stamped memo is retired under it by the belief
      ;; the wider settle moves.  A fresh atom per call, dropped when the pass returns.
      (binding [*clash-marked-below*             (delay (clash-marked-below tax))
                tax/*closure-pass-cache*         (atom {})
                tax/*visible-neighbours-cache*   (atom {})
                tax/*separation-frame-cache*     (atom {})]
        (clash-nogoods kb (jtms/touched (:tms kb)))))))

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
  the instances below its types on those types; a genlCx edge focuses the
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
                 (let [[seen cut?] (take-budgeted left terms)]
                   (when cut? (vswap! trunc conj sen))
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
            (contains? '#{disjoint disjointMetatype genl genlCx} f)
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
            (sort terms)))))                         ; terms are symbols — bare sort is the same content order

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
            ;; Off the cut and not off `entries`, which is `cut-notice`'s whole argument:
            ;; the sweep above can spend the budget on terms that convict nobody, and a
            ;; pass with nothing to report is exactly the one whose silence reads as
            ;; coverage.
            cut     (cut-notice :exposure-truncated truncated
                                {:sweep       "exposure"
                                 :unit        "instances"
                                 :noun        "trigger"
                                 :count-key   :triggers
                                 :consequence "clashes they implicate are unreported"})
            entries (cond-> entries cut (conj cut))]
        (when (seq entries)
          (violations/report kb entries))))))

;; ---- the other two kinds, across the same edge ---------------------------
;;
;; The pass above answers `disjoint` and only `disjoint`.  The other two arbitrable
;; kinds have the same cross-context hole and, until this, no reporting path at all:
;; the assert door is scoped to the writer's own cone so it sees one half and refuses
;; nothing, and under `:refuse` `clash-askers` withholds the vantages that would see
;; the pair whole.  So a `functional` slot filled either side of a `genlCx` edge,
;; and an `asymmetric` claim written across one, stood believed and unmentioned — under
;; the strictest policy, which is the one chosen precisely to let nothing through.
;;
;; **Reported, never decided**, exactly as the disjointness entry is: the ledger says a
;; pair is visible from somewhere, `contradictions` stays the answer to what was
;; *arbitrated*, and belief is untouched.  A pair this settle did arbitrate is excluded
;; on the same grounds `exposed-clashes-for-term` excludes one — decided is not exposed.
;;
;; **Under `:arbitrate` none of it runs**, and there it would be wrong to: the vantages
;; are asked there, so the pair is weighed rather than reported, and reporting it here
;; as well would have two mechanisms claim one clash.

(defn- constraint-facts-in-cone
  "The believed binary facts of a declared `functional` or `asymmetric` predicate stored
  in the contexts `sub` now sees — the candidates a `genlCx` edge's visibility move
  can newly put in joint sight.

  The exact parallel of `members-in-cone`, which answers the same question for the
  disjointness pass, and lazy for the same budgeted consumer: a context cycle makes the
  cone the whole graph, so nothing here may be realized or sorted before its first
  element comes out."
  [kb sub]
  (let [tax (:taxonomy kb)]
    (for [c     (filter symbol? (tax/context-up tax sub))
          s     (keep #(p/get-sentex (:records kb) %)
                      (p/sentexes-in-context (:index kb) c))
          :let  [sen (:sentence s)]
          :when (and (jtms/in? (:tms kb) (:id s))
                     (= :true (:truth s))
                     (sequential? sen)
                     (= 2 (count (nm/args sen)))
                     (let [f (nm/functor sen)]
                       (and (symbol? f)
                            (marks-above? tax f))))]
      s)))

(defn- constraint-exposure-candidates
  "The believed binary facts in the moved region whose predicate is declared
  `functional` or `asymmetric` — the only sentexes that can be half of one of those
  clashes.

  Read straight off the region, so an ordinary write costs the region and no sweep: the
  disjointness pass beside it has to work out which *instances* a moved declaration or
  edge implicates, and on a plain assert this does not. Unordered, unlike every budgeted
  sweep — the answer is a function of the *set* of pairs found
  (`constraint-exposure-entries` groups and ranks on content), so ordering the region
  walk would be an `n log n` per settle that decides nothing.

  **Two edges in the region reach past it**, and both have to, because each moves an
  ingredient of the pair while leaving the two halves themselves untouched — neither is
  relabelled, so neither is in the region, and reporting the same knowledge only when the
  edge happened to arrive first is the arrival-order dependence this whole pass exists to
  remove. `(genlCx w c)` moves **visibility**: a pair already stored and already believed
  becomes jointly visible, and what it implicates is the binary facts in the cone
  (`constraint-facts-in-cone`, the parallel of the `members-in-cone` the disjointness
  pass reads through `declaration-reach`'s own `genlCx` arm). `(genl sub super)` moves the
  **mark**: a standing `(functional super)` descends to a subtree that never carried one,
  so a pair of `sub` facts either side of a visibility edge starts clashing without any
  contexts moving at all, and what it implicates is the subtree's facts
  (`subtree-facts`). The disjointness pass has the analogous arm for the analogous reason
  — `declaration-reach`'s `genl` case, over the memberships an edge newly separates.

  The predicate edge is gated on a mark actually being above it (`marks-above?`), since
  `genl` is the commonest edge in an ontology and one under no marked predicate must cost
  a `props-over` read and nothing more. Both spend the same `*exposure-instance-budget*`,
  and the edges are ordered, unlike the region walk, because a budgeted enumeration's
  *prefix* is what the cap decides and that may not depend on the order a region or a cone
  came back in.

  **One arrival order is still not covered**, and it is an absence rather than an
  oversight: a `(functional P)` or `(asymmetric P)` **declaration** arriving after the
  facts it convicts. `clash-candidates` sweeps for that and only when
  `checks/arbitrating?`, so under this policy nothing does — exactly as the door refuses
  an identical fact written one line later.

  The property reads are the unscoped ones `could-clash?` uses and over-approximate for
  the same reason: a candidate that convicts nothing costs one check that finds nothing,
  where one left out is a pair nobody reports.

  Returns `{:candidates [sentex …] :unswept [sentence …]}` — the second naming the edges
  whose reach the budget cut short, so a bounded sweep never reads as full coverage."
  [kb touched]
  (let [tax   (:taxonomy kb)
        declared? (fn [s]
                    (let [sen (:sentence s)]
                      (and (sequential? sen)
                           (= 2 (count (nm/args sen)))
                           (let [f (nm/functor sen)]
                             (and (symbol? f)
                                  (marks-above? tax f))))))
        believed  (comp (keep #(p/get-sentex (:records kb) %))
                        (filter #(jtms/in? (:tms kb) (:id %)))
                        (filter #(= :true (:truth %))))
        region    (into [] believed touched)
        edges     (content-order
                   (filterv (fn [s]
                              (let [sen (:sentence s)]
                                (and (sequential? sen)
                                     (contains? '#{genl genlCx} (nm/functor sen))
                                     (= 2 (count (nm/args sen)))
                                     (every? symbol? (nm/args sen)))))
                            region))
        left      (volatile! (long *exposure-instance-budget*))
        unswept   (volatile! [])
        swept     (into []
                        (mapcat
                         (fn [e]
                           (let [sen   (:sentence e)
                                 [x y] (nm/args sen)
                                 ;; each edge reads its own end: the cone the newly
                                 ;; seeing context reaches, or the subtree the mark newly
                                 ;; descends to.  A `genl` under nothing marked
                                 ;; enumerates nothing and spends nothing.
                                 ends  (if (= 'genlCx (nm/functor sen))
                                         (constraint-facts-in-cone kb y)
                                         (when (marks-above? tax x)
                                           (subtree-facts kb x)))
                                 [taken cut?] (take-budgeted left ends)]
                             (when cut? (vswap! unswept conj sen))
                             taken)))
                        edges)]
    ;; the cone reader filters to a marked binary fact itself; the subtree reader hands
    ;; back whatever the predicates hold, so both are put through the region's own test
    {:candidates (into (filterv declared? region) (filter declared?) swept)
     :unswept    @unswept}))

(defn- constraint-exposure-entries
  "The `functional` and `asymmetric` clashes the moved region forms across a visibility
  edge, one entry per handle pair, as a **function of the pair's content alone**.

  Each is re-derived by asking the very check the assert door asks
  (`checks/arbitrable-violations`), from the vantages `clash-vantages` names — the same
  two reads `clash-askers` makes under `:arbitrate`, asked here for a report instead of
  for a nogood.  So the discovery cannot drift from the refusal, and widening the
  vantages is not what closes the gap: the pair was always visible from there, and what
  was missing was an entry kind to say so.

  **Both halves can be in one region**, and each convicts the other, so the pair would
  otherwise be filed twice or once depending on which sides the region happened to hold
  — arrival order deciding a report, which is the defect `clash-nogoods` records the
  same fix for.  The entry is keyed on the handle pair, the two `[sentence context]`
  halves are ordered by their printed form rather than by which was walked, and the
  top-level `:sentence` / `:context` name the **first** of that ordered pair rather than
  the side that found it."
  [kb candidates arbitrated]
  (let [tms (:tms kb)
        tax (:taxonomy kb)
        ;; **Content order, and the context is half of it.**  `nm/compare-form` compares
        ;; the `[sentence context]` half element by element, so it reads the sentence
        ;; *then* the context for a reason that bites here: the converse of `(P a a)` is
        ;; itself, so an asymmetric self-tuple stated in two contexts is two halves whose
        ;; sentences are equal, and a key stopping at the sentence would leave them in the
        ;; order the walk supplied.
        found
        (for [s      candidates
              asker  (sort (clash-vantages kb s))    ; contexts are symbols — bare sort is the same order
              v      (checks/arbitrable-violations kb (:sentence s) asker)
              :let   [opp (:opposing-handle v)]
              :when  (and (contains? #{:functional :asymmetric} (:type v))
                          (not= opp (:id s))
                          (jtms/in? tms opp)
                          (not (contains? arbitrated #{(:id s) opp})))
              :let   [other (p/get-sentex (:records kb) opp)]
              :when  other
              :let   [[[sa ca] [sb cb] :as halves]
                      (sort nm/compare-form
                            [[(:sentence s) (:context s)]
                             [(:sentence other) (:context other)]])
                      kind (:type v)
                      ;; The **declared** predicate, which the check knows and the halves
                      ;; do not, and both arms name it.  Two routes separate it from a
                      ;; half's own functor: argument preservation reaches an asymmetric
                      ;; converse from a *sub*-predicate, and either mark is read up the
                      ;; predicate hierarchy (`tax/props-over`), so a pair convicted under
                      ;; `(functional parentOf)` can be two `fatherOf` facts.  The `or` is
                      ;; the floor for a violation shape that names none.
                      pred (or (:pred v) (nm/functor sa))
                      ;; **Read off the pair, not off the walk.**  Which vantages a side
                      ;; is asked from is a property of that side's postings — a third
                      ;; fact sharing an argument adds vantages to one side and not the
                      ;; other — so reporting the asker that happened to convict makes the
                      ;; entry a function of which half the region held.  The contexts
                      ;; that see the pair whole are a function of the two halves' own
                      ;; contexts, and the convicting asker is always one of them.
                      seen (tax/maximal-common-descendant-contexts tax [ca cb])]]
          [#{(:id s) opp}
           {:violation kind
            :sentence  sa
            :context   ca
            :detail    {:pred         pred
                        :clash        (vec halves)
                        :visible-from (set seen)
                        :message
                        (str (name kind) " clash exposed: "
                             (if (= :functional kind)
                               (str pred " of " (first (nm/args sa)) " is "
                                    (second (nm/args sa)) " (in " ca ") and "
                                    (second (nm/args sb)) " (in " cb ")")
                               (str pred " cannot hold both ways, and "
                                    (pr-str sa) " (in " ca ") sits with "
                                    (pr-str sb) " (in " cb ")"))
                             ", jointly visible from "
                             (pr-str (vec (sort nm/compare-form seen))))}}])]
    ;; One entry per pair, and both the choice within a pair and the order between them
    ;; keyed on content — two vantages can both see a pair, and which was enumerated
    ;; first is not something the report may depend on.  The key is spelled out rather
    ;; than taken off `pr-str` of the whole entry: a map's printed order is a property of
    ;; how it was built, so ordering on one would be reading the walk back out.
    (let [rank (fn [e] [(:violation e)
                        (get-in e [:detail :clash])
                        (vec (sort nm/compare-form (get-in e [:detail :visible-from])))])]
      (->> (vals (group-by first found))
           (map (fn [es] (first (sort-by rank nm/compare-form (map second es)))))
           ;; `rank` carries a nested `(sort … visible-from)` — built once per entry here,
           ;; not per comparison; the per-group `first` above stays a plain sort, free at
           ;; the n=1 a single-member group almost always is
           (nm/sort-by-content-key rank nm/compare-form)))))

(def ^:private max-constraint-findings
  "How many cross-context `functional` / `asymmetric` pair entries one pass of the report
  below may file.

  The entries are bounded by neither the region nor the sweep: one slot filled from N
  contexts a single vantage sees is N−1 pairs off one arriving fact, and a `genl` edge
  carrying a mark down reaches every pair in the subtree beneath it.  The ledger keeps the
  newest 1,000 entries and logs each at `:warn`, so a pass filing one per pair evicts every
  other violation in it — the failure `cut-notice` records at 41,500 identical
  complaints.  Bounding on `*exposure-instance-budget*` is no bound at all here: that
  number is 4,096, four times the ledger, and it is a count of *enumerated instances*
  rather than of entries, so a pass could reach it without having swept anything.

  Small enough that a whole settle's findings are a rounding error against the ledger,
  wide enough that a reader meets the pattern rather than one arbitrary member of it; past
  it the count and a sample are what `:constraint-exposure-truncated` carries.  The same
  number and the same reading as `max-arity-findings`, the other pass whose reach is a
  subtree."
  8)

(defn- expose-constraint-clashes!
  "File the `functional` and `asymmetric` clashes the settle's moved region holds across
  a visibility edge.  `:refuse` only, and behind an O(1) gate on the declared vocabulary
  — a KB that declares neither property can form neither clash, and pays two `seq`s.

  **Capped, and never silently.**  One pass files at most `max-constraint-findings` pair
  entries and stops its sweeps at `*exposure-instance-budget*` instances, and either bound
  being met files one `:constraint-exposure-truncated` entry carrying both readings:
  `:pairs` against `:filed` for what was found and not named, `:unswept` for the edges
  whose reach was never walked.  One kind rather than two because a reader acts on them
  the same way — pairs are visible and unreported, and nothing went *undecided* — which is
  what separates it from `:arbitration-truncated` and from either sweep's own notice.

  **Two bounds in one entry, which is why it is built here rather than by `cut-notice`.**
  The cone sweep is bounded like every other and fires off its cut; the pair cap is a
  bound on what one pass will *file* and fires with nothing swept short at all, carrying
  a `:pairs` / `:filed` reading no sweep has.  Putting it through the shared builder
  would mean rewording the message a reader already reads, for a shape that says one
  bound where this says two.  `cut-notice`'s rule holds over the half that is a sweep all
  the same: `:unswept` is read off the cut and never off the pairs, so a cone the budget
  stopped is named whether or not the pass reported a single clash.

  Off while `*rebuilding?*`, where *newly* has no meaning, exactly as the disjointness
  pass is."
  [kb touched arbitrated]
  (let [tax (:taxonomy kb)]
    (when (and (not *rebuilding?*)
               (seq touched)
               (not (checks/arbitrating? kb))
               (or (seq (tax/props tax :functional))
                   (seq (tax/props tax :asymmetric))))
      ;; one `clash-marked-below` for the pass, past the gate that already proved a mark
      ;; exists.  The `genl` trigger asks per arriving edge and the region filter asks per
      ;; binary sentex, so the askers scale with the region while the answer does not.
      (binding [*clash-marked-below* (delay (clash-marked-below tax))]
        (let [{:keys [candidates unswept]} (constraint-exposure-candidates kb touched)
              all     (constraint-exposure-entries kb candidates arbitrated)
              over    (- (count all) max-constraint-findings)
              entries (cond-> (vec (take max-constraint-findings all))
                        (or (pos? over) (seq unswept))
                        (conj {:violation :constraint-exposure-truncated
                               :detail    {:pairs   (count all)
                                           :filed   (min max-constraint-findings (count all))
                                           :cap     max-constraint-findings
                                           :unswept (count unswept)
                                           :sample  (vec (take 3 unswept))
                                           :budget  *exposure-instance-budget*
                                           :message
                                           (str "cross-context constraint report bounded: "
                                                (when (pos? over)
                                                  (str over " further clashing pair(s) are"
                                                       " visible and unreported past the "
                                                       max-constraint-findings
                                                       "-entry cap"))
                                                (when (and (pos? over) (seq unswept)) "; ")
                                                (when (seq unswept)
                                                  (str (count unswept) " edge(s) went"
                                                       " unswept at "
                                                       *exposure-instance-budget*
                                                       " instances, so pairs their reach"
                                                       " exposes are unreported")))}}))]
          (when (seq entries)
            (violations/report kb entries)))))))

;; ---- the arity declaration that arrives after the facts ------------------
;;
;; `arity` is the one definitional check whose retroactive half neither refuses nor
;; arbitrates.  It cannot refuse — that would make the *declaration's* arrival order
;; decide, which is the objection docs/nmtms.md opens with — and it cannot arbitrate,
;; because the sentex it would pair with is the vocabulary entry the conviction is read
;; through (the comment above `checks/arbitrable-kinds` has the measurement).  What is
;; left is to say so: the facts a late declaration convicts are named in the ledger,
;; where a KB author can find them, instead of standing believed and unmentioned.

(defn- arity-bound-by
  "The predicate whose binding arity this sentence may newly supply, or nil — the root of
  the subtree the report below has to sweep.

  Three spellings, because `checks/declared-arity` reads three things.  Two **declare** a
  length: `(arity P n)`, and the predicate-type membership `(binaryPredicate P)` that says
  the same thing.  The third **inherits** one: `(genl sub super)` binds `sub` to whatever
  length `super` was declared with (`checks/inherited-arity`), so an edge is the third
  ingredient of a wrong-arity finding exactly as it is the third ingredient of an
  argument-type mint (`special/entail-under-edge`).  Without the edge arm, the same three
  sentences file a violation in two arrival orders out of three, which is the objection
  the whole retroactive half exists to answer.

  `super` is deliberately **not** a root: the edge changes what `sub` is held to and
  leaves `super` held to what it always was.

  **A fourth sentence supplies a binding and names no predicate**, which is why it is
  answered next door rather than by another arm here: all three of these are read *from a
  context*, so a `genlCx` edge rebinds by moving what a fact's own vantage can see, and
  the predicates it reaches are a sweep's answer rather than anything its two arguments
  spell.  This is one of the two functions that sweep for them
  (`arity-bindings-above-context` reads it of the cone the edge opened)."
  [kb sen context]
  (let [f (nm/functor sen)
        as (rest sen)]
    (when-let [pred (cond
                      (= 'arity f) (when (= 2 (count as)) (first as))
                      (= 'genl f)  (when (= 2 (count as)) (first as))
                      ;; through the closure, `checks/membership-arity`'s reason: a
                      ;; membership spelled with a `genl` of `binaryPredicate` declares a
                      ;; length the door reads, so a trigger matching the three literal
                      ;; functors would leave the facts it convicts unreported
                      (= 1 (count as)) (when (checks/membership-arity kb f context)
                                         (first as)))]
      (when (symbol? pred) pred))))

;; A `genlCx` edge is a binding whose sentence names no predicate, and what it implicates
;; has two ends: the facts stored **below** `sub`, whose vantage moved, and the bindings
;; stored **above** `super`, which is everything that vantage newly reaches.  Either end
;; alone is complete — a fact newly convicted is under one and its binding is over the
;; other — so the pass walks whichever is smaller, sized off `count-in-context` the way
;; `two-sided-reach` sizes a separation off its roots.  Neither end is the cheap one in
;; general: a fresh context joining the root is nothing below and the whole vocabulary
;; above, and a root context gaining a parent is the reverse, and an ontology writes both.

(defn- cone-extent
  "How many sentexes are stored across `contexts` — one `count-in-context` apiece, which
  is an O(1) read, so a cone can be sized without walking it.  Stored rather than
  believed, and whatever the sentences are: this only picks which end to enumerate, so a
  miscount costs a worse choice of end and never an answer."
  [kb contexts]
  (transduce (comp (filter symbol?) (map #(p/count-in-context (:index kb) %)))
             + 0 contexts))

(defn- predicates-below-context
  "The functors of the believed facts stored in the contexts that see `sub` — the end of
  a `(genlCx sub super)` edge's reach that the edge moved the vantage of.  Lazy, so the
  budgeted caller realizes only what it takes.

  An arity is read from the fact's own context (`checks/declared-arity`), so these facts
  are exactly the content the edge puts back in question, whichever ingredient it revealed
  to them — a declaration above `super`, or the `genl` edge that inherits one through.
  The functors are roots and not candidates: the spec expansion and the per-fact check
  beneath them decide.

  Left in the cone's own order, for the reason `members-in-cone` records: a context cycle
  makes the cone the whole graph, so nothing here may be sorted before its first element
  comes out.  The functors are a set by the time they are roots and the sweep beneath them
  is content-ordered, so what a cut prefix costs is coverage and never a different reading
  of the same coverage."
  [kb sub]
  (let [tax (:taxonomy kb)]
    (for [c     (filter symbol? (tax/context-down tax sub))
          s     (keep #(p/get-sentex (:records kb) %)
                      (p/sentexes-in-context (:index kb) c))
          :let  [sen (:sentence s)
                 f   (when (sequential? sen) (nm/functor sen))]
          :when (and (symbol? f)
                     (jtms/in? (:tms kb) (:id s))
                     (= :true (:truth s)))]
      f)))

(defn- arity-bindings-above-context
  "The predicates bound by a believed binding stored in the contexts `super` sees — the
  other end of the same edge's reach, and `predicates-below-context`'s twin in everything
  but which end it walks.  Lazy, and unsorted, for that one's reasons.

  Every spelling `arity-bound-by` reads, because all three become visible together: the
  cone the edge opened carries the declarations *and* the `genl` edges that inherit one,
  and an edge revealing only the second binds a predicate no declaration in the cone
  names."
  [kb super]
  (let [tax (:taxonomy kb)]
    (for [c     (filter symbol? (tax/context-up tax super))
          s     (keep #(p/get-sentex (:records kb) %)
                      (p/sentexes-in-context (:index kb) c))
          :let  [sen  (:sentence s)
                 pred (when (sequential? sen) (arity-bound-by kb sen (:context s)))]
          :when (and pred
                     (jtms/in? (:tms kb) (:id s))
                     (= :true (:truth s)))]
      pred)))

(defn- any-arity-declared?
  "Has the KB declared *any* predicate's arity, in either spelling — the O(1) gate that
  makes the pass below free for a KB that has not?

  The taxonomy's arity table alone is not the answer: it holds the `(arity P n)` sentexes,
  and a KB loaded without CxCore's derivation rules has only the predicate-type
  membership, which `checks/declared-arity` reads and this table never sees.  So the three
  memberships are asked too, as index cardinalities.

  **Each membership's sub-collections with it**, since `checks/membership-arity` reads the
  spelling through the `genl` closure: a KB writing `(myBinPred fatherOf)` under `(genl
  myBinPred binaryPredicate)` declares arities this gate would otherwise count none of, and
  a gate that reads narrower than the trigger it guards turns the whole report off.  The
  closure is cached and read off three fixed roots, so the gate stays a handful of
  cardinalities rather than a walk."
  [kb]
  (let [tax (:taxonomy kb)]
    (or (seq (tax/arity-declarations tax))
        (boolean (some (fn [t]
                         (some #(pos? (p/count-with-functor (:index kb) %))
                               (tax/specs tax t)))
                       (keys checks/predicate-type-arities))))))

(def ^:private max-arity-findings
  "How many per-predicate `:arity` entries one pass of the report below may file.

  The cap exists because the sweep is over a **subtree**: one binding can convict a
  thousand predicates, and the ledger keeps the newest 1,000 entries, so a pass filing one
  each would evict every other violation in it — the failure `cut-notice` records at
  41,500 identical complaints, and the one the entries below are summarized to avoid.
  Small enough that a whole settle's findings are a rounding error against the ledger,
  wide enough that a reader meets the pattern rather than one arbitrary member of it; past
  it the count and a sample are what `:arity-report-truncated` carries."
  8)

(defn- report-arity-reach!
  "File the wrong-arity facts an arity **binding** entering the moved region convicts —
  content stored before anything existed to refuse it, and therefore admitted by an
  `assert` that could not have known.

  **A binding, not a declaration**, and the difference is four arrival orders rather
  than one.  `checks/declared-arity` answers off the predicate's own declaration *or* off
  a super-predicate's, and it answers *from a context* — so the fact, the declaration, the
  `genl` edge that inherits one and the `genlCx` edge that lets a vantage see either are
  all ingredients, and any of the four can be last.  `arity-bound-by` supplies the roots
  for the three that name a predicate or an edge between two, the smaller end of the
  context edge's own reach supplies them for the one that names neither, the spec
  expansion below covers the declaration landing on a super, and together they make the
  finding a fact about the KB rather than about the order it was written in — which is
  what the door already achieves by reading the same `declared-arity` whichever sentence
  arrives.

  Reports and decides nothing.  The facts stay stored and believed, exactly as they were;
  what changes is that `(violations kb)` names the finding, with `:declared-after` carrying
  the declaration's own handle — the same convention the disjointness exposure uses to mark
  an entry as a *finding about stored content* rather than a dropped conclusion.

  **At most `max-arity-findings` entries for the pass**, one per convicted predicate and
  never one per convicted fact, each carrying that predicate's `:count` and a `:sample`.
  Both unbounded readings put the ledger's size at the mercy of what one binding descends
  to: a declaration over 4,096 wrong-arity facts filed per fact, or a subtree of 1,001
  predicates holding one apiece filed per predicate, is a pass that evicts every other
  violation from a ledger keeping the newest 1,000 — the failure `cut-notice` records at
  41,500 identical complaints on one corpus load, and a `:warn` line each on the way out.
  Past the cap a single `:arity-report-truncated` entry carries how
  many predicates convicted, how many facts in all, and a sample of the ones no entry
  names.  Nothing is lost by summarizing, and that is what separates this from a
  disjointness exposure: an exposure reports a *visibility* that took a change to create,
  while the wrong-arity facts of `P` are re-derivable from the store at any time by anyone
  who wants the list.  What the ledger owes a reader is which predicates were convicted
  and how many facts each, and that is what it says.

  **Not gated on the constraint policy.**  `:refuse` versus `:arbitrate` is a question
  about whether a writer is told no and about whose belief moves; nothing here moves
  belief or refuses anybody, so both policies get the report.

  Off while `*rebuilding?*`, like the exposure pass beside it and for the same reason: the
  entry says a declaration *newly* convicted stored content, and on a rebuild everything
  arrives at once, so there is no newly.  Budgeted off the same instance budget — a
  declaration over a predicate with a large extent implicates all of it, now over a
  *subtree* of them, and a context edge implicates the facts under it before a predicate
  has been named at all.

  **A cut sweep says so on its own entry, and the pass says so for what it never reached.**
  Two readings, because the budget is the *pass's* while the sweep is over a subtree
  rather than over one posting list.  A predicate swept short carries `:truncated` on the
  finding it filed; but the budget can also run out inside a predicate that convicts
  nothing, and then every predicate after it takes a budget of zero, examines nothing and
  has nothing to hang the flag on — so a wrong-arity fact one of them holds would be
  neither refused nor reported, and nothing would say a predicate went unlooked-at.  A
  context edge whose cone the budget cut is the same reading one ingredient earlier:
  predicates nobody looked *for*.  That is
  the failure `cut-notice` exists to refuse, so both are collected and filed as a single
  `:arity-truncated` entry off the cut, **whether or not anything was found**.

  **Two bounds in one entry, which is why it is built here rather than by `cut-notice`**,
  and `expose-constraint-clashes!` gives the same reason for the same shape.  The two
  readings count different units — predicates whose facts went unswept, and `genlCx`
  edges whose cone did, which is one ingredient earlier and so a `:edges` /
  `:edge-sample` pair no single-unit entry carries — and the message names whichever of
  them fired.  `cut-notice`'s rule is what both halves obey: read off the cut, never off
  the findings.

  Free for a KB that declares no arity at all (`any-arity-declared?`), which neither edge
  arm changes: an edge binds nothing when nothing above it was ever declared.  Cheap for a
  context edge with a small end, which is what a KB usually writes — a context placed
  before its content has nothing below it, and a root context gaining a parent has a
  vocabulary above it and not a KB."
  [kb touched]
  (when (and (not *rebuilding?*)
             (seq touched)
             (any-arity-declared? kb))
    (let [left    (volatile! (long *exposure-instance-budget*))
          ;; the predicates the budget cut short — content-ordered by construction, since
          ;; `preds` is and the sweep folds over it in that order
          unswept (volatile! [])
          ;; ...and the context edges whose cone it cut short, which is the same reading
          ;; one ingredient earlier: predicates the pass never got as far as naming
          unreached (volatile! [])
          believed (into []
                         (comp (keep #(p/get-sentex (:records kb) %))
                               (filter #(jtms/in? (:tms kb) (:id %)))
                               (filter #(= :true (:truth %))))
                         touched)
          named (into #{} (keep #(arity-bound-by kb (:sentence %) (:context %))) believed)
          ;; the ingredient that names no predicate.  Content order over the edges,
          ;; because a budget running out mid-region decides which cones were walked at
          ;; all, and that may not depend on the handle order the region came back in
          edges (content-order
                 (filterv (fn [s]
                            (let [sen (:sentence s)]
                              (and (sequential? sen)
                                   (= 'genlCx (nm/functor sen))
                                   (= 2 (count (nm/args sen)))
                                   (every? symbol? (nm/args sen)))))
                          believed))
          roots (reduce
                 (fn [acc e]
                   (let [tax         (:taxonomy kb)
                         [sub super] (nm/args (:sentence e))
                         ;; the smaller end, sized off `count-in-context` so choosing
                         ;; costs no walk — and a function of stored content, so two
                         ;; arrival orders reaching one KB choose alike
                         ends        (if (<= (cone-extent kb (tax/context-down tax sub))
                                             (cone-extent kb (tax/context-up tax super)))
                                       (predicates-below-context kb sub)
                                       (arity-bindings-above-context kb super))
                         ;; the same volatile the sweep below spends, so a cone that took
                         ;; the budget leaves the predicates it named nothing to sweep
                         ;; with — one bound over both halves of the pass
                         [taken cut?] (take-budgeted left ends)]
                     (when cut? (vswap! unreached conj (:sentence e)))
                     (into acc taken)))
                 named
                 edges)
          ;; the whole **spec subtree** of each root, because the binding descends: a
          ;; length declared of `parentOf` holds every `fatherOf` tuple too, so an extent
          ;; read off the named predicate alone would file the finding over `(parentOf …)`
          ;; and not over `(fatherOf …)` — the same trap `special/entail-existing` names
          ;; for the mints it draws off the same three ingredients.  `tax/specs` includes
          ;; the root, so the undescended case is the one-element subtree and unchanged.
          ;;
          ;; A subtree can be most of an ontology and `genl` is the commonest edge in
          ;; one, so the walk is filtered by index **cardinality** before it reads
          ;; anything: a predicate with no stored facts has none to convict, and asking
          ;; costs a count rather than a posting list and a record fetch each.  What is
          ;; left to pay per edge is one count per spec, against the whole subtree's
          ;; extent without it.
          ;;
          ;; **The roots are expanded together, in one walk.**  Every `(genl sub super)`
          ;; in the region is a root, and a batch of them is usually a *chain* — a load
          ;; writes a hierarchy, not one edge — so the subtrees nest: n roots whose union
          ;; holds n predicates cost Σ|specs(rᵢ)| = n²/2 expanded one at a time, and
          ;; `specs`' memo cannot help, since it is keyed on the node a walk began at and
          ;; every walk begins somewhere else.  That was the pass's whole cost on a
          ;; deferred load — 1024 chained edges took 252 ms against 0.374 ms for the same
          ;; batch declaring no arity — and none of it was budgeted, because
          ;; `*exposure-instance-budget*` counts facts examined and this examined none.
          ;; `tax/specs-of-all` seeds one traversal with every root instead, so the walk
          ;; is the union and the counts are one per distinct predicate.
          ;;
          ;; content order, so which predicates a bounded pass reaches is a function of
          ;; the vocabulary rather than of the handle order the region came back in
          preds (into (sorted-set)
                      (filter #(pos? (p/count-with-functor (:index kb) %)))
                      (tax/specs-of-all (:taxonomy kb) roots))
          ;; one membership reader per context met, not one per fact.  A reader memoizes
          ;; for the life of one caller, and a subtree's facts share few contexts between
          ;; them, so building one per question paid the retrieval every question and
          ;; threw the memo away unread.  On 2,000 edges and 2,000 facts under a declared
          ;; root: 798 ms before the report descended at all, 874 ms with a reader per
          ;; fact, 810 ms as it stands — so the descension costs ~1.5% and not the 9.5%
          ;; the per-fact shape was about to charge for it.
          reader (let [cache (volatile! {})]
                   (fn [ctx]
                     (or (get @cache ctx)
                         (let [r (kb/membership-reader kb ctx)]
                           (vswap! cache assoc ctx r)
                           r))))
          sweep (fn [findings pred]
                  (let [[taken cut?] (take-budgeted left (predicate-sentexes kb pred))
                        ;; a candidate is a fact *of* `pred`; a trigger is a sentence
                        ;; *about* it, under a different functor, so the sweep does not
                        ;; convict the declaration or the edge that set it off
                        found (into []
                                    (keep #(some->> (checks/arity-violation
                                                     kb (:sentence %) (:context %)
                                                     (reader (:context %)))
                                                    (vector %)))
                                    taken)]
                    (when cut? (vswap! unswept conj pred))
                    (if-not (seq found)
                      findings
                      (let [[s v] (first found)]
                        (conj findings
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
                                           :via            (:via v)
                                           :message
                                           ;; "declared with" is false of a predicate that
                                           ;; declared nothing and took its length off a
                                           ;; super, so the two cases are worded apart —
                                           ;; by the clause `checks`' own doors word it
                                           ;; with, this being its third reader
                                           (str "arity declared after the facts: " pred
                                                " "
                                                (checks/arity-binding-clause
                                                 pred (:via v) (:expected v))
                                                " and " (count found)
                                                " stored fact(s) of it disagree"
                                                (when cut?
                                                  (str " — the sweep was cut short at "
                                                       *exposure-instance-budget*
                                                       " facts, so there may be more")))}})))))]
      (let [findings (reduce sweep [] preds)
            ;; the findings are bounded by the budget rather than by the vocabulary — a
            ;; predicate convicts nothing without spending at least one fact of it — so
            ;; holding them all to count and to cap costs the sweep's own ceiling and no
            ;; more, where filing them all would cost the ledger everything else in it
            over     (- (count findings) max-arity-findings)
            entries  (vec (take max-arity-findings findings))
            entries
            (cond-> entries
              ;; **What the cap left out, said once.**  A reader acting on this is asking
              ;; how wide the binding reached, which is a different question from either
              ;; sweep being cut short: everything counted here was swept, examined and
              ;; convicted — only the entry naming it was not filed.
              (pos? over)
              (conj {:violation :arity-report-truncated
                     :detail    {:predicates (count findings)
                                 :filed      max-arity-findings
                                 :facts      (transduce (map #(get-in % [:detail :count]))
                                                        + 0 findings)
                                 :sample     (mapv #(get-in % [:detail :predicate])
                                                   (take 3 (drop max-arity-findings findings)))
                                 :message
                                 (str "arity report bounded at " max-arity-findings
                                      " entries: " (count findings)
                                      " predicate(s) hold facts a binding convicts and "
                                      over " of them are named by no entry")}})

              ;; **One entry for the pass, filed whether or not anything was found.**  The
              ;; findings are per predicate and this is not: the budget is the pass's, so
              ;; what sits past the cut is cut by arithmetic rather than by anything about
              ;; itself, and a reader needs the one fact that the pass was bounded and how
              ;; much of the reach it did not look at.
              (or (seq @unswept) (seq @unreached))
              (conj {:violation :arity-truncated
                     :detail    {:predicates  (count @unswept)
                                 :sample      (vec (take 3 @unswept))
                                 :edges       (count @unreached)
                                 :edge-sample (vec (take 3 @unreached))
                                 :budget      *exposure-instance-budget*
                                 :message
                                 (str "arity sweep cut short at "
                                      *exposure-instance-budget* " facts: "
                                      (when (seq @unswept)
                                        (str (count @unswept)
                                             " predicate(s) went unswept, so wrong-arity"
                                             " facts they hold are unreported"))
                                      (when (and (seq @unswept) (seq @unreached)) "; ")
                                      (when (seq @unreached)
                                        (str (count @unreached)
                                             " genlCx edge(s) went unswept, so predicates"
                                             " their visibility move binds are unreported")))}}))]
        (when (seq entries)
          (violations/report kb entries))))))

(defn- report-arbitration-cut!
  "File what `*arbitration-cut*` collected: one `:arbitration-truncated` entry for the
  settle, naming how many declarations went unswept and a sample of them.

  **Why this is a separate kind from `:exposure-truncated`, rather than folded into it.**
  They report different halves of the same budget discipline, and a reader acts on them
  differently.  Exposure being cut means clashes went *unreported*; this means content a
  declaration implicates went **undecided** — the arbitration never ran, so a pair that
  would have been defeated stands believed until some later settle surfaces it.  And the
  two do not even cover the same triggers: `functional` and `asymmetric` implicate stored
  content on this path and on no other, so a reader watching only the exposure entry
  would never learn that a predicate declared functional after its facts was swept short.

  Deduped by sentence, because a settle takes several passes and each re-runs the sweep
  over a region that still holds the same declaration — the same trigger cut in three
  passes is one fact about the settle, not three.

  **Silent while `*rebuilding?*`**, like the exposure pass beside it — and silent by
  being handed no sink at all rather than by declining to read one.  A rebuild's settle
  sweeps a region that is the whole KB, so the budget goes almost at once and every
  declaration after it is one the sweep did not finish; collecting those to throw them
  away would put a KB-proportional vector on the settle path, per pass, in the release
  whose thesis is that a settle costs what moved.  `settle*` binds nil instead, and a nil
  sink records nothing by construction.

  The *sweep* is not gated the same way, and `clash-candidates` says why: the flag does
  not promise the region is everything, so it is safe to hang a report on and not belief."
  [kb]
  (when-let [sink *arbitration-cut*]
    (when-let [cut (cut-notice :arbitration-truncated (distinct @sink)
                               {:sweep       "arbitration"
                                :unit        "instances"
                                :noun        "declaration"
                                :count-key   :triggers
                                :consequence (str "content they implicate is undecided"
                                                  " this settle")})]
      (violations/report kb [cut]))))

(defn- settle-finish
  "Reconcile the derived caches with settled belief and record the readings.

  `belief-moved?` gates the `refresh-beliefs` reconcile of the genl / genlCx
  closures and the five flat caches.  That reconcile exists to catch a *supporter's
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
    (special/reconcile-belief-change! kb (jtms/touched (:tms kb)))
    ;; ...and repair again, because the reconcile itself can surrender the potential: an
    ;; edge leaving a strongly connected component dissolves it, and a revived one can
    ;; close a new one.  Left to the *next* settle, `:scc` reads empty in between, and
    ;; `:scc` is not only a pruning — `tax/placement-rep` collapses a mutually-visible
    ;; group of contexts to one name through it, so the same firing would place its
    ;; conclusion in `CxAlpha` or in `CxBeta` depending on how many settles had
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
        (special/reconcile-belief-change!
         kb
         (into (jtms/touched (:tms kb))
               (concat (keys before) (keys after)))))
      ;; ...and the spellings this reconcile gave *back*, which are revived datums by
      ;; every test but the one `jtms/revived` can apply: they gained belief, and no
      ;; relabel says so, so they are in none of the three window sets.  `settle` re-seeds
      ;; them (`*unmerged-sink*`) — from here rather than from the loop because this is
      ;; where the answer exists, and the loop has already converged by the time it does.
      (when-let [sink (and (not *rebuilding?*) *unmerged-sink*)]
        (vswap! sink into
                (filter #(jtms/in? (:tms kb) %))
                (clojure.core/remove after (keys before)))))
    ;; The cross-context exposure reads the same moved region, after the reconciles —
    ;; `:edge-ctxs` and `:cache-ctxs` now reflect settled belief, which is what the
    ;; witnesses walk.
    (expose-clashes! kb (jtms/touched (:tms kb)) arbitrated)
    ;; ...and the two kinds the disjointness pass does not answer, across the same edge.
    ;; `:refuse` only: under `:arbitrate` the vantages are asked and the pair is weighed.
    (expose-constraint-clashes! kb (jtms/touched (:tms kb)) arbitrated)
    ;; ...and the deciding pass's own truncation, filed here for two reasons the
    ;; exposure pass beside it does not have: its sweep runs once per settle *pass*, so
    ;; this is the only place that sees a whole settle, and its budget is spent before
    ;; anything is decided rather than before anything is reported.  One entry for the
    ;; settle, on the grounds `cut-notice` records for one entry per pass.
    (report-arbitration-cut! kb)
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
  `settle-stats` — the instrument the stratification question is decided from.

  The **arbitration cut sink** is bound here rather than per pass, because that is the
  scope the reading is about: `constraint-nogoods` re-runs its budgeted sweep on every
  pass, and a declaration swept short in each of nine is one fact about this settle.
  `settle-finish` reads it, at the end of the last pass — and on a rebuild it is bound
  **nil**, so nothing is collected rather than collected and dropped
  (`report-arbitration-cut!` says why that distinction is worth a `when-not`)."
  [kb]
  ;; A supporter's label can flip three ways in a settle: revival (`clear-defeats!`
  ;; lifting a node this run defeated last run — so a non-empty defeated set *before*
  ;; the clear counts), a fresh defeat, and a block change (a moved pass).  Snapshot
  ;; the pre-clear defeated set now; `settle-finish` folds it with the post-resolve
  ;; defeated set and the moved count into the `belief-moved?` gate on the cache
  ;; reconcile.  Both reads are of the small defeated set, never the graph.
  (binding [*arbitration-cut* (when-not *rebuilding?* (volatile! []))]
    (let [defeated-before  (jtms/defeated (:tms kb))
          defeated-before? (boolean (seq defeated-before))
          moved? (fn [moved] (or defeated-before?
                                 (boolean (seq (jtms/defeated (:tms kb))))
                                 (pos? moved)))]
      (jtms/clear-defeats! (:tms kb))
      ;; ...and reconcile the belief-derived caches with what that revived, **before**
      ;; anything asks them a question.  `clear-defeats!` lifts a defeat, so a `genl` or
      ;; `genlCx` edge defeated last settle is believed again as of this line — but
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
                            (special/reconcile-belief-change! kb (jtms/touched (:tms kb)))
                            (tax/restore-depths (:taxonomy kb))
                            ;; ...and an except among the revived is a visibility flip:
                            ;; what it hid is seeable again, and only this settle knows
                            ;; the defeat was lifted
                            (recheck-flipped-excepts kb defeated-before))]
        (loop [pass 1, moved 0, seen #{}, flips (or revival-flips #{}), reseeded #{}]
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
                {:keys [violated dilemmas rejoin]} (resolve-contradictions kb ngs)
                ;; a resolution that defeated (or revived) a visibility except flipped
                ;; what its cone can see — queue the same re-check its arrival or
                ;; departure queues, and carry the marked rules to the re-chain, since a
                ;; reveal moves no blocked justification for the drain to notice
                flips  (into flips
                             (recheck-flipped-excepts
                              kb (let [ex-after (believed-excepts kb)]
                                   (concat (set/difference ex-before ex-after)
                                           (set/difference ex-after ex-before)))))
                queued (drain-recheck! kb)
                ;; A context-visibility transition carries `:all-rejoin` because there is no
                ;; arriving sentence narrow enough to identify the one firing it may
                ;; have released.  It therefore owes the coarse rule re-join even when
                ;; the blocked set itself did not move.  Decide that before the
                ;; unproductive-pass gate below; otherwise the gate drops precisely the
                ;; work `blanket-recheck-rules` exists to preserve.
                forced (vec (forced-recheck-rules queued))
                ;; ...and the datums whose belief came *back*, which no trigger queues and
                ;; no blocked set holds.  Read after the resolve above, so a datum this
                ;; pass revived and defeated again is not one of them.  `jtms/touched`
                ;; spans the whole settle rather than the pass, so what keeps a datum from
                ;; being seeded once per pass is `reseeded`, not the window.
                revived (revived-seeds kb reseeded)]
            (if (and (empty? queued) (empty? revived) (empty? rejoin))
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
                (if (and (= new was) (empty? forced) (empty? aggs)
                         (empty? free) (empty? over) (empty? flips)
                         (empty? revived) (empty? rejoin))
                  (settle-finish kb pass moved violated dilemmas (moved? moved) arbitrated)   ; unproductive pass: converged
                  ;; read before the sweep, which deletes justifications
                  (let [released (released-rules kb was new)]
                    (jtms/set-blocked (:tms kb) new)
                    (sweep-excepted! kb (into #{} (remove was) new))
                    ;; A released refusal is re-derived from the bindings it recorded, not
                    ;; re-joined: `place-conclusion` with the firing's own conclusion,
                    ;; placement and antecedents.  The conclusions it places are new datums,
                    ;; so they go back on the agenda like any other — and the revived datums
                    ;; go with them, on the one run, so the partner a revival has to be
                    ;; enumerated against is ranked against one agenda rather than two.
                    (let [seeds (into (into [] (mapcat (fn [[rh e]] (chain/release-refusal! kb rh e)))
                                            free)
                                      revived)]
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
                                                              rejoin
                                                              (keys @(:recheck kb)))))
                    (if (< pass max-settle-passes)
                      (recur (inc pass) (inc moved) arbitrated #{} (into reseeded revived))
                      (do (trove/log! {:level :warn :id ::exception-fixpoint
                                       :msg  (str "exception re-check did not converge in "
                                                  max-settle-passes " passes; giving up")
                                       :data {:passes pass :blocked (count new)}})
                          (settle-finish kb pass (inc moved) violated dilemmas (moved? (inc moved)) arbitrated)))))))))))))

(def ^:private max-unmerge-rounds
  "How many times `settle` re-seeds an un-merge and settles again before it gives up and
  says so.  Two is the shape of every real case — one settle discovers the un-merge, the
  next derives from it and finds nothing further to give back — and the bound is here for
  the same reason `max-settle-passes` is: a round that keeps producing work is a bug, and
  what this buys is that it reports one instead of hanging the writer."
  8)

(defn settle
  "Settle belief (`settle*`), then hand the region it moved to whoever is listening.

  Returns the unsatisfiable clashes, as `settle*` does.  Delivery is here rather than
  inside `settle-finish` because a listener may **write**, and a write inside a relabel
  would relabel mid-relabel: by the time this runs the fixpoint is reached, the caches
  are reconciled, the readings are recorded and the touched set is cleared, so a
  listener's `assert` starts a fresh settle like any other caller's.  A KB nobody is
  listening to pays one deref (`feed/deliver!`).

  **An un-merge settles again**, which is the one thing here that is not delivery.  A
  spelling an equality displaced comes back when the equality stops being believed, and
  that is a revival owed a re-derivation exactly as a lifted defeat is — but it is
  discovered by `special/refresh-supersessions`, which runs at the end of `settle*` after
  the fixpoint, so there is no pass left to re-seed into.  The seeds therefore go on the
  agenda here and the whole settle runs again, the way `core/retract!` already settles
  twice around its own re-derivation.

  Two designs were measured against this one and neither ships. **Moving the reconcile
  into the loop** keeps one fixpoint, which is the better property — but `settle-finish`
  decides what the settle moved by diffing the supersession map it brackets, so a
  reconcile that ran earlier would have to thread its own flips forward or a merge would
  stop being reported as `:believed-removed` at all; that is a change to what every
  `preview` and feed event says, to fix a re-derivation.  A **re-enter signal** from
  `settle-finish` is the same loop as this one with the bound further from the thing it
  bounds.  What this shape costs is that a KB whose settle un-merges something settles
  twice; a KB that does not un-merge pays one deref of an unbound var, which is nearly
  all of them (`feed/wants-region?` is the same bargain beside it).

  The rounds are bounded rather than trusted: an un-merge that keeps giving spellings
  back is a bug, and `max-unmerge-rounds` makes it a log line instead of a hang."
  [kb]
  (let [violated
        ;; each round's answer supersedes the one before it — a re-seed derives, and what
        ;; is unsatisfiable is a question about where the KB landed, so the last round's
        ;; reading is the settle's
        (loop [round 1]
          (let [seeds (volatile! #{})
                v     (binding [*unmerged-sink* seeds] (settle* kb))
                back  (into [] @seeds)]
            (cond
              (empty? back) v
              (>= round max-unmerge-rounds)
              (do (trove/log! {:level :warn :id ::unmerge-fixpoint
                               :msg  (str "un-merge re-seeding did not converge in "
                                          max-unmerge-rounds " rounds; giving up")
                               :data {:rounds round :seeds (count back)}})
                  v)
              :else (do (rechain-seeds kb back) (recur (inc round))))))]
    (feed/deliver! kb)
    violated))

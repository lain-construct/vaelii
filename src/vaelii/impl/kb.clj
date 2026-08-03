;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.kb
  "The KB record, its constructor, and the ground floor of retrieval:
  find/create sentexes, the belief-filtered `sentexes-matching`, and the equality-closure
  goal rewriting that keeps a retired spelling usable as a question.

  Bottom of the engine stack (kb <- checks <- special <- integrate <- chain <-
  settle <- vaelii.core): everything here reads the storage protocols, the taxonomy, the
  JTMS and the matchers — never assertion, chaining, or settling.  `sentexes-matching`
  lives here rather than in core because the layers above it (`integrate-sentex`,
  `negation-nogoods`) need *querying*, not asserting — moving it down is what
  unties the old `declare assert query settle` knot."
  (:refer-clojure :exclude [isa?])
  (:require [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.impl.columnar :as columnar]
            [vaelii.impl.dense-kv :as dense]
            [vaelii.impl.disk.backend :as disk]
            [vaelii.impl.disk.index-snapshot :as snapshot]
            [vaelii.impl.disk.record-store :as drs]
            [vaelii.impl.feed :as feed]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.memory :as mem]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.observe :as observe]
            [vaelii.impl.overlay.mount :as mount]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.provers :as provers]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.rewrite :as rewrite]
            [vaelii.impl.rules :as rules]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.solve :as solve]
            [vaelii.impl.taxonomy :as tax]))

;; `solver`, `conflicts`, and `program` are atoms: the solver is swappable (the ASP
;; backend in vaelii.impl.asp.edge); `conflicts` holds the last settle's
;; unsatisfiable contradictions — the "solve result" surfaced by `core/conflicts`;
;; `program` holds the last edge Program handed to the solver.
;;
;; `program` is kept because belief is *self-erasing evidence*: once settle defeats
;; one side of a tie, that side stops matching, so the very nogood that produced the
;; contested set is no longer derivable from the KB.  Recomputing it after the fact
;; yields nothing.  Anything wanting to ask what the tie *was* — which beliefs were
;; forced and which were an arbitrary pick (`asp.edge/classify`) — has to read the
;; program the decision was actually made from.
;;
;; `violations` holds the definitional constraints a *derived* conclusion would have
;; broken during the last chaining run — see `place-conclusion` and `violations`.
;;
;; `contradictions` holds the coexisting P/¬P pairs the last settle left standing.
;; Those are *represented dilemmas*, not conflicts: neither rule named the other's
;; case, so there is nothing to arbitrate and both sides stay believed at :default
;; (docs/exceptions.md, "What surfaces where").  `conflicts` is now only the
;; irreducible clashes among known-true content.
;;
;; `recheck` is the exception re-check queue: `{rule-handle -> triggers}` for the rules
;; whose `exceptWhen` query may have flipped since the last settle, posted by the
;; triggers (a fact arriving or leaving on one of the exception's predicates, or any
;; genl/genlContext edge change) and drained by `settle`.  `triggers` is the set of
;; sentences that moved — which firings of that rule to re-evaluate — or `:all` when
;; there is no such sentence and all of them must be.  Nothing here caches whether an
;; exception *holds* — the queue says what to re-evaluate, and the re-evaluation says
;; what is true.
;;
;; `settle-stats` is instrumentation for the exception fixpoint: `:iterations` counts
;; the passes in which the blocked set actually moved (0 = nothing blocked, 1 = one
;; pass sufficed), `:passes` the total loop passes including the confirming one, and
;; `:histogram` the distribution of `:iterations` since the last reset.
;;
;; `qcn` is where a qualitative constraint network **lives between reads**: an atom of
;; `{[calculus-name context] -> {:read … :clock n}}`, stamped with `observe/change-clock`
;; and re-derived the moment that has moved (`vaelii.impl.qcn-kb`).  Per KB rather than
;; global, because two KBs in one JVM share the clock but not their content.
;;
;; `matches` is the literal cache (`vaelii.impl.literal-cache`): an atom of
;; `{[canonical-literal context hierarchical? arg-root?] -> {:value … :clock n}}` holding
;; what `matches-visible` answered, α-renamed so two spellings of one question share an
;; entry and stamped with `observe/change-clock` so any mutation retires it.  Per KB for
;; the same reason `qcn` is: two KBs in one JVM share the clock but not their content, so
;; a global cache would serve one KB's extent as another's.  A **declared field** rather
;; than a bare key on the map, because `matches-visible` reads it on every retrieval and
;; an extension-map key costs a hash lookup where a field costs none.
;; `reports` memoizes the `contradicts` reports `conflicts` and `contradictions` hand
;; back — `{#{h1 h2} -> report}` for the pairs the last settle reported, and nothing else,
;; so it is bounded by what is standing rather than by what ever stood.  Why an entry the
;; settle's region does not hold can be carried forward, and what removing it costs:
;; docs/nmtms.md, "The reports are rebuilt only where the region moved".
;;
;; `negations` is the memo beside `:opposed`, and the two answer different halves of one
;; question: `:opposed` says *which bodies could contradict*, kept O(1) per mutation at the
;; store and removal choke points; `:negations` says *what each of those bodies currently
;; contradicts about*, as `{body #{nogood}}`.  `:dirty` is the bodies a store or a removal
;; touched since the last settle drained it (`note-opposed!` posts them, the same choke
;; points that maintain `:opposed`); `:vocab` is the genlContext generation the
;; joint-visibility test reads through, so a context edge retires the whole memo.  Which
;; three things move a pairing, and the measured cost of dropping either narrowing:
;; docs/nmtms.md, "Soft, prioritized contradictions".
;;
;; `feed` is the change feed's listeners and the region a settle files for them
;; (`vaelii.impl.feed`).  A field rather than a bare key for the same reason as
;; `:naming`: every settle reads it to decide whether to accumulate anything, and a KB
;; nobody is listening to should pay a field read and not a hash lookup.
;; `dir` is the record store's directory when the records are durable, else nil. It is
;; here so `core/close!` can release the exclusive FileLock the disk backend takes:
;; without it a long-running process could not hand a directory to another process, or
;; reopen it elsewhere, until the JVM exited.
(defrecord KB [records index tms taxonomy provers solver conflicts program violations
               contradictions recheck settle-stats chain-stats opposed negations clashes
               reports qcn matches naming constraints feed dir])

;; ---- storage selection: two independent axes ------------------------------
;;
;; A KB's two stores answer to different pressures and are chosen separately.  The
;; **records** (`:record-space`) are the ground truth — what must survive — so the
;; question there is durability.  The **index** (`:index-space`) is *derived*: `reindex`
;; rebuilds every entry of it from the records, through the protocols, so it need never
;; be persisted at all and the question there is representation (how dense, how fast).
;; Welding the two into one `:backend` keyword makes every density experiment
;; memory-only and every durable KB pay for a durable index it can always recompute.
;;
;; So the axes are independent — `:records` (`:memory` / `:disk`) and `:index`
;; (`:memory` / `:dense` / `:columnar` / `:disk`) — and `:backend` is sugar naming a
;; pair.  **Every legal pair has a name**, spelled `<records>-<index>`, so the two opts
;; are for overriding a half rather than for reaching a corner the table left out.

(def ^:private backend-modes
  "The `:backend` sugar: each name expands to a `{:records :index}` pair, and reads
  `<records>-<index>` — `:disk-memory` is durable records with the derived index in RAM
  (rebuilt on open), `:disk-columnar` the same with the columnar index instead.
  `:memory` and `:disk` are the two pairs that are the same store on both axes, named for
  the store rather than doubled.

  Seven pairs, not eight: **RAM records with the durable index is refused**, so no name
  spells it (`backend-axes` says why)."
  {:memory          {:records :memory :index :memory}
   :memory-dense    {:records :memory :index :dense}
   :memory-columnar {:records :memory :index :columnar}
   :disk-memory     {:records :disk   :index :memory}
   :disk-dense      {:records :disk   :index :dense}
   :disk-columnar   {:records :disk   :index :columnar}
   :disk            {:records :disk   :index :disk}
   ;; a fork: both halves decorate whatever the frozen base resolved to, so `:overlay` is
   ;; a *decorator* selection rather than a store — see the `:base` / `:overlay` opts
   :overlay         {:records :overlay :index :overlay}})

(defn backend-axes
  "The `{:records :index}` selection for `opts`: the `:backend` sugar expanded, with an
  explicit `:records` / `:index` opt overriding its half.  Public because it is the one
  answer to \"which two stores does this opts map name?\" — a harness asking that (the
  test suite's index-shape gate) must read the same table `open-kb` does, or a new sugar
  name silently leaves it saying the wrong thing.

  **RAM records under the durable index is refused**, on either spelling.  The index is a
  function of the records, so persisting the derived half while the ground truth
  evaporates at JVM exit leaves index files describing records that no longer exist — and
  the next open answers every query out of them, believing nothing is wrong."
  [{:keys [backend records index] :or {backend :memory}}]
  (let [pair (or (backend-modes backend)
                 (throw (ex-info (str "unknown KB backend " (pr-str backend) " — want one of "
                                      (pr-str (vec (sort (keys backend-modes))))
                                      ", or the :records / :index opts")
                                 {:type :unknown-backend :backend backend})))
        axes {:records (or records (:records pair))
              :index   (or index   (:index pair))}]
    (when (= axes {:records :memory :index :disk})
      (throw (ex-info (str "the :disk index needs :disk records — an index is derived from "
                           "the records, so persisting it over a record store that empties "
                           "at JVM exit leaves it describing records that are gone.  Want "
                           "durability? :disk.  Want the RAM index? :memory.")
                      (assoc axes :type :unknown-backend))))
    axes))

(defn- record-store-for
  "The `RecordStore` for the record axis.  `:memory` keys the in-RAM store by
  `:record-space`, so a KB rebuilt over the same number sees the same records
  (`vaelii.impl.memory`); `:disk` opens the durable log/idx record store in a directory
  (`:dir`, else derived from the space numbers), shared per directory — and opens
  *only* the records, so a derived-index mode writes no index files
  (`vaelii.impl.disk.backend`)."
  [kind {:keys [record-space] :or {record-space 0} :as opts}]
  (case kind
    :memory (mem/memory-record-store {:space record-space})
    :disk   (disk/records-for (disk/disk-dir opts))
    ;; `:overlay` is resolved by `open-kb`, which alone knows the base — reaching here
    ;; means a base or an overlay half was itself declared `:overlay`, and a stack of
    ;; forks is deliberately not built (docs/overlay.md)
    (throw (ex-info (str "unknown record backend " (pr-str kind) " — want :memory or :disk"
                         (when (= :overlay kind)
                           " (an :overlay half cannot itself be an overlay)"))
                    {:type :unknown-backend :records kind}))))

(defn- derived-index-space
  "What a **derived** (in-RAM) index's shared state is keyed by.  A derived index is a
  function of the records, so it must be shared exactly when the records are: the
  `:index-space` number when the records are in RAM, the record *directory* when they
  are on disk.  Keying a disk-backed KB's RAM index by the space number instead would
  hand two KBs over different directories one shared index whenever they took the
  default numbers — one directory's records answered out of the other's index, with
  nothing to signal it."
  [record-kind {:keys [index-space] :or {index-space 1} :as opts}]
  (if (= :disk record-kind)
    [:dir (disk/canonical-dir (disk/disk-dir opts))]
    index-space))

(defn- index-store-for
  "`[index-store durable?]` for the index axis.  Three of the four are **derived-only**
  — the flat `:memory` map, the `:dense` int-postings backend (Phase 1,
  `vaelii.impl.dense-kv`) and the `:columnar` native trie (Phase 2,
  `vaelii.impl.columnar`) — and open empty, so a KB pairing one with durable records
  must `reindex` before it can answer (`open-kb`).  `:disk` is the write-ahead-logged
  durable index, which opens already populated.

  The flag is returned rather than sniffed from the store type at the call site: what
  makes an index durable is which one was *selected*, and a type test would have to be
  updated by whoever adds the next backend, silently and after the fact."
  [kind record-kind opts]
  (if (= :disk kind)
    [(disk/index-for (disk/disk-dir opts)) true]
    (let [space (derived-index-space record-kind opts)]
      (case kind
        :memory   [(mem/memory-index-store        {:space space}) false]
        :dense    [(dense/dense-index-store       {:space space}) false]
        :columnar [(columnar/columnar-index-store {:space space}) false]
        (throw (ex-info (str "unknown index backend " (pr-str kind)
                             " — want :memory, :dense, :columnar, or :disk"
                             (when (= :overlay kind)
                               " (an :overlay half cannot itself be an overlay)"))
                        {:type :unknown-backend :index kind}))))))

;; ---- forks: an overlay over a frozen base ---------------------------------
;; `:overlay` is not a store but a *decorator* over whatever each axis resolves to, so it
;; is the one selection `open-kb` has to resolve itself: it needs the base's stores, which
;; the axis functions above are not given.  A base arrives either already open
;; (`:base-stores`, what `core/fork` passes from a live KB) or as the opts naming it
;; (`:base`, what a second JVM mounting the same frozen directory passes).

(defn- resolve-base
  "The `{:records :index}` pair a fork mounts over, frozen by the mount itself."
  [{:keys [base base-stores]}]
  (cond
    base-stores base-stores
    base        (let [{rk :records ik :index} (backend-axes base)]
                  {:records (record-store-for rk base)
                   :index   (first (index-store-for ik rk base))})
    :else (throw (ex-info (str "an :overlay backend needs a base — pass :base (the opts "
                               "naming it) or :base-stores (already-open stores)")
                          {:type :no-base}))))

(defn- create-tms
  "The truth-maintenance network `:tms` selects: `:reference` (default) is the atom
  over one persistent map; `:dense` is the bitmap/primitive-map representation
  (`vaelii.impl.dense-jtms`), off by default and
  proven to answer identically by `jtms_dense_oracle_test`.

  Resolved lazily, exactly as the solver backends are, so a KB that never asks for the
  dense network never loads RoaringBitmap or fastutil."
  [kind]
  (case kind
    :reference (jtms/create-tms)
    :dense     ((requiring-resolve 'vaelii.impl.dense-jtms/create-dense-tms))
    (throw (ex-info (str "unknown TMS " (pr-str kind) " — want :reference or :dense")
                    {:type :unknown-backend :tms kind}))))

(def opt-keys
  "Every key `open-kb` reads.  Public because it is the answer to \"is this a real
  option?\", and a caller that can ask does not have to find out from a wrong answer."
  #{:backend :records :index :record-space :index-space :dir :tms :recover?
    :naming :constraints :base :base-stores :overlay})

(defn- check-opts!
  "Refuse a key `open-kb` does not read.  **An option that is not read is not an option**:
  a misspelt `:record-space` leaves the KB on the default space in silence, so two KBs a
  caller built to keep apart share one store — each one's flush empties the other, and
  every read after it answers out of the wrong records with nothing to signal it.  A KB
  that took the default is indistinguishable downstream from one that asked for it, so
  the only place that can still tell is here, where what was written is still legible.

  `where` names the map, since a fork's `:base` and `:overlay` carry opts of their own."
  [opts where]
  (when-let [unknown (seq (sort-by pr-str (remove opt-keys (keys opts))))]
    (throw (ex-info (str "unknown " where " option" (when (next unknown) "s") " "
                         (str/join ", " (map pr-str unknown))
                         " — open-kb reads " (str/join ", " (map pr-str (sort opt-keys)))
                         ".  An option nothing reads takes the default in silence,"
                         " which for a store number means sharing a store.")
                    {:type :unknown-option :unknown (vec unknown)
                     :options (vec (sort opt-keys))}))))

(defn- check-naming!
  "Refuse a `:naming` setting `nm/policies` does not name, returning it.  Beside
  `check-opts!` because it is the same failure at one level down — an option read but not
  understood — and for the same reason: a KB that silently took `:strict` when it was
  told something else refuses content the caller expected to land."
  [policy]
  (if (contains? nm/policies policy)
    policy
    (throw (ex-info (str "unknown :naming policy " (pr-str policy) " — open-kb reads "
                         (str/join ", " (map pr-str (sort (keys nm/policies)))))
                    {:type :unknown-option :naming policy
                     :options (vec (sort (keys nm/policies)))}))))

(def constraint-policies
  "The constraint policies a KB's front door may hold, as `open-kb`'s `:constraints`.

    :refuse     `assert` refuses a disjoint / functional clash, and a declaration
                arriving after the content it convicts reports rather than decides
    :arbitrate  refuse only against `:monotonic` content; against a `:default` claim
                admit the sentence and let `settle` arbitrate the pair — and let a
                declaration reach back over what is already stored, so a violating set
                lands on the same belief in every arrival order

  This is **this KB's** policy, not the build's, for `:naming`'s reason: whether a writer
  is told no is an application question, and one process can hold a KB curating a
  hand-written ontology beside one ingesting a corpus whose schema arrives last.
  `checks/arbitrating?` is what reads it, and an unstated policy reads the process
  default there rather than one of these.

  **The policy is not persisted, and a `recover` decides more than `:refuse` does.**  It
  belongs to the KB handle, not to the store, so reopening the same records under the
  other policy is legitimate and changes what belief settles to.  Sharper than that: a
  rebuild's region is *every* stored sentex, so `settle/clash-nogoods` finds a standing
  clash from the region alone — no declaration sweep needed — and decides it under either
  policy.  A `:refuse` KB therefore believes both sides of a clash it was built
  incrementally into, and one side of the same clash after a restart.  That is the
  `:refuse` half being the loose one: `clash-nogoods` is deliberately not gated on
  `*rebuilding?*` because a nogood is *state* that belief depends on, and a rebuild that
  skipped it would revive the loser of a decided clash.  A KB that wants the two to agree
  wants `:arbitrate`."
  #{:refuse :arbitrate})

(defn- check-constraints!
  "Refuse a `:constraints` policy `constraint-policies` does not name, returning it.
  Beside `check-naming!` because it is the same kind of setting — this KB's front-door
  policy, not the build's — and the same failure when it is misspelt: a KB that silently
  took `:refuse` when it was told `:arbitrate` refuses content the caller expected to
  land and arbitrate."
  [policy]
  (if (contains? constraint-policies policy)
    policy
    (throw (ex-info (str "unknown :constraints policy " (pr-str policy) " — open-kb reads "
                         (str/join ", " (map pr-str (sort constraint-policies))))
                    {:type :unknown-option :constraints policy
                     :options (vec (sort constraint-policies))}))))

(defn- snapshot-mode?
  "Is this KB the one configuration a mapped index snapshot is for — durable records
  under the derived columnar index, with the snapshot switched on?  Every other pairing
  either has no image to write (a RAM record store's index describes records that vanish
  at JVM exit) or needs none (`:disk` persists its index outright)."
  [rkind ikind]
  (and (= :disk rkind) (= :columnar ikind) (snapshot/enabled?)))

(defn- register-index-snapshot!
  "Arrange for `dir`'s index image to be written when the directory closes.  Registered
  for every KB in snapshot mode, not only one that read an image: a KB that *rebuilt* its
  index is precisely the one worth snapshotting afterwards, and a freshly loaded one has
  no image to have read."
  [dir istore rstore]
  (disk/register-index-snapshot!
   dir (fn [] (snapshot/save! dir istore #(drs/slot-fingerprint rstore)))))

(defn- map-index-snapshot!
  "Try to map `dir`'s index image into `istore` instead of rebuilding it — the decision
  map (`{:index :mapped}` or `{:index :rebuild :reason r}`)."
  [dir istore rstore]
  (snapshot/load! dir istore #(drs/slot-fingerprint rstore)))

(defn open-kb
  "Construct a KB — the implementation behind `vaelii.core/open-kb`, which owns the
  user-facing docstring.  `:backend` (`:memory` default) names a record/index store
  pair, or `:records` / `:index` select the two axes independently; `:tms`
  (`:reference` default, or `:dense`) selects the truth-maintenance representation.

  `recover-fn` and `reindex-fn` are injected by the caller: both rebuild through the
  whole engine stack (taxonomy, TMS, settle), which sits *above* this namespace, so they
  arrive as arguments rather than as a require that would close the layering cycle this
  namespace exists to break.  `reindex-fn` is `core/reindex` — rebuild the index from
  the records, *then* recover — which is what a derived index over a durable record
  store needs: `recover` alone reads the index it is recovering from
  (`special/rebuild-taxonomy` reads the functor root), so over an empty one it would
  rebuild an empty taxonomy and report nothing wrong."
  ;; `:recover? :auto` is the default, and the alternative was worse than it looked.
  ;; Under `:warn` a reopened store handed back a fully functional KB whose `isa?`
  ;; answered false and whose queries answered `[]` — a wrong answer, not an error,
  ;; with nothing on the returned value for a caller to detect and a single `:warn`
  ;; log as the only signal. The `:test` profile floors logging at `:error`, so even
  ;; that was invisible where it mattered most. The mirror case below (a derived index
  ;; describing records that are gone) has always repaired first and logged after;
  ;; this branch now agrees with it. `:warn` and `false` remain, spelled explicitly.
  [{:keys [record-space recover? tms naming constraints]
    :or   {record-space 0 recover? :auto tms :reference naming :strict}
    :as   opts}
   recover-fn reindex-fn]
  (check-opts! opts "open-kb")
  (check-naming! naming)
  ;; **No default here, and nil is not one.**  An unstated policy means the caller said
  ;; nothing, which `checks/arbitrating?` answers from the process default — so a
  ;; `binding` and `VAELII_ARBITRATE_CONSTRAINTS=1` still move a KB that did not ask.
  ;; Defaulting to `:refuse` here would make every KB state a policy and silently take
  ;; the var out of the picture.
  (when (some? constraints) (check-constraints! constraints))
  (doseq [half [:base :overlay]]
    (when-let [sub (get opts half)] (check-opts! sub (str half))))
  (let [{rkind :records ikind :index} (backend-axes opts)
        overlay?                      (or (= :overlay rkind) (= :overlay ikind))
        base                          (when overlay? (resolve-base opts))
        ov-opts                       (:overlay opts {})
        {ovr :records ovi :index}     (when overlay? (backend-axes ov-opts))
        rstore  (if (= :overlay rkind)
                  (mount/mount-records (record-store-for ovr ov-opts)
                                       (:records base)
                                       (mount/meta-kv ovr ov-opts))
                  (record-store-for rkind opts))
        [istore index-durable?]
        (if (= :overlay ikind)
          ;; A fork's merged index opens populated exactly when its base's did, so what
          ;; the recovery branch below needs to know is simply whether the merged view
          ;; holds anything — which the trie's own root count answers in O(1), and
          ;; answers correctly whether the base index was durable or derived-and-built.
          (let [merged (mount/mount-index (first (index-store-for ovi ovr ov-opts))
                                          (:index base))]
            [merged (pos? (long (p/count-at merged [])))])
          (index-store-for ikind rkind opts))
        ;; by name rather than positionally: seventeen `(atom {})`s in a row is a
        ;; miscount waiting to happen, and a miscount here hands one subsystem another's
        ;; state with nothing to notice it — every field is an atom, so the shapes do not
        ;; even disagree until something reads one.
        kb (map->KB {:records rstore
                     :index   istore
                     ;; the directory `close!` releases, when the records are durable
                     :dir     (when (= :disk rkind)
                                (disk/canonical-dir (disk/disk-dir opts)))
                     :tms     (create-tms tms)
                     :taxonomy (tax/create-taxonomy)
                     :provers  (atom provers/default-provers)
                     :solver   (atom solve/local-solver)
                     :conflicts (atom [])
                     :program   (atom nil)
                     :violations (atom [])
                     :contradictions (atom [])
                     :recheck   (atom {})
                     :settle-stats (atom {:iterations 0 :passes 0 :histogram {}})
                     :chain-stats  (atom {:runs 0 :last nil})
                     :opposed   (atom #{})
                     ;; `{pred -> how many rules take it as an antecedent}` — the roster
                     ;; `special/visibility-seeds` enumerates instead of walking a context
                     ;; cone.  Kept O(1) at the rule index/unindex choke points, exactly
                     ;; as `:opposed` is kept at the store's, and rebuilt by `recover`
                     ;; because recovery replays rule indexing.  Reference-counted rather
                     ;; than a set: two rules on one antecedent must not have the first
                     ;; retraction retire the predicate the second still reads.
                     :rule-antecedents (atom {})
                     ;; `{context -> how many rules are stated there}` — the other half
                     ;; of the same question: an edge only needs seeding when one side
                     ;; holds a rule that could newly reach the other side's facts, and
                     ;; wiring an empty microtheory under a full one holds none.
                     :rule-contexts (atom {})
                     :negations (atom {})
                     :clashes   (atom {})
                     :reports   (atom {})
                     :qcn       (atom {})
                     :matches   (atom {})
                     :feed      (feed/create-feed)
                     ;; a plain value, not an atom: which conventions the front door
                     ;; holds content to is settled when the KB is opened, and a store
                     ;; whose policy moved under it would hold two vocabularies with
                     ;; nothing recording which sentence arrived under which
                     :naming    naming
                     ;; likewise, and nil on purpose — the caller said nothing, so
                     ;; `checks/arbitrating?` reads the process default
                     :constraints constraints})
        snapshot? (snapshot-mode? rkind ikind)]
    (when snapshot? (register-index-snapshot! (disk/disk-dir opts) istore rstore))
    (when recover?
      (cond
        ;; A **derived** index opens empty over records that are not, so the repair is
        ;; one step longer than `recover`: rebuild the index from the records first, then
        ;; recover the TMS and taxonomy from both.  That ordering *is* `core/reindex`.
        (seq (p/sentex-ids (:records kb)))
        (if (= :auto recover?)
          (if index-durable?
            (recover-fn kb)
            ;; A derived index is rebuilt from the records here — unless a **mapped
            ;; snapshot** of it survives and still describes them, in which case the
            ;; rebuild is replaced by reading its bytes back
            ;; (`vaelii.impl.disk.index-snapshot`).  The stamp decides; a snapshot that
            ;; fails any part of it falls back to exactly the rebuild below, which is
            ;; always legal because the index is derived state.
            (let [snap (when snapshot?
                         (map-index-snapshot! (disk/disk-dir opts) istore rstore))]
              (if (= :mapped (:index snap))
                (recover-fn kb)
                ;; O(records), paid on every open — the standing cost of not persisting
                ;; the index, and the number that decides whether persisting a snapshot
                ;; of one is worth it, so it is reported rather than absorbed silently
                (let [t0 (System/nanoTime)
                      {:keys [sentexes rules]} (reindex-fn kb)
                      ms (/ (- (System/nanoTime) t0) 1e6)]
                  (trove/log! {:level :info :id ::reindexed-on-open
                               :msg (format "rebuilt the derived index from %d records (%d rules) in %.0f ms%s"
                                            (long sentexes) (long rules) ms
                                            (if snap (str " — no usable index snapshot ("
                                                          (name (:reason snap)) ")") ""))})))))
          (trove/log! {:level :warn :id ::unrecovered-store
                       :msg (str "the record store (space " record-space ") already holds sentexes "
                                 "but this KB's TMS and taxonomy are empty"
                                 (when-not index-durable?
                                   ", and its index is derived state that opens empty")
                                 " — queries will silently answer nothing.  Call "
                                 (if index-durable? "(recover kb)" "(reindex kb)")
                                 ", or construct with {:recover? :auto}; {:recover? false} "
                                 "silences this.")}))

        ;; The mirror case, and the more dangerous one: a derived index holding entries
        ;; for records that are *gone*.  Such an index is shared for the life of the JVM
        ;; under the identity of the records it is derived from, so a store emptied out
        ;; from under it (a directory closed, deleted and reopened) leaves it describing
        ;; nothing — resolving handles to no record and answering `find-or-create` with a
        ;; dead one.  It is derived state and the records are the ground truth, so it is
        ;; simply dropped.
        (and (not index-durable?) (pos? (p/count-at (:index kb) [])))
        (do (p/clear-index! (:index kb))
            (trove/log! {:level :warn :id ::stale-derived-index
                         :msg (str "dropped a derived index left over from an earlier life of "
                                   "this record store — the records it describes are gone")}))))
    kb))

(def equality-predicates
  "The relations that assert a merge — `vaelii.impl.special` is where they are
  acted on, but stratification (`vaelii.impl.checks`) needs the set too.  `different`
  is not among them: it *reads* the closure and is never stored (see
  `vaelii.impl.wff`)."
  '#{rewriteOf sameAs equals})

;; ---- type queries -------------------------------------------------------

(defn- exists-in?
  "Does the ground `sentence` hold in a context visible from `context` (its genlContext
  up-closure; a variable context means any context)?"
  [kb sentence context]
  (boolean (seq (res/matches-visible kb sentence context))))

(defn find-sentexes
  "Every stored sentex that contains `term` anywhere (any position, any nesting).

  An atom is one inverted-index read.  A **compound** is narrowed by the postings of the
  atoms it contains — every sentex holding the compound holds all of them — and each
  candidate is then verified against its own sentence, since that intersection is a
  superset.  So a compound is findable whether or not it earns a key of its own
  (`sentex/*min-indexed-depth*`, `sentex/max-indexed-compound`), and the verify reads the
  record this was going to return anyway.

  A compound holding a **variable** is a pattern rather than a term, and this answers
  nothing for one — `sentexes-matching` is what takes a pattern."
  [kb term]
  (let [t (sx/canon term)]
    (if (and (sequential? t) (not (sx/indexable-term? t)))
      ()
      (cond->> (if (sequential? t)
                 (p/sentexes-with-terms (:index kb) (sx/probe-atoms t))
                 (p/sentexes-with-term (:index kb) t))
        true            (map #(p/get-sentex (:records kb) %))
        true            (filter some?)
        (sequential? t) (filter #(sx/mentions? % t))))))

(defn find-sentexes-all
  "Every stored sentex that contains all of `terms`.  One intersection over every term's
  probe keys, then the same verify `find-sentexes` does, once per compound among them."
  [kb terms]
  (let [ts    (mapv sx/canon terms)
        cmpds (filterv sequential? ts)
        ks    (into [] (comp (mapcat #(if (sequential? %) (sx/probe-atoms %) [%])) (distinct)) ts)]
    (if (some #(not (sx/indexable-term? %)) cmpds)
      ()
      (cond->> (p/sentexes-with-terms (:index kb) ks)
        true        (map #(p/get-sentex (:records kb) %))
        true        (filter some?)
        (seq cmpds) (filter (fn [sx] (every? #(sx/mentions? sx %) cmpds)))))))

(defn types-of
  "The types asserted of term `x` — functors of unary sentexes (T x), found via the
  argument root.  Scoped to memberships visible from `context` (default: any context).

  `x` is any term, not only an individual: a predicate carries the meta-ontology's
  types (`binaryPredicate`, `instanceRelationPredicate`, …) the same way `Fido`
  carries `dog`.

  The same three filters `matches-visible` applies, since this *is* the retrieval
  `isa?` and the disjointness check are built on and the two must not disagree about
  what the KB holds: believed, asserted in a context `context` sees, and not hidden
  from it by an `except`.  A negative membership is excluded by the argument test
  rather than by a truth filter — a `(not (T x))` sentex has `not` for its functor and
  `(T x)` for its lone argument, so it is not a unary sentence *about* `x` at all."
  ([kb x] (types-of kb x '?ctx))
  ([kb x context]
   (let [recs     (:records kb)
         tms      (:tms kb)
         visible? (if (sx/variable? context)
                    (constantly true)
                    (let [up (tax/context-up (:taxonomy kb) context)] #(contains? up %)))
         hidden?  (let [ex (res/excepted-handles kb context)]
                    (if (empty? ex) (constantly false) #(contains? ex %)))]
     ;; the argument root goes straight to the sentexes holding x in argument
     ;; position 1, instead of every sentex mentioning x anywhere (any position, any
     ;; nesting) — this runs on every unary assert, via disjoint-problem.
     ;;
     ;; The filters are one `keep` rather than a stack of threaded stages: every
     ;; definitional check bottoms out here, the postings are short, and a chain of
     ;; six `filter`/`map` stages allocates six conses per entry to do a few field
     ;; reads.  Lazy, so a caller looking for one type does not pay for a long posting
     ;; — which is also why this is not a transducer: at these lengths `sequence` spends
     ;; more on building the pipeline than the pipeline saves.
     (->> (p/sentexes-with-arg (:index kb) 1 x)
          (keep (fn [h]
                  (when-not (hidden? h)
                    (when-let [s (p/get-sentex recs h)]
                      (when (and (jtms/in? tms (:id s))      ; believed memberships only
                                 (visible? (:context s)))
                        (let [sen (:sentence s)]
                          (when (and (= 1 (nm/arity sen)) (= x (first (nm/args sen))))
                            (nm/functor sen))))))))
          distinct))))

(defn memberships
  "What a term is, as the checks need to ask it: `{:types [t …] :closures [#{…} …]}` —
  the types asserted of `x` and visible from `context`, each paired with its own genl
  up-closure.

  The closures are what make repeated questions free.  `isa? x t` is \"does some type
  `x` holds reach `t`\", and reachability is the *same* edge set read either way — `t' ∈
  specs(t)` iff `t ∈ genls(t')` — so the two directions differ only in what they cost
  here.  `specs(t)` is unbounded in the wrong direction: with `t` = `thing`, the floor
  every `argIsa` check tests first, it is every type in the KB.  The up-closure of a
  type a term actually holds is one chain, cached, and once read every constraint on
  that term is one set membership."
  [kb x context]
  (let [tax (:taxonomy kb)
        ts  (vec (types-of kb x context))]
    {:types ts :closures (mapv #(tax/genls tax % context) ts)}))

(defn isa-among?
  "Is `t` in one of the genl up-closures a `memberships` read returned?  The subtype
  test, once the retrieval it rests on has been paid for."
  [closures t]
  (boolean (some #(contains? % t) closures)))

(defn isa?
  "Is individual `x` (transitively) of type `t`?  Considers only type memberships
  visible from `context` (default: any context).

  Read `x`'s own memberships and climb from each, rather than matching `(t x)` and
  letting the matcher fan `t` out over its genl spec closure — see `memberships` for
  why that direction is the cheap one.

  A non-symbol `x` has no argument-root posting to read, so it falls back to the
  matcher, which reaches the same facts through the functor extents.

  Lazy in the memberships, so a term with a long posting stops at the first type that
  reaches `t` — `memberships` is the batch form, for a caller that will ask again."
  ([kb x t] (isa? kb x t '?ctx))
  ([kb x t context]
   (if (and (symbol? x) (not (sx/variable? x)))
     (let [tax (:taxonomy kb)]
       (boolean (some #(contains? (tax/genls tax % context) t) (types-of kb x context))))
     (exists-in? kb (list t x) context))))

(defn membership-reader
  "A `term -> `memberships`` reader, memoized for the life of one caller.

  The definitional checks ask about a handful of terms — the sentence's arguments, and
  its predicate — but ask about each several times over: the arity arm reads the
  predicate's memberships for three spellings of the declaration and again for
  `variableArity`, `argIsa` reads an argument's twice per constraint on its position,
  and for a unary sentence the disjointness arm wants the very memberships `argIsa`
  just read.  Each is a posting read plus a record fetch and a belief test per entry,
  and none of it can change underneath one `assert`."
  [kb context]
  (let [cache (volatile! {})]
    (fn [term]
      (if-some [m (get @cache term)]
        m
        (let [m (memberships kb term context)]
          (vswap! cache assoc term m)
          m)))))

(defn disjoint?
  "Are types `a` and `b` provably disjoint (via disjoint declarations, closed
  under genl) — anywhere, or (with `context`) using only the declarations and
  genl edges visible from it?"
  ([kb a b] (tax/disjoint? (:taxonomy kb) a b))
  ([kb a b context] (tax/disjoint? (:taxonomy kb) a b context)))

;; ---- storage helpers ----------------------------------------------------

(defn canon-stamp
  "What a raw sentence's canonical form is a function of, beyond the sentence itself:
  the set of predicates declared `symmetric`, which is the one thing
  `resolution/kb-sentex` reads off the KB.  `observe/*handle-cache*` stamps its entries
  with it, so a lookup memoized under one reading of that set is never served under
  another."
  [kb]
  (tax/props (:taxonomy kb) :symmetric))

(defn find-sentex-handle
  "The handle of an existing sentex for `sentence` in `context`, or nil.  A **ground**
  symmetric literal also probes its mirror, so a fact stored before its `symmetric`
  declaration is still found (and re-asserting the mirror image resolves to it rather
  than storing a duplicate)."
  [kb sentence context]
  (let [stamp (canon-stamp kb)]
    (or (observe/cached-handle stamp sentence context)
        (let [probe  #(first (p/lookup (:index kb) (sx/path (res/kb-sentex kb % context))))
              direct (probe sentence)]
          (if direct
            ;; only this arm fills the cache, and the difference is what the answer
            ;; *says*.  Here it is "this sentence is stored at this handle" — true until
            ;; the sentex is removed, which is a choke point.  The mirror arm's answer is
            ;; "this sentence resolves to the handle of its mirror", which additionally
            ;; needs the mirror to keep resolving; the stamp covers that, but a firing
            ;; never asks it, so there is nothing to buy by widening the contract
            (observe/cache-handle! stamp sentence context direct)
            ;; the global property, matching kb-sentex's key discipline: storage sorted
            ;; the arguments (or did not), and which it did cannot vary by who is looking
            (let [sym? #(tax/has-prop? (:taxonomy kb) :symmetric %)]
              (when (and (sx/symmetric-literal? sentence sym?)
                         (every? sx/ground-term? (rest sentence)))
                (probe (sx/mirror-literal sentence)))))))))

;; ---- the P/¬P coincidence set --------------------------------------------
;; A negation nogood (`settle/negation-nogoods`) needs a body stored in *both*
;; polarities, and most negative facts have no positive twin.  Enumerating every
;; stored negation on every settle to find the few that clash is quadratic in the
;; negation count (a settle runs after every mutation).  `:opposed` instead holds
;; exactly the bodies stored both ways, maintained O(1) from two `count-at` probes at
;; the store primitive below and the removal choke point (`integrate/sentex-removed!`),
;; so settle iterates it directly rather than scanning the `:false` trie node.

(defn body-under-not
  "A fact's body with a single leading `not` stripped — the form both polarities key
  on (`(not (flies Opus))` and `(flies Opus)` share the body `(flies Opus)`).  Double
  negation is eliminated at store time, so one strip suffices; a non-fact sentence (a
  rule, a metadata declaration) is returned unchanged and simply never opposes.

  Public because `settle` reads it the other way round: given a handle whose belief just
  moved, this is which opposed body's pairing that handle could have changed, and so
  which memo entry the settle owes a re-derivation."
  [sentence]
  (if (and (sequential? sentence) (= 'not (first sentence)) (= 2 (count sentence)))
    (second sentence)
    sentence))

(defn- opposed?
  "Is `body` stored in **both** polarities — some positive fact under it and some
  `(not body)` under `[:false body]`?  Storage only (belief-blind), the same gate
  `negation-nogoods` applies before its belief-filtered pairing.  The `:false` probe
  runs first: it is 0 for the overwhelmingly common body with no negative twin, so the
  positive `key-stream` walk is never built."
  [idx body]
  (let [b (sx/canon body)]
    (and (pos? (p/count-at idx [:false b]))
         (pos? (p/count-at idx (vec (sx/key-stream b)))))))

(defn note-opposed!
  "Update the `:opposed` coincidence set for a sentence whose fact just arrived or
  left: add its body when both polarities are now stored, drop it otherwise.  Runs at
  the store primitive (`create-sentex`, every add) and the removal choke point
  (`integrate/sentex-removed!`, every remove), so no store path can bypass it; recover
  rebuilds the set with `rebuild-opposed!`.

  The same call posts the body to `:negations` as **dirty** and drops whatever the last
  settle derived for it.  A store or a removal is the one way a body's pairing can change
  with no belief moving to record it — a second `(not S)` arriving in another context adds
  a pair between two sentexes that were both already believed — so the settle's other
  input, the relabelled region, cannot see it.  Posting it here means the two inputs
  together cover every way the answer moves, and it costs one `dissoc` and one `conj` at a
  choke point that was already being paid for."
  [kb sentence]
  (let [b (sx/canon (body-under-not sentence))]
    (swap! (:opposed kb) (if (opposed? (:index kb) b) conj disj) b)
    (swap! (:negations kb) (fn [m] (-> m
                                       (update :by-body dissoc b)
                                       (update :dirty (fnil conj #{}) b))))))

(defn rebuild-opposed!
  "Recompute `:opposed` from storage — the scan `recover` needs, since the set is
  derived state no store holds.  Enumerates the stored negated bodies (the `:false`
  node's children, deduped across contexts) and keeps those with a stored positive
  twin.

  The `:negations` memo over that set goes with it, for the reason every derived cache
  here is cleared rather than merged into on a rebuild: a merge can only ever *add*, so an
  entry for a body the rebuilt set no longer holds would outlive the sentexes it was
  derived from.  The `relabel` in the same `recover` touches every node, so the next
  settle repopulates it whole."
  [kb]
  (let [idx (:index kb)]
    (reset! (:negations kb) {})
    (reset! (:opposed kb)
            (into #{} (comp (filter #(opposed? idx %)) (map sx/canon))
                  (p/children idx [:false])))))

(defn create-sentex
  "Store `sentence` in `context` as a new sentex, index it, and return `[handle sentex]`.

  `strength` (optional) is the assumption strength the record is *born* with.  A premise
  is a sentex whose `:strength` is non-nil, so a caller that already knows it is asserting
  a premise says so here rather than storing the record and having `mark-premise` store it
  again — on the disk backend that second store is a second full frame, leaving the first
  dead the moment it is written, which is half the record log and what trips its compaction
  threshold mid-load."
  ([kb sentence context] (create-sentex kb sentence context nil))
  ([kb sentence context strength]
   (let [s (cond-> (res/kb-sentex kb sentence context)
             strength (assoc :strength strength))
         h (p/put-sentex (:records kb) s)
         s (assoc s :id h)]
     (p/index-sentex (:index kb) s h)
     ;; the add-side seam for an incremental matcher's alpha memories — a no-op
     ;; unless one is engaged (docs/inference.md, "Incremental rule matching")
     (observe/notify-add kb s h)
     ;; and the coarse clock a *derived, resident* structure stamps itself with: this
     ;; is one of the two points the stored content moves at, the other being
     ;; `integrate/sentex-removed!`
     (observe/note-change)
     ;; a run with the handle cache engaged learns the handle here rather than paying a
     ;; trie walk to rediscover it — keyed on the *canonical* sentence, which is what the
     ;; store holds; a caller looking it up by some other spelling misses and fills its
     ;; own key off the index, since a miss costs exactly the trie walk and no more
     (observe/cache-handle! (canon-stamp kb) (:sentence s) (:context s) h)
     ;; maintain the P/¬P coincidence set for settle (this store may have completed an
     ;; opposing pair); the remove mirror is `integrate/sentex-removed!`
     (note-opposed! kb (:sentence s))
     [h s])))

(defn find-or-create-sentex
  "The existing sentex for `sentence` in `context`, or a new one — `[handle sentex new?]`.
  `strength` is passed through to `create-sentex` and so applies only to a *new* record;
  an existing one keeps what it has until `mark-premise` says otherwise."
  ([kb sentence context] (find-or-create-sentex kb sentence context nil))
  ([kb sentence context strength]
   (if-let [h (find-sentex-handle kb sentence context)]
     [h (p/get-sentex (:records kb) h) false]
     (let [[h s] (create-sentex kb sentence context strength)]
       [h s true]))))

;; ---- the equality closure: reading and rewriting -------------------------
;; The closure itself is `vaelii.impl.taxonomy`'s; the *machinery* that runs when two
;; names turn out to denote one thing (migration, supersession) lives in
;; `vaelii.impl.special`.  What lives here is the read/rewrite half — which terms an
;; equality sentence merges and how a sentence or goal is restated under the class
;; representatives — because `sentexes-matching` needs it, and everything above
;; needs it in turn.

(defn equality-sentence?
  [sentence] (contains? equality-predicates (nm/functor sentence)))

(defn preferred-term
  "The term this equality sentence puts on top, or nil.  `rewriteOf` deprecates its
  second argument in favour of its first; `sameAs` and `equals` deprecate neither."
  [[f a _]] (when (= f 'rewriteOf) a))

(defn- rewrite-symbols
  "`term` with every non-variable symbol replaced by its equivalence-class
  representative, recursively — so a merged term nested inside a compound is rewritten
  at whatever depth it sits.  That is the whole of ground congruence closure: the
  inverted term index finds the occurrence and this rewrites it, so no congruence
  algorithm is needed (docs/equality.md, \"Congruence comes free\")."
  [kb visible? term]
  (cond
    (sequential? term) (apply list (map #(rewrite-symbols kb visible? %) term))
    (symbol? term)     (if (sx/variable? term) term (res/representative-in kb visible? term))
    :else              term))

(defn rewrite-term*
  "`term` (a sentence or a term) rewritten to its **normal form**: first every symbol
  replaced by its class representative (ground congruence, `rewrite-symbols`), then its
  argument terms normalized under any schematic rewrite rules (the oriented equational
  rewriting of docs/equality.md — `(equals (fatherOf (fatherOf ?x)) (grandfatherOf
  ?x))` reduces `fatherOf∘fatherOf` to `grandfatherOf`).

  Both halves are belief-following and both are gated: a KB with no merges pays a
  representative lookup per symbol, and one with no schematic equations skips
  normalization entirely (`tax/rewrite-rules` is empty).  Migration and query both go
  through here, so a stored term and a goal meet at one normal form.

  **With a `context`, both halves apply only where they are visible.**  A merge is a
  sentex, so it rewrites the microtheories that inherit it and no others — the same
  filter `migrate-sentex` puts on the twins it creates, now on the question as well as
  on the answer.  Without it the two disagree: a rewrite migration correctly declined
  to make still renames the goal, and a context loses the ability to retrieve a fact it
  believes, under either spelling.  The two-arity is the **unscoped** read, which asks
  about the KB rather than from a vantage.

  `rewrite-term*` takes the visibility predicate **already built**, for a caller
  normalizing many sentences under one reader.  Deciding visibility costs a record fetch
  per equality supporter, and `res/visible-supporter-fn` memoizes those — but only within
  the one predicate it returns, so a caller that builds a fresh one per sentence re-fetches
  the same handful of records once per sentence.  `supersession-map` is that caller: it
  re-examines every entry the closure displaces on each merging assert."
  ([kb term visible?]
   (let [sym   (rewrite-symbols kb visible? term)
         rules (cond->> (tax/rewrite-rules (:taxonomy kb))
                 visible? (filterv #(visible? (:handle %))))]
     (rewrite/normalize-sentence rules sym))))

(defn rewrite-term
  "`rewrite-term*` for a caller that has a context rather than a built predicate — the
  ordinary spelling.  Its docstring above owns the semantics."
  ([kb term] (rewrite-term* kb term nil))
  ([kb term context] (rewrite-term* kb term (res/visible-supporter-fn kb context))))

(defn displaced-terms*
  "The `{old-term representative}` rewrites a sentence undergoes, given the visibility
  predicate already built — empty when nothing in it has merged."
  [kb sentence visible?]
  (into {}
        (keep (fn [t]
                (when (and (symbol? t) (not (sx/variable? t)))
                  (let [r (res/representative-in kb visible? t)]
                    (when (not= r t) [t r])))))
        (tree-seq sequential? seq sentence)))

(defn displaced-terms
  "The `{old-term representative}` rewrites a sentence undergoes — empty when nothing
  in it has merged.  This is what a supersession *records*, so `why-not` can name the
  representative that displaced a spelling rather than merely reporting that one did.

  Scoped by `context` like every other class read: the spelling that displaced this one
  is the one *its own* context elected, and naming a representative elected by an edge
  that context cannot see would make `why-not` cite a merge nobody there has heard of.
  The `visible?` arity is `rewrite-term*`'s, and for the same caller."
  ([kb sentence] (displaced-terms* kb sentence nil))
  ([kb sentence context] (displaced-terms* kb sentence (res/visible-supporter-fn kb context))))

(defn rewrite-goal
  "A query goal with its terms rewritten to their class representatives.

  A caller who has not heard about a merge still asks under the old spelling, and
  that spelling's own sentexes are no longer believed — so the goal is rewritten
  before lookup and migration stays invisible to them.  Rewriting is a *question*
  transformation only: `handle-of` and the `lookup` levels deliberately do **not** do
  it, because they answer about storage rather than about truth.

  **`different` is exempt.**  Rewriting its arguments would map each to its class
  representative, so a merged pair would compare equal — and since reading class
  membership is the entire job of `different`, every `different` goal would go false
  the moment anything merged.  Its arguments are already rewrite-invariant (the
  prover consults the closure directly), so this exempts it explicitly rather than
  relying on the rewrite happening to be a no-op.

  Rewritten only by the merges `context` can see (`rewrite-term`'s three-arity): a
  question asked from a microtheory is a question about what that microtheory holds,
  so a merge it does not inherit must not rename what it asked."
  ([kb goal] (rewrite-goal kb goal nil))
  ([kb goal context]
   (if (and (sequential? goal) (= 'different (nm/functor goal)))
     goal
     (rewrite-term kb goal context))))

(defn- rule-touches-merged-predicate?
  "Does rewriting this rule change a **predicate or type** — a non-individual symbol
  it mentions — rather than only an individual constant?  That is the case a
  predicate/type merge (docs/equality.md, round two) must migrate a rule for, since
  it changes a functor the rule reasons over; an individual-only rewrite is held
  back.  `displaced-terms` already computes the `{changed rep}` map, so this only
  asks whether any changed spelling is a non-individual."
  [kb sentence]
  (boolean (some #(not (nm/individual? %)) (keys (displaced-terms kb sentence)))))

(defn rewritable-sentex?
  "May this stored sentex be migrated by an equality merge?

  A **rule** is held back for an *individual* merge — rewriting a rule's individual
  constant is congruence over a schema rather than over ground content, and the
  rewritten copy would fire alongside its original — but **migrated for a predicate
  or type** merge, which changes a functor the rule reasons over (`birthplaceOf ⇒
  bornIn`, `dog ⇒ canine`): the original is superseded and the twin carries the
  inference (docs/equality.md, round two).  A rule's `exceptWhen` exceptions ride
  separate meta-sentexes keyed by the rule's handle; migration re-points them onto the
  twin (`special/migrate-rule-exceptions`), and a NAF (`unknown`) antecedent lives
  *in* the rule sentence, so it rewrites with the rule and re-posts through the twin's
  own `index-rule-sentex` — so an exception/NAF rule migrates with its guard intact.

  A non-rule is migratable unless it is one of the equality relations themselves:
  rewriting `(rewriteOf Pref Dep)` yields `(rewriteOf Pref Pref)`, the self-edge
  `wff` exists to refuse."
  [kb sentex]
  (if (rules/rule? sentex)
    (rule-touches-merged-predicate? kb (:sentence sentex))
    (let [s (:sentence sentex)]
      (and (not (equality-sentence? s))
           (not (equality-sentence? (sx/positive-body s)))))))

;; ---- matching ------------------------------------------------------------

(defn sentexes-matching-as-stored
  "*Believed* sentexes matching `sentence` **as spelled**, in `context` —
  `sentexes-matching` without the equality goal rewrite.

  For a caller iterating the engine's own storage rather than asking a question about the
  world.  `sentexes-matching` rewrites a goal to the class representative, which is right for a
  *question* — a caller who has not heard about a merge still gets its answer — and wrong
  for an iteration, because it silently redirects: asking about a body an equality has
  retired hands back the *representative's* sentexes, and the caller then reports them
  under the spelling it asked with.  `settle`'s walk over the P/¬P coincidence set is that
  caller, and a superseded body has to answer *nothing* there, which is what it does here:
  its own sentexes are no longer believed, so the belief filter empties it and the
  representative's body reports the pair once, under its own name.

  Everything else is `sentexes-matching`'s: literal (no subtype expansion), both
  symmetric argument orders, belief-sensitive, clear of the `exceptWhen`
  meta-sentexes."
  ([kb sentence] (sentexes-matching-as-stored kb sentence '?ctx))
  ([kb sentence context]
   ;; This *is* the level-2 (`:local`) matcher — one literal context, no subtype
   ;; fan-out, both symmetric argument orders, belief-filtered, clear of the
   ;; exceptWhen meta-sentexes.  `res/raw-match` is exactly that, so routing
   ;; through it (rather than a bare `p/lookup`) shares `match-one`'s argument-root
   ;; retrieval: a pattern pinning an argument *after* a variable — `(parentOf ?x
   ;; Tom)` — is answered from the predicate-scoped argument root
   ;; (`[:argument-root parentOf 2 Tom]`), not a full leading-variable trie fan-out.  `without-excepted` then drops
   ;; what a visible `except` hides here (docs/contexts.md).  Both halves are
   ;; belief-following; the stored record already fetched to unify against rides
   ;; along as the third element, so this costs no extra round trip.
   (->> (res/raw-match kb sentence context)
        (res/without-excepted kb context)
        (res/without-retired kb context)
        (map (fn [m] (nth m 2))))))

(defn sentexes-matching
  "*Believed* sentexes matching `sentence` in `context` — the implementation behind
  `vaelii.core/sentexes-matching`, which owns the user-facing docstring.  Literal (no subtype
  expansion), belief-sensitive (a stored-but-disbelieved sentex is excluded)."
  ([kb sentence] (sentexes-matching kb sentence '?ctx))
  ([kb sentence context]
   ;; a goal naming a term an equality merge has retired is rewritten to the class
   ;; representative first — the retired spelling stays a usable *question* even
   ;; though it is no longer a usable *answer* (docs/equality.md)
   (sentexes-matching-as-stored kb (rewrite-goal kb sentence context) context)))

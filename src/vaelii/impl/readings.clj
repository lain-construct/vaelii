;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.readings
  "What a reader's verdicts move with no relabel: each reader's reading of what it
  withdraws at its own context, read again where a settle moved it and kept in
  `:own-readings` for the next settle to diff against (the published window), and the
  rules a moved verdict releases.  A settle reads both once per pass through
  `reconcile-own!` and `released!`.  See docs/nmtms.md, \"The published window\"."
  (:require [clojure.set :as set]
            [vaelii.impl.decide :as decide]
            [vaelii.impl.decide.inherited :as inherited]
            [vaelii.impl.decide.negation :as negation]
            [vaelii.impl.discovery :as discovery]
            [vaelii.impl.inherit :as inherit]
            [vaelii.impl.jtms :as jtms]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.resolution :as res]
            [vaelii.impl.sentex :as sx]
            [vaelii.impl.special :as special]
            [vaelii.impl.taxonomy :as tax]
            [vaelii.impl.types.reasoning :as reasoning]))

;; ---- what a reader's verdict releases ---------------------------------------
;; A verdict moves belief with no relabel, so the rules watching what it moved are
;; re-checked and re-chained by the pass that reads it.

(defn- released-by-defeat
  "The rules watching the predicate of a sentex in `handles`, whose belief a verdict
  moved: an `(unknown S)` that now holds, or an exception that no longer does
  (docs/naf.md).  Returns the rule handles, which the pass re-chains."
  [kb handles]
  (into #{}
        (comp (keep #(p/get-sentex (:records kb) %))
              (mapcat #(special/rules-watching kb (sx/sentence-of %))))
        handles))

(defn- released-by-negations
  "The rules watching either polarity of a body whose reader-decided negation pair may
  have moved a verdict with no relabel of the rule's firing: a body
  `negation/take-moved-negations!` names, and the body of a pair member in `region` (a
  delay, forced only while such a pair is stored) that `read` (a volatile set) does not
  hold yet, which this adds.  Each polarity is posted to
  the re-check queue (`special/recheck-on-sentence`) as its arrival would be, and the
  rules are returned for the pass to re-chain (`released-by-defeat`).  The watched rules
  are read only when a body is named."
  [kb region read]
  (let [bodies (into (negation/take-moved-negations! kb)
                     (negation/negation-bodies kb #(let [fresh (into [] (remove @read) @region)]
                                                     (vswap! read into fresh)
                                                     fresh)))]
    (when (and (seq bodies) (seq (reads/watched-rules (:index kb))))
      (into #{}
            (comp (mapcat #(vector % (list 'not %)))
                  (mapcat (fn [s]
                            (special/recheck-on-sentence kb s)
                            (special/rules-watching kb s))))
            bodies))))

(defn- released-by-verdicts
  "The rules watching an inherited clash's member whose verdict at a vantage moved between
  `was` and `now` (`inherited-losers`), which a verdict moves with no relabel: each such member's
  sentence is posted to the re-check queue as its arrival would be
  (`special/recheck-on-sentence`), and the rules are returned for the pass to re-chain
  (`released-by-defeat`)."
  [kb was now]
  (let [moved (into (into #{} (remove was) now) (remove now) was)]
    (when (seq moved)
      (doseq [h moved]
        (when-let [s (p/get-sentex (:records kb) h)]
          (special/recheck-on-sentence kb (sx/sentence-of s))))
      (released-by-defeat kb moved))))

(defn- preserved-rejoins-for
  "The forward rules whose preserving joins arbitration's defeat of `handles` may have
  moved, for the pass to re-chain (docs/inherit.md)."
  [kb handles]
  (into #{}
        (comp (keep #(p/get-sentex (:records kb) %))
              (mapcat #(inherit/rejoin-rules kb (sx/sentence-of %))))
        handles))

(defn- released-by-own
  "The rules watching a handle whose belief at its own context moved (`own`, as
  `special/reconcile-own-withdrawals!` answers it), which a verdict moves with no relabel,
  and the rules whose preserving joins it can move (`preserved-rejoins-for`): each such
  handle's sentence is posted to the re-check queue as its arrival would be, and the rules
  are returned for the pass to re-chain (`released-by-defeat`)."
  [kb {:keys [back gone]}]
  (let [moved (into (set back) gone)]
    (when (seq moved)
      (doseq [h moved]
        (when-let [s (p/get-sentex (:records kb) h)]
          (special/recheck-on-sentence kb (sx/sentence-of s))))
      (into (released-by-defeat kb moved) (preserved-rejoins-for kb moved)))))

;; ---- the readers' own-context readings -------------------------------------

(def ^:private reading-keys
  "The keys of `:own-readings` `reader-moves` writes; the settle keeps memos of its own
  beside them."
  [:rest :cands :reach :closure :by-ctx :readers :watched :own-out])

(defn own-out
  "The handles IN and withdrawn at their own context as the last `reader-moves` read
  them, or nil when none are."
  [kb]
  (not-empty (:own-out @(reasoning/own-readings kb))))

(defn- with-contexts
  "`closure` (`{handle context}`) and `by-ctx` (`{context #{handle}}`) with the stored
  handles of `hs` added."
  [[closure by-ctx] kb hs]
  (reduce (fn [[cl bc :as acc] h]
            (if-let [sx (p/get-sentex (:records kb) h)]
              (let [c (:context sx)]
                [(assoc cl h c) (update bc c (fnil conj #{}) h)])
              acc))
          [closure by-ctx] hs))

(defn- without-handles
  "`closure` and `by-ctx` with the handles of `hs` removed."
  [[closure by-ctx] hs]
  (reduce (fn [[cl bc :as acc] h]
            (if-let [[_ c] (find cl h)]
              (let [left (disj (get bc c) h)]
                [(dissoc cl h) (if (seq left) (assoc bc c left) (dissoc bc c))])
              acc))
          [closure by-ctx] hs))

(defn- readers-seeing
  "The readers of `readers` (a map keyed by context) whose ancestor set holds context
  `x`, walking the smaller of `x`'s descendants and `readers`.  Unscoped, since the
  ancestor set is the one `res/withdrawal` decides over."
  [tax readers x]
  (let [down (tax/context-down-global tax x)]
    (if (< (count down) (count readers))
      (filterv #(contains? readers %) down)
      (filterv #(contains? (tax/context-up-global tax %) x) (keys readers)))))

(defn- reach-moved
  "The readers of `by-ctx` a move of the handles `moved` can reach, from the index part of
  the stamp: those whose ancestor set holds the context of one of them, and every reader
  when one is stored with no context, which every reader sees."
  [kb by-ctx moved]
  (let [recs (:records kb)
        tax  (reasoning/taxonomy kb)
        ctxs (into #{} (keep #(when-let [sx (p/get-sentex recs %)] [(:context sx)])) moved)]
    (if (contains? ctxs [nil])
      (keys by-ctx)
      (into #{} (mapcat #(readers-seeing tax by-ctx (first %))) ctxs))))

(defn- reader-moves
  "The belief at their own context that the nogoods a reader decides moved since the last
  call, as `{:moved :withdrawn-before :gone :back}`, `:gone` and `:back` the handles
  newly withdrawn at their own context and the ones given back, with this call's readings
  recorded in `:own-readings` for the next one to diff against, and their union under
  `:own-out` (`own-out`).  A reader in `read` was read earlier in this settle, so its
  last reading is no before-state; `:read` is the readers this call read.  A reader is a context holding a
  handle of the closure of `decide/reach-handles`, and its
  reading is the part of `res/defeat-reading` stored there and IN.  Only the readers a
  move reaches are read again: those whose watch meets `region`, the relabelled window,
  those that see a handle that entered or left `reach-handles`, and those of a handle the
  closure gained; every reader when the rest of `res/withdrawal-stamp` moved, and on a
  rebuild (`rebuilding?`), whose region is the store (docs/nmtms.md, \"The published
  window\")."
  [kb region read rebuilding?]
  (let [prev     @(reasoning/own-readings kb)
        guards?  (res/guards? kb)
        ;; the guarded rules whose answer at a reader below them moved, and what their
        ;; firings reach (`res/guard-closure`)
        gnoted   (res/take-guard-window! kb)]
    (if-not (or (decide/live? kb) guards?)
      (let [bw (into #{} (mapcat (comp :out val)) (:readers prev))]
        ;; read, and nothing withdrawn: an empty reading, not a missing one
        (when-not (and (some? prev) (empty? (select-keys prev reading-keys)))
          (swap! (reasoning/own-readings kb) #(apply dissoc (or % {}) reading-keys)))
        {:moved bw :withdrawn-before (into #{} (comp (remove #(contains? read (key %))) (mapcat (comp :out val)))
                                           (:readers prev))
         :gone #{} :back bw :read #{}})
      (let [tms          (reasoning/tms kb)
            [cands rest] (res/withdrawal-stamp kb)
            ;; a rebuild's region is the store, so reading every reader costs less
            ;; than asking which of them the region reaches
            full?        (or (nil? prev) rebuilding? (not= rest (:rest prev)))
            reach        (if (and (not full?) (= cands (:cands prev)))
                           (:reach prev)
                           (decide/reach-handles kb))
            recs         (:records kb)
            guarded      (when guards? (set (reads/watched-rules (:index kb))))
            [closure by-ctx q]
            (if full?
              ;; the cached closure of the candidates and the `except` targets, which holds that of `reach`'s candidates
              (let [[cl bc] (with-contexts [{} {}] kb
                              (cond-> (or (res/withdrawable-closure kb) #{})
                                guards? (into (res/guard-closure kb guarded))))]
                [cl bc (into (set (keys bc)) (keys (:readers prev)))])
              (let [old     (:closure prev)
                    entered (if (identical? reach (:reach prev)) #{} (set/difference reach (:reach prev)))
                    left    (if (identical? reach (:reach prev)) #{} (set/difference (:reach prev) reach))
                    rests?  (fn [h] (some (fn [j] (some #(contains? old %)
                                                        (some-> (jtms/justification tms j) jtms/rests-on)))
                                          (jtms/supports tms h)))
                    ;; a rule whose guard moved reaches its every firing; a firing that
                    ;; arrived or left reaches its own conclusion
                    {grules :rules gfired :fired}
                    (when guards? (res/guard-moves kb guarded gnoted region))
                    greach  (cond-> (if (seq grules) (res/guard-closure kb grules) #{})
                              (seq gfired) (into (jtms/consequence-closure tms gfired)))
                    grown   (into (into #{} (remove #(contains? old %)) entered)
                                  (filter #(and (not (contains? old %)) (rests? %)))
                                  region)
                    added   (-> (into #{} (remove #(contains? old %))
                                      (when (seq grown) (jtms/consequence-closure tms grown)))
                                (into (remove #(contains? old %)) greach))
                    dead    (into #{} (filter #(and (contains? old %) (nil? (p/get-sentex recs %))))
                                  region)
                    [cl bc] (-> [old (:by-ctx prev)] (without-handles dead) (with-contexts kb added))
                    watched (:watched prev)]
                [cl bc (-> #{}
                           (into (comp (mapcat #(res/near-handles tms %)) (mapcat #(get watched %)))
                                 region)
                           (into (reach-moved kb bc (into entered left)))
                           (into (keep #(get cl %)) added)
                           (into (keep #(get cl %)) greach))]))
            was  (:readers prev)
            step (fn [[readers watched moved before oo gone back] c]
                   (let [old  (get was c)
                         mine (get by-ctx c)
                         [out watch] (when mine (res/defeat-reading kb c))
                         own  (if (and mine (seq out))
                                (let [[small big] (if (< (count mine) (count out)) [mine out] [out mine])]
                                  (into #{} (filter #(and (contains? big %) (jtms/in? tms %))) small))
                                #{})
                         ow   (:out old)
                         watched (as-> watched w
                                   (reduce #(let [cs (disj (get %1 %2) c)]
                                              (if (seq cs) (assoc %1 %2 cs) (dissoc %1 %2)))
                                           w (:watch old))
                                   (if mine
                                     (reduce #(update %1 %2 (fnil conj #{}) c) w watch)
                                     w))]
                     [(if mine (assoc readers c {:out own :watch (set watch)}) (dissoc readers c))
                      watched
                      (-> moved (into (remove #(contains? ow %)) own)
                          (into (remove #(contains? own %)) ow))
                      (cond-> before (not (contains? read c)) (into ow))
                      (-> (reduce disj oo ow) (into own))
                      (into gone (remove #(contains? ow %)) own)
                      (into back (remove #(contains? own %)) ow)]))
            prev-out (:own-out prev #{})
            [readers watched moved before oo gone back]
            (reduce step [(if full? {} was) (if full? {} (:watched prev)) #{} #{}
                          (if full? #{} prev-out) #{} #{}]
                    q)
            ;; a full read starts from nothing, so a reader it no longer holds gives back
            ;; what it held
            back (cond-> back full? (into (remove #(contains? oo %)) prev-out))]
        (swap! (reasoning/own-readings kb)
               merge {:rest rest :cands cands :reach reach :closure closure :by-ctx by-ctx
                      :readers readers :watched watched :own-out oo})
        {:moved moved :withdrawn-before before :read (set q) :prev-out prev-out
         :gone (into #{} (remove #(contains? prev-out %)) gone)
         :back (into #{} (remove #(contains? oo %)) back)}))))

(defn reader-window
  "What a settle accumulates across its `reader-moves` calls: the handles moved, the ones
  withdrawn before the settle and the readers read; and across its passes, the inherited
  losers the last pass read (`losers`, at the start) and the window handles
  `released-by-negations` has read."
  [losers]
  {:moved (volatile! #{}) :before (volatile! #{}) :read (volatile! #{})
   :losers (volatile! losers) :negations (volatile! #{})})

(defn- note-readings!
  "Fold a `reader-moves` answer `rm` into the settle's window `win`, and return `rm`."
  [win rm]
  (vswap! (:moved win) into (:moved rm))
  (vswap! (:before win) into (:withdrawn-before rm))
  (vswap! (:read win) into (:read rm))
  rm)

(defn reconcile-own!
  "Read the readers a move reaches again (`reader-moves`), fold the answer into the
  settle's window `win`, and reconcile the unscoped caches with what each verdict
  withdrew at its own context or gave back (`special/reconcile-own-withdrawals!`), whose
  answer, `{:back :gone}` or nil, this returns.  `region` is the relabelled window, as a
  delay."
  [kb win region rebuilding?]
  (let [rm (note-readings! win (reader-moves kb @region @(:read win) rebuilding?))]
    (special/reconcile-own-withdrawals! kb (own-out kb) rm)))

(defn released!
  "The rules a verdict moved with no relabel this pass: those watching an inherited clash's
  member whose verdict at a vantage moved since the last pass (`released-by-verdicts`,
  against the losers `win` holds, which this replaces), those watching a handle whose
  own-context belief moved (`own`, `reconcile-own!`'s answer; `released-by-own`), and
  those watching a body whose negation pair may have moved (`released-by-negations`)."
  [kb win region own]
  (let [losers (if (seq (inherited/inherited-clashes kb)) (discovery/inherited-losers kb) #{})
        was    @(:losers win)]
    (vreset! (:losers win) losers)
    (-> #{}
        (into (released-by-verdicts kb was losers))
        (into (released-by-own kb own))
        (into (released-by-negations kb region (:negations win))))))

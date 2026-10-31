;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.profile
  "What a KB is asked, and what each answer costs the index: seven tallies behind one
  switch. `:goals` (retrieval decisions by shape and access path), `:reads` (`IndexStore`
  reads by family), `:fan` (trie walks and node probes), `:sift` (candidates returned,
  unified and matched), `:fetches` (`RecordStore` reads by kind), `:writes` and `:retracts`
  (per-family index cost by functor). The switch and the store are one atom, nil when off, so
  every call site is a deref and a `nil?` check. A goal's key is `[functor polarity
  adornment path]`, one adornment character per argument: `b` ground atom, `B` ground
  compound, `n` ground token the roots do not key, `f` open atom, `F` open compound. See
  docs/profile.md."
  (:require [vaelii.impl.sentex :as sx]))

;; nil when off; otherwise `{:t0 <nanos> :goals {} :reads {} :fan {} :sift {} :fetches {}
;; :writes {} :retracts {}}`.  One atom rather than a flag beside a store, so a call site
;; cannot read the flag on and the store as nil.
(defonce ^:private tally (atom nil))

(defn profiling?
  "Is the instrument collecting?"
  []
  (some? @tally))

(defn start
  "Begin collecting, dropping whatever a previous run left.  Bare, not `!`: a tally is
  derived from a workload nobody stored, so nothing it holds is knowledge and re-running
  the workload recomputes it."
  []
  (reset! tally {:t0 (System/nanoTime) :goals {} :reads {} :fan {} :sift {} :fetches {}
                 :writes {} :retracts {}})
  nil)

(defn- read-out [t]
  (when t
    (-> (dissoc t :t0)
        (assoc :elapsed-ms (/ (- (System/nanoTime) (long (:t0 t))) 1e6)))))

(defn snapshot
  "The tallies so far as plain data, or nil when the instrument is off:

      {:elapsed-ms  how long this run has been collecting
       :goals   {[functor polarity adornment path] count}
       :reads   {family count}
       :fan     {first-token {:calls :visits :widest :handles :decades {n count}}}
       :sift    {[functor polarity adornment path] {:calls :returned :unified :matched}}
       :fetches {kind count}
       :writes  {functor {:asserts :levels :terms :roots :term-names :slots}}
       :retracts {functor {:retracts :levels :terms :roots :term-names :slots :dead}}}"
  []
  (read-out @tally))

(defn stop
  "Stop collecting and return the final snapshot (nil when it was not running).

  One CAS rather than a deref and a `reset!`: the reading taken and the instrument
  cleared are the same step, so a tally filed between the two is reported rather than
  wiped unread."
  []
  (read-out (first (swap-vals! tally (constantly nil)))))

;; ---- the call site every tally goes through ----------------------------------

(defmacro ^:private tallying
  "`(update-in tally path f args…)`, applied only while the instrument is still collecting:
  the one shape every `record-*` files its count in. The deref is the fast path, and the
  `when` inside the swap makes `stop` final: a bare `swap!` after `stop` recreates a tally
  with no `:t0`, which leaves `profiling?` true and makes `snapshot` read `(long nil)`.
  Answers nil."
  [path f & args]
  `(do (when @tally
         (swap! tally (fn [t#] (when t# (update-in t# ~path ~f ~@args)))))
       nil))

;; ---- the goal tally -----------------------------------------------------

(defn- arg-class
  "One character for one argument position — see the alphabet in the namespace docstring."
  [a]
  (if (sequential? a)
    (if (sx/ground-term? a) \B \F)
    (cond
      (sx/variable? a)       \f
      (sx/indexable-term? a) \b
      :else                  \n)))

(defn shape-of
  "One literal's tally key, `[functor polarity adornment path]`.  Public because the oracle
  asks for a shape directly rather than inferring it from a count."
  [body polarity path]
  (if (or (not (sequential? body)) (empty? body))
    [:none polarity "" path]
    (let [f (first body)]
      [(if (and (symbol? f) (sx/variable? f)) :open f)
       polarity
       (apply str (map arg-class (rest body)))
       path])))

(defn record-goal
  "Tally one `candidate-handles` decision: the pattern sentex it was asked for and the
  access path it chose.  A deref and a `nil?` check when the instrument is off."
  [pat path]
  (tallying [:goals (shape-of (sx/body pat) (sx/polarity pat) path)] (fnil inc 0)))

(defn record-literal
  "Tally one retrieval decision taken over a bare sentence rather than a pattern sentex —
  the set-algebra matcher's, which is handed the literal and admits only positive ones."
  [sentence path]
  (tallying [:goals (shape-of sentence :positive path)] (fnil inc 0)))

;; ---- the read tally -----------------------------------------------------

(def ^:dynamic *handle-sink*
  "nil, or a fn of one handle, called with each sentex handle a `RecordStore` fetch reads
  (`record-fetch`'s two-argument arity) and each handle an `IndexStore` posting read
  answers (`record-posting`).  The handle twin of `reads/*contexts-read*`: a test binds it
  around a write to bound the stored sentexes the write reads (`padding_blindness_test`).
  A count, a child-token or a name-set read answers no handle and calls nothing."
  nil)

(defn record-posting
  "`hs`, the handles one `IndexStore` read answers, after passing each to
  `*handle-sink*` when it is bound."
  [hs]
  (when-let [f *handle-sink*] (run! f hs))
  hs)

(defn record-read
  "Tally one `IndexStore` read against the family that answered it.  This is the tally
  that says whether a family pays for itself, so the names are the families and not the
  method names: several methods read the argument roots, and what a policy would drop is
  the family."
  [family]
  (tallying [:reads family] (fnil inc 0)))

;; ---- the record-fetch tally ---------------------------------------------

(defn record-fetch
  "Tally one `RecordStore` read against its kind, one of the seven `:fetches` names in the
  namespace docstring. The record-store twin of `record-read`: a read tally cannot see a
  fetch per candidate handle. Keyed by kind, not by handle or functor. A deref and a
  `nil?` check when the instrument is off. With `id`, the fetched record's handle also goes
  to `*handle-sink*`."
  ([kind]
   (tallying [:fetches kind] (fnil inc 0)))
  ([kind id]
   (when-let [f *handle-sink*] (f id))
   (tallying [:fetches kind] (fnil inc 0))))

;; ---- the sift tally -----------------------------------------------------

(defn- bump-sift [row ^long returned ^long matched ^long unified]
  (-> row
      (update :calls    (fnil inc 0))
      (update :returned (fnil + 0) returned)
      (update :matched  (fnil + 0) matched)
      (update :unified  (fnil + 0) unified)))

(defn record-sift
  "Tally one hierarchical retrieval's three widths: candidate handles the argument-root probe
  (`lead-candidates`) handed the matcher (`returned`), those that reached `unify` after the
  liveness, predicate and context filters (`unified`), and those that matched (`matched`).
  Keyed by the literal's shape and the retrieval path, like `:goals`. The call site realizes
  the full candidate seq only while collecting. The args are unhinted because a fn taking
  primitive `long`s is capped at four."
  [sentence path returned matched unified]
  (tallying [:sift (shape-of sentence :positive path)]
            bump-sift (long returned) (long matched) (long unified)))

;; ---- the fan tally ------------------------------------------------------

(defn- decade
  "The power of ten `n` sits at — 1, 10, 100 — so a fan histogram has a bounded number of
  buckets whatever the corpus size."
  ^long [^long n]
  (if (< n 1)
    0
    (loop [d 1] (if (< n (* 10 d)) d (recur (* 10 d))))))

(defn- bump-fan [row ^long visits ^long widest ^long handles]
  (let [{:keys [calls] :or {calls 0}} row]
    (-> row
        (assoc :calls (inc (long calls)))
        (update :visits (fnil + 0) visits)
        (update :widest (fnil max 0) widest)
        (update :handles (fnil + 0) handles)
        (update-in [:decades (decade visits)] (fnil inc 0)))))

(defn record-fan
  "Tally one trie walk: `visits` node probes, a frontier that reached `widest`, and
  `handles` handles at the terminus.  Keyed by the path's first token, which is the
  functor for a positive fact and `:false` for a negative."
  [pattern ^long visits ^long widest ^long handles]
  (tallying [:fan (first pattern)] bump-fan visits widest handles))

;; ---- the write tally ----------------------------------------------------

(defn- write-key [sentex]
  (if (some? (:antecedent sentex))
    :rule
    (let [b (sx/body sentex)]
      (if (and (sequential? b) (seq b) (symbol? (first b))) (first b) :other))))

(defn- bump-write [row {:keys [levels terms roots term-names slots]}]
  (-> row
      (update :asserts (fnil inc 0))
      (update :levels  (fnil + 0) (long levels))
      (update :terms   (fnil + 0) (long terms))
      (update :roots   (fnil + 0) (long roots))
      (update :term-names (fnil + 0) (long term-names))
      (update :slots   (fnil + 0) (long slots))))

(defn record-index-write
  "Tally one `index-sentex`: how many trie levels it touched and how many keys each of
  the flat families took.  Call sites guard on `profiling?` so the counts map is built
  only while collecting."
  [sentex counts]
  (tallying [:writes (write-key sentex)] bump-write counts))

(defn- bump-retract [row {:keys [levels terms roots term-names slots dead]}]
  (-> row
      (update :retracts (fnil inc 0))
      (update :levels   (fnil + 0) (long levels))
      (update :terms    (fnil + 0) (long terms))
      (update :roots    (fnil + 0) (long roots))
      (update :term-names (fnil + 0) (long term-names))
      (update :slots    (fnil + 0) (long slots))
      (update :dead     (fnil + 0) (long dead))))

(defn record-index-retract
  "Tally one `unindex-sentex!`: the same families as `record-index-write` plus `:dead`, the
  trie nodes this retraction emptied. `:dead` depends on what else is stored under the same
  prefix, so it is a tally of its own."
  [sentex counts]
  (tallying [:retracts (write-key sentex)] bump-retract counts))

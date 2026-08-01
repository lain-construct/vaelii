(ns vaelii.impl.kv
  "The key-value substrate the index rests on, and the one `IndexStore`
  implementation written over it.

  The index — the trie, the secondary roots, the rule predicate index, the exception
  re-check index, and the inverted term index — is *all* sets and counters keyed
  by structured vectors.  `KvIndexStore` encodes that structure once, in terms of a
  small `KvBackend` protocol; a backend is then just an adapter that says how a
  scalar, a counter, and a set live in some store.  An in-memory map
  (`vaelii.impl.memory`) and an on-disk WAL (`vaelii.impl.disk.kv`) are two such
  adapters; a SQL or overlay backend is another.

  ## The flattened count-aware trie

  A sentex is indexed by its trie path.  The trie is flattened — every node,
  identified by its path prefix, is exactly three keys:

    count-key  [:trie :count prefix]  ->  integer: how many sentexes live at the leaves
                                     under this prefix (selectivity without walking).
    set-key    [:trie :children prefix]  ->  a SET: the next possible token labels (the
                                     node's child edges).
    leaf-key   [:trie :handles prefix]  ->  a SET: the handles of the sentexes whose path
                                     ends exactly here.

  **Child edges and leaf handles are separate keys because the trie is ragged.**
  Paths differ in length with arity, so one sentex's *full* path can be a proper
  prefix of another's: `(rel A B)` in `CeeContext` keys as `[rel A B CeeContext]`,
  and `(rel A B CeeContext X)` in `DeeContext` keys as `[rel A B CeeContext X
  DeeContext]` — the first path is an interior node of the second.  Storing both
  handles and child labels in one set therefore mixed them, and a caller could not
  tell them apart by type (a handle is an integer, and so is the token `1970`).  Two
  keys make the distinction structural: `lookup` reads only the leaf key at its
  terminus, so it can never return a token as a handle, and `children` reads only
  the child set, so `plan`'s fan-out divisor can never count a handle as a branch.

  Alongside the trie sit the secondary roots, the rule predicate index, the
  exception re-check index, and the inverted term index — all flat sets whose
  cardinality is their own size.  One more flat set, the **term roster**
  `[:term-roster]`, holds the term index's *names* rather than handles, so the
  vocabulary can be listed and counted in O(terms) instead of a walk over every record.

  Contract: lookup expects a *full* path (sentence tokens + a context slot; the
  context may itself be a variable).  A short pattern terminates on an interior
  node, whose leaf key is empty, so it yields nothing rather than that node's child
  labels dressed up as handles.

  ## The `KvBackend`

  Logical keys are structured vectors and set members are bare values; a backend
  turns those into whatever its store wants (an in-memory map uses them directly; the
  on-disk backend nippy-frames them into its log).  The load-bearing ops are
  `kv-batch` (the whole index write for one sentex lands as one unit — one batched
  write) and `kv-intersect` (the multi-column narrowing `sentexes-with-args` needs, one
  set intersection rather than N fetch-and-filter reads).  A batch op is a vector
  `[op key & args]` with `op` one of `:put`, `:delete`, `:increment`,
  `:decrement`, `:add-to-set`, `:remove-from-set`; `kv-batch`
  returns one reply per op in order (only `:increment`/`:decrement` replies — the post-op
  counter value — are read; the rest are placeholders that keep the vector aligned).

  **`kv-member?` is a membership test, not a fetch**, and it is its own op because on
  several backends those cost different orders.  `exception-rule?` is the gate
  `chain/rule-view-of` takes once per candidate rule per new datum, so answering it by
  materializing the roster and testing the result makes forward chaining a product of
  two KB-sized quantities.  A flat-map backend hands the stored set back by reference
  and hides the distinction entirely; a dense one holds the roster as an `IntPostings`,
  where 1e5 gate calls against a roster of 1,000 cost 15,926 ms built-then-tested
  against 87 ms on the flat map — so the op exists to let each backend answer with the
  probe it already has (a hash lookup, a binary search, a bitmap test)."
  (:require [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx]))

(def index-layout-version
  "Which key shapes this build's index is written in.

  The key families below — `[:trie :count|:children|:handles prefix]`, the roots, the
  rule / exception indexes, the term index and the roster — *are* the index's portable
  form, so a dump of them is only readable by a build that agrees on them.  An index
  written in a layout this build does not use reads as **empty** rather than as wrong
  (a lookup finds no key and answers nothing), which is fail-safe and undiagnosable —
  so the layout is stated as a number and checked, rather than discovered by a KB that
  quietly stopped answering.

  **Bump it whenever a key shape changes**: a new family, a renamed tag, a different
  arity, or a different value type at an existing key."
  1)

(defprotocol KvBackend
  "The key-value operations `KvIndexStore` bottoms out on.  Keys are structured
  vectors; set members are bare values.  Each adapter maps those onto its store."
  ;; scalars / counters
  (kv-get  [b k]   "The value at `k`, or nil.")
  (kv-put  [b k v] "Set `k` to `v`.")
  (kv-delete  [b k]   "Delete `k`.")
  (kv-increment [b k]   "Increment the counter at `k`; return the new value.")
  (kv-decrement [b k]   "Decrement the counter at `k`; return the new value.")
  ;; sets
  (kv-add-to-set     [b k member] "Add `member` to the set at `k`.")
  (kv-remove-from-set     [b k member] "Remove `member` from the set at `k` (dropping the key when it empties).")
  (kv-members [b k]        "The members of the set at `k`, as a set (empty when absent).")
  (kv-member? [b k member] "Is `member` in the set at `k`? — answered without building the set.")
  (kv-count    [b k]        "The cardinality of the set at `k` (0 when absent).")
  ;; set intersection — one operation over N keys
  (kv-intersect [b ks] "The intersection of the sets at `ks`, as a set.")
  ;; batch — a sequence of write ops applied as one unit; returns one reply per op
  (kv-batch [b ops] "Apply the write ops `[op key & args]` as one unit; return the replies in order.")
  ;; the portable projection, both ways.  `kv-entries` is the only way to ask a backend
  ;; for everything it holds; `kv-load` puts an entry back **in the backend's own
  ;; representation**, which a bare `kv-put` cannot do — a backend that packs handle sets
  ;; into int postings would take a plain set from `kv-put` and then fail the next
  ;; `kv-add-to-set` against it.
  (kv-entries [b]         "Every entry as a lazy `[key value]` seq; set values as Clojure sets, counters as longs.")
  (kv-load    [b entries] "Install `[key value]` entries into an empty backend, in this backend's representation.")
  ;; wholesale wipe (the whole index)
  (kv-clear! [b] "Remove every entry."))

;; ---- logical keys -------------------------------------------------------
;; Structured vectors — a backend encodes them (used directly as map keys in memory;
;; nippy-framed on disk).  The trie node's three keys share the [:trie …] prefix and
;; differ only in the :count/:children/:handles tag; the roots and indexes take
;; their own tags.

(defn- count-key [prefix] [:trie :count prefix])
(defn- set-key   [prefix] [:trie :children prefix])
;; leaf handles live under their own key, never mixed into the child-label set —
;; see the ragged-path note in the namespace docstring.
(defn- leaf-key  [prefix] [:trie :handles prefix])

(defn- rule-ante-key   [pred] [:rule-index :antecedent pred])
(defn- rule-conseq-key [pred] [:rule-index :consequent pred])
;; exception re-check index — a predicate is a symbol and the roster key a keyword,
;; so `[:exception-index :rules]` can never collide with a predicate's own key.
(defn- exception-pred-key  [pred] [:exception-index pred])
(defn- exception-rules-key []     [:exception-index :rules])

;; secondary roots — the trie is ordered [pred args… ctx], so it narrows only
;; left-to-right: it can count "predicate P" but not "context C" (the deepest level)
;; nor "X in argument position 2" without fixing everything to its left.  These
;; single-level roots fill that in; cardinality is the set's own size.
(defn- ctx-key  [c]     [:context-root c])
(defn- pred-key [p]     [:functor-root p])
;; canonicalize the term so a compound query term (a reader-literal list) hits the
;; same key as the stored subterm (built by canon); see sentex/canon.
(defn- arg-key  [pos t] [:argument-root pos (sx/canon t)])
;; public: the columnar index (vaelii.impl.columnar) emits the same term/root keys into
;; a shared backend for the non-trie families, so both stores key identically.
(defn term-key [term]  [:term-index (sx/canon term)])
;; the term roster — ONE set holding every name the term index is keyed by, so the
;; vocabulary is listable and countable without walking the records.  Its own key
;; family, because its members are terms rather than handles: a backend that packs the
;; handle families into int postings routes `[:term-roster]` to its ordinary set storage.
(def ^:private roster-key [:term-roster])

(defn root-keys
  "The secondary-root keys a sentex belongs to: its context always, plus — for a
  *fact* — its functor and each indexable top-level argument by 1-based position.
  A negative fact roots under its positive body's functor (polarity lives in the
  record), so `sentexes-with-functor` covers both polarities.  A rule contributes
  only its context; its predicates live in the rule index instead."
  [sentex]
  (let [b (sx/body sentex)]
    (cond-> [(ctx-key (:context sentex))]
      (and (sequential? b) (seq b) (symbol? (first b)))
      (into (cons (pred-key (first b))
                  (keep-indexed (fn [i a]
                                  (when (sx/indexable-term? a) (arg-key (inc i) a)))
                                (rest b)))))))

(defn sentex-terms
  "The distinct terms that make a sentex findable: its indexable content terms (see
  sentex/index-terms — connective-free, no numbers/strings/variables) plus its
  context."
  [sentex]
  (conj (sx/index-terms sentex) (:context sentex)))

;; ---- the term roster ----------------------------------------------------
;; Membership is *derived from the postings*, never counted separately: a name enters
;; the roster when the first sentex to mention it is indexed (its `[:term-index term]` posting
;; is empty) and leaves when the last one is unindexed (its posting is exactly that
;; handle).  Both are decided from the pre-write state, so each stays one extra read per
;; name and the index write remains a single batch.  Only *symbols* are rostered: a
;; ground compound keys the term index too, but it is a sentence fragment, not a name.

(defn roster-adds
  "The write ops entering `terms` (one sentex's, from `sentex-terms`) in the roster —
  read BEFORE their postings are written, so a name is entered exactly by the first
  sentex to mention it."
  [backend terms]
  (into [] (comp (filter symbol?)
                 (remove (fn [t] (pos? (long (kv-count backend (term-key t))))))
                 (map (fn [t] [:add-to-set roster-key t])))
        terms))

(defn roster-retires
  "The write ops retiring the names in `terms` that `handle` is the last mention of —
  read BEFORE their postings are removed, so a name dies exactly when its posting is
  `#{handle}`."
  [backend terms handle]
  (into [] (comp (filter symbol?)
                 (filter (fn [t]
                           (let [k (term-key t)]
                             (and (= 1 (long (kv-count backend k)))
                                  (contains? (kv-members backend k) handle)))))
                 (map (fn [t] [:remove-from-set roster-key t])))
        terms))

(defn- ->count [reply] (if reply (Long/parseLong (str reply)) 0))
(defn- count-at* [backend prefix] (->count (kv-get backend (count-key prefix))))

(defrecord KvIndexStore [backend]
  p/IndexStore
  ;; One batch, not three round trips: the trie levels, the inverted term index, and
  ;; the secondary roots land together, so a crash cannot leave the index partially
  ;; written for one sentex — e.g. a (genl a b) visible to the trie (query) but absent
  ;; from the [:functor-root] root rebuild-taxonomy reads, which would silently drop the edge
  ;; across a restart.  The record/index seam remains; `vaelii.impl.reindex` is the repair.
  (index-sentex [_ sentex handle]
    (let [pth    (sx/path sentex)
          n      (count pth)
          terms  (sentex-terms sentex)
          roster (roster-adds backend terms)]         ; reads the pre-write postings
      (kv-batch backend
                (concat
                 (mapcat (fn [i]
                           (let [prefix (subvec pth 0 i)]
                             [[:increment (count-key prefix)]
                              (if (< i n)
                                [:add-to-set (set-key prefix)  (nth pth i)]   ; child edge
                                [:add-to-set (leaf-key prefix) handle])]))    ; leaf handle
                         (range (inc n)))
                 (map (fn [t] [:add-to-set (term-key t) handle]) terms)
                 (map (fn [k] [:add-to-set k handle]) (root-keys sentex))
                 roster))
      handle))

  ;; Two batches instead of a round trip per trie level: one to drop the leaf handle
  ;; and decrement every level's counter, whose replies decide which nodes died; one
  ;; to delete the dead nodes' keys, detach them from their parents, and clean the
  ;; term index and roots.
  (unindex-sentex! [_ sentex handle]
    (let [pth      (sx/path sentex)
          n        (count pth)
          terms    (sentex-terms sentex)
          roster   (roster-retires backend terms handle)             ; reads the pre-write postings
          prefixes (mapv #(subvec pth 0 %) (range n -1 -1))          ; leaf .. root
          replies  (kv-batch backend
                             (cons [:remove-from-set (leaf-key pth) handle]
                                   (map (fn [prefix] [:decrement (count-key prefix)]) prefixes)))
          dead     (keep (fn [[prefix c]] (when (<= (long c) 0) prefix))
                         (map vector prefixes (rest replies)))]
      (kv-batch backend
                (concat
                 (mapcat (fn [prefix]
                           ;; the node is empty: drop its counter *and* both of its
                           ;; sets, or an orphaned [:trie :count prefix] leaves
                           ;; plan/prefix-estimate costing off a phantom count forever;
                           ;; then detach its edge from the parent's child set.
                           (cond-> [[:delete (count-key prefix)]
                                    [:delete (set-key prefix)]
                                    [:delete (leaf-key prefix)]]
                             (pos? (count prefix))
                             (conj [:remove-from-set (set-key (subvec pth 0 (dec (count prefix))))
                                    (nth pth (dec (count prefix)))])))
                         dead)
                 (map (fn [t] [:remove-from-set (term-key t) handle]) terms)
                 (map (fn [k] [:remove-from-set k handle]) (root-keys sentex))
                 roster))
      handle))

  (count-at [_ prefix] (count-at* backend prefix))

  (children [_ prefix] (vec (kv-members backend (set-key prefix))))

  ;; The terminus reads the *leaf* key, so an under-long pattern — which stops on an
  ;; interior node — yields nothing instead of that node's child labels, and a full
  ;; path that also happens to be interior (ragged arity) yields its own handles
  ;; without the child token sitting at the same prefix.
  ;;
  ;; **Structural walk.**  A positive-fact key linearizes nested compounds into arity
  ;; markers (see `vaelii.impl.sentex`), so a query token is one of three:
  ;;   * a variable — matches exactly one complete stored form.  If the child is an
  ;;     atom it advances one level; if the child is a marker it **skips** the whole
  ;;     subterm the marker's arity spans (`skip-one` / `skip-n`, recursing for nested
  ;;     arity).  This is what lets `(p ?y b)` bind a whole compound of unknown depth.
  ;;   * a marker `[::subterm k]` — matched exactly, like any token; the query's own
  ;;     next k linearized forms then match the subterm's elements.
  ;;   * anything else (an atom, or a whole list token in a `:false`/`:rule` key) —
  ;;     matched exactly by `count-at`.
  ;; Only child *sets* are read while walking; handles are read solely at the terminus,
  ;; so the skip can never cross into a leaf handle or read a marker as one.  This is a
  ;; superset filter — `res/unify` is the source of truth — so a markerless (flat)
  ;; key walks exactly as before.
  (lookup [_ pattern]
    (letfn [(child-labels [prefix] (kv-members backend (set-key prefix)))
            (skip-one [prefix]                         ; advance past one complete form
              (mapcat (fn [c]
                        (if (sx/subterm-mark? c)
                          (skip-n (conj prefix c) (sx/subterm-arity c))
                          [(conj prefix c)]))
                      (child-labels prefix)))
            (skip-n [prefix n]                         ; advance past n complete forms
              (if (zero? n)
                [prefix]
                (mapcat #(skip-n % (dec n)) (skip-one prefix))))]
      (loop [frontier [[]]                             ; node prefixes reached so far
             qs pattern]
        (if (empty? qs)
          (into #{} (mapcat (fn [prefix] (kv-members backend (leaf-key prefix)))) frontier)
          (let [q (first qs)
                frontier'
                (into []
                      (mapcat
                       (fn [prefix]
                         (if (sx/variable? q)
                           (skip-one prefix)
                           (when (pos? (count-at* backend (conj prefix q)))
                             [(conj prefix q)]))))
                      frontier)]
            (recur frontier' (rest qs)))))))

  (sentexes-in-context [_ context] (kv-members backend (ctx-key context)))
  (count-in-context    [_ context] (kv-count    backend (ctx-key context)))

  (sentexes-with-functor [_ pred] (kv-members backend (pred-key pred)))
  (count-with-functor    [_ pred] (kv-count    backend (pred-key pred)))

  (sentexes-with-arg [_ pos term] (kv-members backend (arg-key pos term)))
  (count-with-arg    [_ pos term] (kv-count    backend (arg-key pos term)))

  ;; Multi-column narrowing in one operation: intersect the functor root with every
  ;; named argument root, so knowing `(rel ?x B C)` narrows on [:functor-root rel], [:argument-root 2 B]
  ;; and [:argument-root 3 C] at once rather than fetching one column and filtering the rest per
  ;; record.  The result is a superset of the positional-trie hits (it does not
  ;; constrain numeric arguments or context — the roots do not index those), which the
  ;; caller's `unify` filters to the exact set.
  (sentexes-with-args [_ pred pos-terms]
    (let [ks (cond-> (mapv (fn [[pos term]] (arg-key pos term)) pos-terms)
               pred (conj (pred-key pred)))]
      (if (empty? ks) #{} (kv-intersect backend ks))))

  ;; Both predicate sets are complete — every rule is registered under all of its
  ;; antecedent predicates and its consequent predicate, whatever its direction — so
  ;; "what could conclude P?" is answerable for forward-only rules too.  Direction is
  ;; not indexed: it is a field on the rule's own sentex, which chaining reads.
  (index-rule [_ handle ante-preds conseq-pred]
    (kv-batch backend
              (cond-> (mapv (fn [p] [:add-to-set (rule-ante-key p) handle]) ante-preds)
                conseq-pred (conj [:add-to-set (rule-conseq-key conseq-pred) handle])))
    nil)

  (unindex-rule! [_ handle ante-preds conseq-pred]
    (kv-batch backend
              (cond-> (mapv (fn [p] [:remove-from-set (rule-ante-key p) handle]) ante-preds)
                conseq-pred (conj [:remove-from-set (rule-conseq-key conseq-pred) handle])))
    nil)

  (rules-by-antecedent [_ pred] (kv-members backend (rule-ante-key pred)))
  (rules-by-consequent [_ pred] (kv-members backend (rule-conseq-key pred)))

  ;; The exception re-check index.  A rule carrying an `exceptWhen` is posted under
  ;; every predicate its exception query mentions, so asserting or retracting a fact on
  ;; that predicate finds the rules whose exception it could have flipped; and into the
  ;; `:rules` roster, which a genl/genlContext edge change re-checks wholesale (a
  ;; closure can flip an exception with no matching fact ever arriving).  Granularity
  ;; is the rule, never the firing; nothing here records whether an exception *holds*.
  (index-exception [_ handle preds]
    (kv-batch backend
              (conj (mapv (fn [p] [:add-to-set (exception-pred-key p) handle]) preds)
                    ;; unconditional: a rule with an exception belongs in the roster
                    ;; whatever its exception mentions, or the taxonomy trigger misses it.
                    [:add-to-set (exception-rules-key) handle]))
    nil)

  (unindex-exception! [_ handle preds]
    (kv-batch backend
              (conj (mapv (fn [p] [:remove-from-set (exception-pred-key p) handle]) preds)
                    [:remove-from-set (exception-rules-key) handle]))
    nil)

  (rules-with-exception-on [_ pred] (kv-members backend (exception-pred-key pred)))
  (exception-rules [_] (kv-members backend (exception-rules-key)))
  ;; the roster *probe*, not the roster: `kv-member?` so a backend that packs the family
  ;; into int postings tests membership rather than materializing every rule that carries
  ;; an exception, once per candidate rule per new datum
  (exception-rule? [_ handle] (kv-member? backend (exception-rules-key) handle))

  (sentexes-with-term [_ term] (kv-members backend (term-key term)))
  (sentexes-with-terms [_ terms]
    (if (empty? terms) #{} (kv-intersect backend (mapv term-key terms))))

  ;; the roster reads: one set fetch and one size read, both O(distinct terms) at worst and
  ;; neither touching a record — the whole point of maintaining the roster.
  (terms      [_] (kv-members backend roster-key))
  (term-count [_] (kv-count    backend roster-key))

  ;; the flat-map index *is* the portable projection, so both directions are the
  ;; backend's own enumeration and install — no key is reshaped on the way through.
  (index-entries [_]         (kv-entries backend))
  (index-load    [_ entries] (kv-load    backend entries))

  (clear-index! [_] (kv-clear! backend) nil))

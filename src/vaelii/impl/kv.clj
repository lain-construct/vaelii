;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.kv
  "The key-value substrate the index rests on, and the one `IndexStore`
  implementation written over it.

  The index — the trie, the secondary roots, the rule indexes, the exception
  re-check index, and the inverted term index — is *all* sets and counters keyed
  by structured vectors.  `KvIndexStore` encodes that structure once, in terms of a
  small `KvBackend` protocol; a backend is then just an adapter that says how a
  scalar, a counter, and a set live in some store.  An in-memory map
  (`vaelii.impl.memory`) and an on-disk WAL (`vaelii.impl.disk.kv`) are two such
  adapters; a SQL or overlay backend is another.

  ## The count-aware trie

  A sentex is indexed by its trie path.  Every node, identified by its path
  prefix, is exactly three keys:

    count-key  [:trie :count prefix]  ->  integer: how many sentexes live at the leaves
                                     under this prefix (selectivity without walking).
    set-key    [:trie :children prefix]  ->  a SET: the next possible token labels (the
                                     node's child edges).
    leaf-key   [:trie :handles prefix]  ->  a SET: the handles of the sentexes whose path
                                     ends exactly here.

  **Child edges and leaf handles are separate keys because the trie is ragged.**
  Paths differ in length with arity, so one sentex's *full* path can be a proper
  prefix of another's: `(rel A B)` in `CxCee` keys as `[rel A B CxCee]`,
  and `(rel A B CxCee X)` in `CxDee` keys as `[rel A B CxCee X
  CxDee]` — the first path is an interior node of the second.  Storing both
  handles and child tokens in one set therefore mixed them, and a caller could not
  tell them apart by type (a handle is an integer, and so is the token `1970`).  Two
  keys make the distinction structural: `lookup` reads only the leaf key at its
  terminus, so it can never return a token as a handle, and `children` reads only
  the child set, so `plan`'s fan-out divisor can never count a handle as a branch.

  Alongside the trie sit ten smaller count tries whose last level is the context — the
  argument roots, the predicate extent, the two rule indexes, the rule extent, the
  opposed bodies, the self tuples, the taxonomy's supporters and the mint family's two
  (\"The count tries that end in the context\" below) — and three flat sets whose
  cardinality is their own size: the context root, the exception re-check index and the
  inverted term index.  One more flat set, the **term roster**
  `[:term-roster]`, holds the term index's *names* rather than handles, so the
  vocabulary can be listed and counted in O(terms) instead of a walk over every record.

  Contract: lookup expects a *full* path (sentence tokens + a context slot; the
  context may itself be a variable).  A short pattern terminates on an interior
  node, whose leaf key is empty, so it yields nothing rather than that node's child
  labels dressed up as handles.

  ## The `KvBackend`

  Logical keys are structured vectors and set members are bare values; a backend
  turns those into whatever its store wants (an in-memory map uses them directly; the
  on-disk backend nippy-frames them into its log).  The required ops are
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
  (:require [clojure.set :as set]
            [taoensso.trove :as trove]
            [vaelii.impl.profile :as prof]
            [vaelii.impl.protocols :as p
             :refer [kv-batch kv-clear! kv-count kv-entries kv-get
                     kv-intersect kv-load kv-member? kv-members unknown-op!]]
            [vaelii.impl.sentex :as sx]))

(def index-layout-version
  "Which key shapes this build's index is written in.

  The key families below — `[:trie :count|:children|:handles prefix]`, the context root,
  the five count tries ending in the context, the exception index, the term index and the
  rosters — *are*
  the index's portable form, so a dump of them is only readable by a build that agrees on
  them.  An index written in a layout this build does not use reads as **empty** rather
  than as wrong (a lookup finds no key and answers nothing), which is fail-safe and
  undiagnosable — so the layout is stated as a number and checked, rather than discovered
  by a KB that quietly stopped answering.

  **Bump it whenever a key shape changes**: a new family, a renamed tag, a different
  arity, or a different value type at an existing key.

  2 scopes the argument roots by predicate (`[:argument-root pred pos term]`) and adds
  the `[:argument-slot pos term]` roster that keeps the predicate-agnostic reads
  answerable.  3 adds the `[:unary-slot term]` roster beside it, which is what lets a
  membership question read a term's types without fetching every fact that names it.
  4 keys the argument roots as a count trie over `[pred pos term ctx]`: a node's
  `[:argument-root :count|:children [pred pos term]]` and the leaf
  `[:argument-root :handles [pred pos term ctx]]`.  5 replaces the functor root with the
  predicate extent, a count trie over `[pred ctx]`, and keys the two rule indexes as count
  tries over `[key ctx]` (`:rule-antecedent`, `:rule-consequent`).  6 adds the rule
  extent, a count trie over `[kind ctx]` (`:rule-extent`), and the antecedent trie's root
  level, `[:rule-antecedent-keys]`.  7 adds the bodies stored in both polarities: the
  count trie `:opposed` over `[body ctx]`, its root level `[:opposed-bodies]`, and the
  members by context, `[:opposed-in ctx]`.  8 adds the taxonomy's supporter families: a
  count trie over `[k ctx]` keyed by the key a declaration installs (`:tax-support`), and
  `[:tax-installs h]`.  9 adds the mint family: the `:mint` count trie over `[term ctx]`
  with its root level `[:mint-terms]`, and the `:mint-in` count trie over `[ctx]`.  10
  adds the shape roster, `[:shape-count f n]` and `[:shape-lengths f]`, `[:unary-multi]`,
  the terms the unary roster lists two or more predicates of, and the self-tuple count
  trie over `[pred ctx]` (`:self-tuple`)."
  10)

(defn apply-op
  "Apply one `kv-batch` write op to map `m`, returning `[m' reply]`.  Only
  `:increment`/`:decrement` carry a meaningful reply (the post-op counter value); the
  rest reply nil.  `:remove-from-set` drops the key when the set empties, so an absent
  key and an empty set are indistinguishable — a set with no members does not exist.

  **The op semantics live here, with the protocol that names them, and not in the
  backends.**  Both map-shaped backends fold their writes through this — the in-memory
  one (`vaelii.impl.memory`) over its state map, the on-disk one
  (`vaelii.impl.disk.kv`) over the RAM half of its write-ahead log, where it is also
  what *replays* the log, since a WAL frame there is the write op itself rather than
  the resulting value.  Written twice, the two copies could answer one op differently,
  and the disk side is replay: a seventh op added to the live path and missed in the
  fold would be a write that applies once and never comes back.

  An unrecognized op goes to `unknown-op!`, which every adapter shares: a bulk load
  taking the transient path, a dense backend's own batch, a fork decorator's, and an
  ordinary write taking this one may not disagree about what an unreadable op is.

  `:decrement` floors at zero, per the `KvBackend` contract: these counters are
  cardinalities.  The floor is in every fold rather than in one of them, because the WAL
  replays through this and the live write went through a backend — a floor applied on
  only one side would make a reopened store disagree with the one that wrote it."
  [m [op k a]]
  (case op
    :put  [(assoc m k a) nil]
    :delete  [(dissoc m k) nil]
    :increment (let [v (inc (long (get m k 0)))] [(assoc m k v) v])
    :decrement (let [v (max 0 (dec (long (get m k 0))))] [(assoc m k v) v])
    :add-to-set [(update m k (fnil conj #{}) a) nil]
    :remove-from-set (let [s (disj (get m k) a)]
                       [(if (empty? s) (dissoc m k) (assoc m k s)) nil])
    (unknown-op! op)))

;; ---- logical keys -------------------------------------------------------
;; Structured vectors — a backend encodes them (used directly as map keys in memory;
;; nippy-framed on disk).  The trie node's three keys share the [:trie …] prefix and
;; differ only in the :count/:children/:handles tag; the roots and indexes take
;; their own tags.

(defn- count-key [prefix] [:trie :count prefix])
(defn- set-key   [prefix] [:trie :children prefix])
;; leaf handles live under their own key, never mixed into the child-token set —
;; see the ragged-path note in the namespace docstring.
(defn- leaf-key  [prefix] [:trie :handles prefix])

;; exception re-check index — a predicate is a symbol and the roster key a keyword,
;; so `[:exception-index :rules]` can never collide with a predicate's own key.
(defn- exception-pred-key  [pred] [:exception-index pred])
(defn- exception-rules-key []     [:exception-index :rules])

;; the context root — the trie is ordered [pred args… ctx], so it narrows only
;; left-to-right: it cannot count "context C" (the deepest level) without fixing everything
;; to its left.  A flat set; cardinality is the set's own size.
(defn- ctx-key  [c]     [:context-root c])

;; ---- the count tries that end in the context -----------------------------
;; Ten families share one shape: a count trie whose last level is the context.  A
;; `node` is the path above the context, and each node is three keys under the family's
;; `tag` — its count (how many handles sit under it, in every context), its children (the
;; contexts that state one) and, per child, the leaf holding that context's handles:
;;
;;   :argument-root     node [pred pos term]   `pred`'s facts with `term` at 1-based `pos`
;;   :predicate-extent  node [pred]            `pred`'s facts, either polarity
;;   :rule-antecedent   node [key]             the rules with an antecedent on `key`
;;   :rule-consequent   node [key]             the rules whose consequent files under `key`
;;   :rule-extent       node [kind]            every rule (`:rule`), and the rules a solve
;;                                             reads (`:solve`)
;;   :opposed           node [body]            the facts of a body stored in both
;;                                             polarities, either polarity
;;   :self-tuple        node [pred]            `pred`'s ground positive binary self
;;                                             tuples `(pred a a)`
;;   :tax-support       node k                 the supporters of taxonomy key `k`, which
;;                                             the taxonomy writers post (below)
;;   :mint              node [term]            the mints about `term`
;;   :mint-in           node []                every mint
;;
;; So "what is stated under this node in the contexts a reader sees" reads the node's
;; children, intersected with the reader's ancestor set, and the leaves it keeps.  The
;; `:rule-antecedent` trie's root level, the keys some stored rule takes, is the one level
;; above a node any read asks for, and it is stored under its own key, `rule-keys-key`,
;; because its members are keys rather than contexts.  The `:opposed` trie's root level
;; is `opposed-bodies-key` for the same reason.

(defn- node-count-key [tag node]     [tag :count node])
(defn- node-ctxs-key  [tag node]     [tag :children node])
(defn- node-leaf-key  [tag node ctx] [tag :handles (conj node ctx)])
(def ^:private rule-keys-key [:rule-antecedent-keys])
(def ^:private opposed-bodies-key [:opposed-bodies])
(defn- opposed-in-key [ctx] [:opposed-in ctx])
(def ^:private mint-terms-key [:mint-terms])

;; ---- the argument family's keys ------------------------------------------
;; The argument roots are the `:argument-root` trie, and the family adds two rosters
;; beside it: the slot roster that keeps the predicate-AGNOSTIC reads answerable without
;; a second copy of the postings, and the unary slice of that roster a membership question
;; reads.  `arg-slots` below canonicalizes the term on the way in and `KvIndexStore`'s
;; argument reads canonicalize on the way out, so a term reaching a key here is already
;; `sx/canon`'d: a lazy seq and the `PersistentList` it is `=` to agree in any Clojure map
;; but freeze to different nippy bytes, so a key built from an uncanonicalized term misses
;; a durable backend's stored key and reports the fact absent
;; (`index_edge_test/the-argument-root-canonicalizes-a-compound-term` is the pin).

(defn- arg-count-key [node] (node-count-key :argument-root node))
(defn- arg-ctxs-key  [node] (node-ctxs-key :argument-root node))
(defn- arg-leaf-key  [node ctx] (node-leaf-key :argument-root node ctx))

(defn- slot-key
  "The slot roster key: the predicates present at `(pos, term)`.

  This keeps the predicate-AGNOSTIC reads answerable without a second copy of the
  postings — the coarse read is a union over a handful of scoped leaves rather than one
  wide bucket.  Its members are predicates, so it is vocabulary-scaled."
  [pos term]
  [:argument-slot pos term])

(defn- unary-slot-key
  "The unary slice of the slot roster: the predicates `term` is the LONE argument of.

  `kb/types-of` — the retrieval every definitional check bottoms out on — asks what types
  a term holds, and `slot-key` cannot answer it: `(T x)` and `(P x y)` both put `x` at
  position 1, share the roster entry and share the trie node below it, so the only way to
  tell them apart was to fetch every record at that node and read its arity.  A term at
  argument 1 of n binary facts therefore cost n record fetches per membership question,
  and every assert asks one.

  A deliberate **superset**: the entry is written by every unary fact rather than
  reference-counted on the first, so a predicate used at two arities with one term is
  listed here whichever arity arrived first.  Over-answering costs one posting read that
  the caller's arity filter drops; under-answering would lose a membership."
  [term]
  [:unary-slot term])

;; the key both index stores' non-trie writes carry, through `flat-family-adds` /
;; `flat-family-retires` below, so the two stores key the term index identically.
(defn term-key [term]  [:term-index (sx/canon term)])
;; the term roster — ONE set holding every name the term index is keyed by, so the
;; vocabulary is listable and countable without walking the records.  Its own key
;; family, because its members are terms rather than handles: a backend that packs the
;; handle families into int postings routes `[:term-roster]` to its ordinary set storage.
(def ^:private roster-key [:term-roster])

;; The terms the unary roster lists two or more predicates of, which the membership
;; family reads for the terms that can form a nogood.  Its members are terms.
(def ^:private unary-multi-key [:unary-multi])

;; The shape roster: per functor, the lengths its positive facts are stored at, kept by a
;; count per functor and length, so a length leaves with its last fact.  Its members are
;; numbers, so a backend that packs the handle families routes it to its ordinary storage.
(defn- shape-count-key   [f n] [:shape-count f n])
(defn- shape-lengths-key [f]   [:shape-lengths f])

(defn arg-slots
  "`[[pred pos term] ...]` - the argument-root nodes a fact enters, each term canonical.
  Empty for a rule and for a non-fact, matching `root-keys`.

  The canonicalization is here rather than in the key constructors so a term reaching a
  key or a backend read is canonical whichever of the three rosters it is going into."
  [sentex]
  (let [b (sx/body sentex)]
    (if (and (sequential? b) (seq b) (symbol? (first b)))
      (let [pred (first b)]
        (into [] (keep-indexed (fn [i a]
                                 (when (sx/indexable-term? a) [pred (inc i) (sx/canon a)])))
              (rest b)))
      [])))

(defn- self-tuple?
  "Is `sentex` a ground positive binary tuple `(p a a)` with a plain symbol functor?"
  [sentex]
  (let [s (:sentence sentex)]
    (boolean (and (nil? (:antecedent sentex)) (seq? s) (= 3 (count s))
                  (let [[f a b] s]
                    (and (symbol? f) (not= 'not f) (not (sx/variable? f)) (= a b)
                         (sx/ground-term? s)))))))

(defn- fact-nodes
  "`[[tag node] ...]` - the count-trie nodes a sentex enters.  A fact enters its predicate
  extent, then the argument-root node of each indexable top-level argument, and a ground
  positive binary self tuple its `:self-tuple` node.  A negative
  fact enters its positive body's nodes (polarity lives in the record), so
  `sentexes-with-functor` covers both polarities.  A rule enters the rule extent's
  `[:rule]` node, and its `[:solve]` node when a solve reads it (`:solve` among its
  `:engines`); its predicates live in the rule indexes.  Empty for a non-fact."
  [sentex]
  (if (some? (:antecedent sentex))
    (cond-> [[:rule-extent [:rule]]]
      (contains? (:engines sentex) :solve) (conj [:rule-extent [:solve]]))
    (let [b (sx/body sentex)]
      (if (and (sequential? b) (seq b) (symbol? (first b)))
        (cond-> (into [[:predicate-extent [(first b)]]]
                      (map (fn [node] [:argument-root node]))
                      (arg-slots sentex))
          (self-tuple? sentex) (conj [:self-tuple [(first b)]]))
        []))))

(defn root-keys
  "The handle postings a sentex enters outside the trie and the term index: its context
  root always, plus the leaf under each of its `fact-nodes` in its context."
  [sentex]
  (let [c (:context sentex)]
    (into [(ctx-key c)] (map (fn [[tag node]] (node-leaf-key tag node c))) (fact-nodes sentex))))

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

;; ---- the count tries' nodes, and the slot roster --------------------------
;; A fact enters one leaf per node through `root-keys`, and the node above that leaf
;; here: the context joins the node's children and the node's count goes up.  A
;; retraction reads the leaf and the children BEFORE the batch, so it decides from the
;; pre-write state whether the leaf empties (the context leaves the children) and whether
;; the node empties (its count key goes, which a map backend would otherwise keep as 0).
;; The rule indexes take the same two halves in `rule-adds` / `rule-retires`.
;;
;; The predicate-scoped argument roots answer `(P ?x B)` directly, but they cannot
;; answer the predicate-AGNOSTIC public reads (`sentexes-with-arg` / `count-with-arg`,
;; which `settle` uses for functional-predicate clash detection and the planner for
;; selectivity).  Rather than keep a second copy of every posting, the slot roster holds
;; the *predicates* present at a slot, so the coarse read is a union over a handful of
;; nodes.  A predicate enters when its node is created and leaves when its node empties.

(defn- unary-slot
  "`[pred term]` when `sentex` is a unary fact about an indexable term, else nil - the
  one entry it owes the unary roster, derived from the same positive body `arg-slots`
  reads so a negation is listed under the type it denies exactly as its argument root
  is."
  [sentex]
  (let [b (sx/body sentex)]
    (when (and (sequential? b) (= 2 (count b)) (symbol? (first b))
               (sx/indexable-term? (nth b 1)))
      [(first b) (sx/canon (nth b 1))])))

(defn- node-add
  "Write ops entering context `c` under the `tag` trie's `node`: the context joins the
  node's children and the count goes up.  They follow the leaf add in the batch, so a
  backend that answers a node's count from its leaves (`dense-roots`) replies with the
  count after the add."
  [tag node c]
  [[:add-to-set (node-ctxs-key tag node) c] [:increment (node-count-key tag node)]])

(defn- node-retire
  "`{:tag :node :dies? :ops}` - whether taking `handle` out of the `tag` trie's `node` in
  context `c` empties the node, and the write ops that keep its count and children right.
  Read BEFORE the leaf removal: the leaf empties when it is exactly `#{handle}`, and the
  node empties when that leaf is its only child."
  [backend tag node c handle]
  (let [leaf  (node-leaf-key tag node c)
        lone? (and (= 1 (long (kv-count backend leaf)))
                   (kv-member? backend leaf handle))
        dies? (and lone? (= 1 (long (kv-count backend (node-ctxs-key tag node)))))]
    {:tag   tag
     :node  node
     :dies? dies?
     :ops   (cond-> [(if dies?
                       [:delete (node-count-key tag node)]
                       [:decrement (node-count-key tag node)])]
              lone? (conj [:remove-from-set (node-ctxs-key tag node) c]))}))

(defn- node-adds
  "Write ops entering `sentex`'s context under each of its `fact-nodes`."
  [sentex]
  (let [c (:context sentex)]
    (into [] (mapcat (fn [[tag node]] (node-add tag node c))) (fact-nodes sentex))))

(defn- node-retires
  "`node-retire` for each of `sentex`'s `fact-nodes`."
  [backend sentex handle]
  (let [c (:context sentex)]
    (mapv (fn [[tag node]] (node-retire backend tag node c handle)) (fact-nodes sentex))))

(defn slot-adds
  "Write ops entering a sentex's predicates in their slots - read BEFORE the postings
  are written, so a predicate is entered exactly by the fact that creates its node.

  The unary roster is the exception and takes no read at all: its entry is written by
  every unary fact rather than by the first, because the node that guards the others is
  `[pred 1 term]`, which a *binary* fact of the same predicate about the same term also
  creates - so a reference count read off it would skip the unary entry whenever the
  binary fact arrived first, and a missing entry there loses a membership.  An
  `:add-to-set` of a member already present is a no-op inside the same batch.  A term
  joins `unary-multi-key` when the entry is its second predicate, which two reads of the
  unary roster decide."
  [backend sentex]
  (let [ops (into [] (comp (filter (fn [node] (zero? (long (kv-count backend (arg-ctxs-key node))))))
                           (map (fn [[pred pos t]] [:add-to-set (slot-key pos t) pred])))
                  (arg-slots sentex))]
    (if-let [[pred t] (unary-slot sentex)]
      (let [k (unary-slot-key t)]
        (cond-> (conj ops [:add-to-set k pred])
          (and (== 1 (long (kv-count backend k))) (not (kv-member? backend k pred)))
          (conj [:add-to-set unary-multi-key t])))
      ops)))

(defn- slot-retires
  "Write ops retiring the predicates whose argument-root node `retires` (from
  `node-retires`) says empties.

  A **unary** fact retires the unary entry with its position-1 slot, and a fact of any
  other arity leaves it alone: the extra op is owed by the sentexes that wrote one and by
  no others, so a KB of binary facts pays nothing for a roster it never enters.  The
  entry therefore outlives the last unary fact wherever a *binary* one of the same
  predicate is what empties the node — the ragged-arity case the naming invariant already
  refuses — and that is the superset `unary-slot-key` describes: a stale entry costs one
  posting read and the caller's arity filter drops it.  A term leaves `unary-multi-key`
  with the entry that leaves it one predicate, read off the unary roster's size."
  [backend sentex retires]
  (let [unary (unary-slot sentex)]
    (into [] (comp (filter #(and (:dies? %) (= :argument-root (:tag %))))
                   (mapcat (fn [{[pred pos t] :node}]
                             (cond-> [[:remove-from-set (slot-key pos t) pred]]
                               (and unary (= 1 pos))
                               (conj [:remove-from-set (unary-slot-key t) pred])

                               (and unary (= 1 pos)
                                    (== 2 (long (kv-count backend (unary-slot-key t))))
                                    (kv-member? backend (unary-slot-key t) pred))
                               (conj [:remove-from-set unary-multi-key t])))))
          retires)))

(defn- ->count
  "A trie counter as a long.  The `Long/parseLong` arm is for a backend that replies
  in bytes; both in-memory backends store a boxed `Long` (`memory.clj`, `dense_kv.clj`),
  and routing those through `(str)` and back allocated a String per counter read on the
  default index — once per ground pattern token per frontier node, so on the path of
  every `find-sentex-handle` and every `prefix-estimate` step of the planner."
  [reply]
  (cond
    (nil? reply)    0
    (number? reply) (long reply)
    :else           (Long/parseLong (str reply))))

(defn- fact-shape
  "`[f n]` for a positive fact of `n` arguments with a plain symbol functor, else nil."
  [sentex]
  (let [s (:sentence sentex)]
    (when (and (nil? (:antecedent sentex)) (seq? s) (<= 2 (count s)) (not (sx/negation? s)))
      (let [f (first s)]
        (when (and (symbol? f) (not (sx/variable? f)))
          [f (dec (count s))])))))

(defn- shape-adds
  "Write ops entering `sentex`'s shape in the shape roster: its length joins its
  functor's lengths, and the count of its shape goes up.  No read."
  [sentex]
  (when-let [[f n] (fact-shape sentex)]
    [[:add-to-set (shape-lengths-key f) n] [:increment (shape-count-key f n)]]))

(defn- shape-retires
  "Write ops taking `sentex`'s shape out of the shape roster, read before the write: the
  length leaves its functor's lengths with the last fact of the shape."
  [backend sentex]
  (when-let [[f n] (fact-shape sentex)]
    (if (<= (->count (kv-get backend (shape-count-key f n))) 1)
      [[:delete (shape-count-key f n)] [:remove-from-set (shape-lengths-key f) n]]
      [[:decrement (shape-count-key f n)]])))

;; ---- the bodies stored in both polarities -----------------------------------
;; A body B is **opposed** while a `(not B)` and a `B` are both stored, in any contexts,
;; and its **members** are the handles of both polarities.  Three keys hold the family:
;; the body joins `opposed-bodies-key`, each member enters B's `:opposed` node under its
;; context, and each member enters `[:opposed-in ctx]`, the members stated in `ctx` of
;; every opposed body.  The last is a context-first leaf beside the context-last trie: a
;; `genlCx` edge's placement pass reads the members stated in the contexts the edge
;; newly exposes, and keyed context last that read would visit every opposed body.
;;
;; The writes read the trie before the write (`trie`, `{:count f :leaves f}`): a body
;; joins on the first record of its second polarity, which enters the other polarity's
;; records with it, and leaves on the last record of either polarity, which takes every
;; member out.  A `[:false B]` prefix is exact, because the body is one token there; a
;; positive prefix `(sx/key-stream B)` also counts a longer sentence that extends it, so
;; the positive side is read as the leaves one level below it, and its count as the
;; node's count less the denials.

(defn- opposed-side
  "`[B denial?]` for a fact whose body `B` is a compound, else nil."
  [sentex]
  (when (nil? (:antecedent sentex))
    (let [s (:sentence sentex)]
      (when (seq? s)
        (let [neg? (sx/negation? s)
              b    (if neg? (second s) s)]
          (when (and (seq? b) (seq b)) [b neg?]))))))

(defn- member-adds
  "Write ops entering `handle`, stated in `c`, as a member of the opposed body `b`."
  [b c handle]
  (into [[:add-to-set (node-leaf-key :opposed [b] c) handle]
         [:add-to-set (opposed-in-key c) handle]]
        (node-add :opposed [b] c)))

(defn- opposed-adds
  "Write ops the fact `sentex`, stored under `handle`, owes the opposed family, read
  before the write.  A positive fact reads one trie count, the `[:false B]` count, and
  nothing more when it is 0."
  [backend trie sentex handle]
  (when-let [[b neg?] (opposed-side sentex)]
    (let [c      (:context sentex)
          denied (long ((:count trie) [:false b]))
          join   (fn [others]
                   (into [[:add-to-set opposed-bodies-key b]]
                         (mapcat (fn [[c' hs]] (mapcat #(member-adds b c' %) hs)))
                         (cons [c [handle]] others)))]
      (cond
        (pos? denied) (cond (kv-member? backend opposed-bodies-key b) (member-adds b c handle)
                            ;; a body with denials that is not opposed stores no
                            ;; positive, so this fact is its first
                            (not neg?) (join ((:leaves trie) [:false b])))
        neg?          (let [pre (vec (sx/key-stream b))]
                        (when (pos? (long ((:count trie) pre)))
                          (when-let [pos (seq ((:leaves trie) pre))]
                            (join pos))))))))

(defn- opposed-retires
  "Write ops taking the fact `sentex`, stored under `handle`, out of the opposed family,
  read before the write: its own postings, or every member's when it is the last record
  of its polarity.  One membership read for a body that is not opposed."
  [backend trie sentex handle]
  (when-let [[b neg?] (opposed-side sentex)]
    (when (kv-member? backend opposed-bodies-key b)
      (let [c      (:context sentex)
            denied (long ((:count trie) [:false b]))
            all    (->count (kv-get backend (node-count-key :opposed [b])))]
        (if (== 1 (if neg? denied (- all denied)))
          (-> [[:remove-from-set opposed-bodies-key b] [:delete (node-count-key :opposed [b])]]
              (into (mapcat (fn [c']
                              (into [[:remove-from-set (node-ctxs-key :opposed [b]) c']]
                                    (mapcat (fn [h] [[:remove-from-set (node-leaf-key :opposed [b] c') h]
                                                     [:remove-from-set (opposed-in-key c') h]]))
                                    (kv-members backend (node-leaf-key :opposed [b] c')))))
                    (kv-members backend (node-ctxs-key :opposed [b]))))
          (into [[:remove-from-set (node-leaf-key :opposed [b] c) handle]
                 [:remove-from-set (opposed-in-key c) handle]]
                (:ops (node-retire backend :opposed [b] c handle))))))))

(defn trie-reads
  "The two trie reads the opposed family's writes take, over `count-at` (prefix ->
  count) and `children` and `leaf` (prefix -> set): `:count`, and `:leaves`, the
  `[child handles]` of each child of a prefix whose leaf one level below holds a handle."
  [count-at children leaf]
  {:count  count-at
   :leaves (fn [prefix]
             (into [] (keep (fn [ch] (let [hs (leaf (conj prefix ch))] (when (seq hs) [ch hs]))))
                   (children prefix)))})

;; ---- the non-trie write path ---------------------------------------------
;; `KvIndexStore` and `ColumnarIndexStore` store the trie differently and store
;; everything under it identically: the inverted term index, the context root, the
;; predicate extent, the argument trie, the term roster and the argument-slot roster are
;; `key -> set` and `key -> count` families over one backend.  The two builders below
;; produce that half of a write — the ops and the per-family counts together — and each
;; store concatenates its own trie ops around the ops and hands the counts to the profile
;; tally with its own `:levels` (and `:dead` on the retire).  One definition fixes three things across the
;; two stores: which families a sentex enters, the order its ops land in, and the numbers
;; the tally reports.  The order belongs to the definition because `assert_cost_test` pins
;; the per-family read/write counts one assert costs, on either store.  `:roots` counts
;; the root postings, the count-trie nodes' ops and the opposed family's ops together.
;; `trie` is the store's own trie reads (`trie-reads`), which only the opposed family
;; takes.

(defn flat-family-adds
  "`{:ops [...] :counts {:terms n :roots n :roster n :slots n}}` — the non-trie write ops
  entering `sentex` under `handle`, and the number of ops each family takes.

  Both roster reads run here, before the caller batches the ops, so a name enters the
  term roster and a predicate enters its argument slot exactly on the first sentex to
  carry it."
  [backend trie sentex handle]
  (let [terms   (sentex-terms sentex)
        roots   (root-keys sentex)                      ; derived from the sentex alone
        nodes   (node-adds sentex)                      ; likewise
        roster  (roster-adds backend terms)             ; reads the pre-write postings
        slots   (into (slot-adds backend sentex) (shape-adds sentex)) ; likewise
        opposed (opposed-adds backend trie sentex handle)] ; likewise, and the trie
    {:ops    (-> []
                 (into (map (fn [t] [:add-to-set (term-key t) handle])) terms)
                 (into (map (fn [k] [:add-to-set k handle])) roots)
                 (into nodes)
                 (into opposed)
                 (into roster)
                 (into slots))
     :counts {:terms  (count terms)
              :roots  (+ (count roots) (count nodes) (count opposed))
              :roster (count roster)
              :slots  (count slots)}}))

(defn flat-family-retires
  "`{:ops [...] :counts {:terms n :roots n :roster n :slots n}}` — the mirror of
  `flat-family-adds`: the ops taking `handle` out of those same families, and the
  number of ops each family takes.

  Every read runs here, before the caller batches the ops, so a name leaves the term
  roster, a predicate leaves its argument slot and a node leaves the argument trie
  exactly on the last sentex to carry it."
  [backend trie sentex handle]
  (let [terms   (sentex-terms sentex)
        roots   (root-keys sentex)                      ; derived from the sentex alone
        retires (node-retires backend sentex handle)    ; reads the pre-write postings
        nodes   (into [] (mapcat :ops) retires)
        opposed (opposed-retires backend trie sentex handle) ; likewise, and the trie
        roster  (roster-retires backend terms handle)   ; likewise
        slots   (into (slot-retires backend sentex retires) (shape-retires backend sentex))]
    {:ops    (concat (map (fn [t] [:remove-from-set (term-key t) handle]) terms)
                     (map (fn [k] [:remove-from-set k handle]) roots)
                     nodes opposed roster slots)
     :counts {:terms  (count terms)
              :roots  (+ (count roots) (count nodes) (count opposed))
              :roster (count roster)
              :slots  (count slots)}}))

;; ---- reading the family --------------------------------------------------

(defn- count-at* [backend prefix] (->count (kv-get backend (count-key prefix))))

(defn- kv-trie
  "`trie-reads` over the trie `backend` holds, untallied."
  [backend]
  (trie-reads #(count-at* backend %) #(kv-members backend (set-key %))
              #(kv-members backend (leaf-key %))))

(defn- seen-ctxs
  "The children of the `tag` trie's `node` a reader with ancestor set `ctxs` sees, or
  every child when `ctxs` is nil.  The intersection iterates the smaller side: the node's
  children filtered by membership in `ctxs`, or `ctxs` probed against the children with
  `kv-member?`, so it costs min(|children|, |ctxs|) probes."
  [backend tag node ctxs]
  (let [k (node-ctxs-key tag node)]
    (cond
      (nil? ctxs) (kv-members backend k)
      (<= (long (kv-count backend k)) (count ctxs))
      (filterv #(contains? ctxs %) (kv-members backend k))
      :else (filterv #(kv-member? backend k %) ctxs))))

(defn- node-handles
  "The handles under the `tag` trie's `node` in the contexts `seen-ctxs` returns.  One
  context hands its leaf back as stored."
  [backend tag node ctxs]
  (let [cs (seen-ctxs backend tag node ctxs)]
    (case (count cs)
      0 #{}
      1 (kv-members backend (node-leaf-key tag node (first cs)))
      (reduce (fn [acc c] (into acc (kv-members backend (node-leaf-key tag node c)))) #{} cs))))

(defn- nodes-intersect
  "The handles under every one of `nodes` (two or more, one predicate), per context: the
  contexts all of them state and the reader sees, then one `kv-intersect` of the leaves
  in each."
  [backend nodes ctxs]
  (let [common (reduce (fn [cs node]
                         (let [k (arg-ctxs-key node)]
                           (filterv #(kv-member? backend k %) cs)))
                       (vec (seen-ctxs backend :argument-root (first nodes) ctxs))
                       (rest nodes))
        leaves (fn [c] (kv-intersect backend (mapv #(arg-leaf-key % c) nodes)))]
    (case (count common)
      0 #{}
      1 (leaves (nth common 0))
      (reduce (fn [acc c] (into acc (leaves c))) #{} common))))

(defn- roster-union
  "The union of `preds`' nodes at `(pos, term)`, in the contexts `ctxs` (every context
  when nil).  A roster holds ONE predicate in the common case — a term occupies a given
  position under one predicate — and that node's handles are handed straight back."
  [backend preds pos term ctxs]
  (case (count preds)
    0 #{}
    1 (node-handles backend :argument-root [(first preds) pos term] ctxs)
    (reduce (fn [acc pd] (into acc (node-handles backend :argument-root [pd pos term] ctxs)))
            #{} preds)))

(defn- roster-tally
  "The cardinality of that union over every context, as a sum of the nodes' own counts —
  a disjoint sum, since a handle is one sentex with one functor and so sits under exactly
  one predicate at a fixed `(pos, term)`."
  [backend preds pos term]
  (reduce (fn [n pd] (+ (long n) (->count (kv-get backend (arg-count-key [pd pos term])))))
          0 preds))

;; ---- the rule indexes' writes ---------------------------------------------
;; A rule enters the `:rule-antecedent` trie once per distinct antecedent key and the
;; `:rule-consequent` trie under its consequent key, each in its own context, so a node's
;; count is how many rules take the key.  Each node is written only where its leaf does
;; not already hold the handle, and retired only where it does, so registering a rule
;; twice or deregistering it twice leaves every count right.  An antecedent key joins
;; `rule-keys-key` with the node it creates and leaves it with the node that empties.

(defn- rule-nodes
  "`[[tag node] ...]` - the rule-index nodes of a rule with antecedent keys `ante-keys`
  and consequent key `conseq-key` (nil when it has none)."
  [ante-keys conseq-key]
  (cond-> (into [] (comp (distinct) (map (fn [k] [:rule-antecedent [k]]))) ante-keys)
    (some? conseq-key) (conj [:rule-consequent [conseq-key]])))

(defn- rule-adds
  "Write ops registering `handle`, stated in `c`, under each of its rule-index nodes it is
  not already under."
  [backend handle ante-keys conseq-key c]
  (into [] (comp (remove (fn [[tag node]] (kv-member? backend (node-leaf-key tag node c) handle)))
                 (mapcat (fn [[tag node]]
                           (cond-> (into [[:add-to-set (node-leaf-key tag node c) handle]]
                                         (node-add tag node c))
                             (and (= :rule-antecedent tag)
                                  (zero? (long (kv-count backend (node-ctxs-key tag node)))))
                             (conj [:add-to-set rule-keys-key (first node)])))))
        (rule-nodes ante-keys conseq-key)))

(defn- rule-retires
  "Write ops deregistering `handle`, stated in `c`, from each of its rule-index nodes it
  is under.  The node reads run before the batch (`node-retire`)."
  [backend handle ante-keys conseq-key c]
  (into [] (comp (filter (fn [[tag node]] (kv-member? backend (node-leaf-key tag node c) handle)))
                 (mapcat (fn [[tag node]]
                           (let [{:keys [dies? ops]} (node-retire backend tag node c handle)]
                             (cond-> (into [[:remove-from-set (node-leaf-key tag node c) handle]] ops)
                               (and dies? (= :rule-antecedent tag))
                               (conj [:remove-from-set rule-keys-key (first node)]))))))
        (rule-nodes ante-keys conseq-key)))

;; ---- the mint family's writes ---------------------------------------------
;; A mint is a record a stored argument-declaration justification concludes, filed under
;; its term and its context (`special/post-mint!` says which records).  The family is
;; posted from the justification rather than from the sentence: a minted `(person A)` and
;; an authored `(person A)` in one context are one sentex, so no key over the sentence
;; tells them apart.  Two count tries hold it, written in one batch: `:mint` over `[term
;; ctx]`, whose root level is `mint-terms-key`, and `:mint-in` over `[ctx]`, whose node
;; `[]` counts every mint.  A handle is posted only where its `:mint` leaf does not hold it
;; and retired only where it does, so a record several mint justifications conclude is
;; filed once.

(defn- mint-adds
  "Write ops filing `h` under `term` in context `c`, or nil when it is filed there."
  [backend term c h]
  (when-not (kv-member? backend (node-leaf-key :mint [term] c) h)
    (cond-> (-> [[:add-to-set (node-leaf-key :mint [term] c) h]]
                (into (node-add :mint [term] c))
                (conj [:add-to-set (node-leaf-key :mint-in [] c) h])
                (into (node-add :mint-in [] c)))
      (zero? (long (kv-count backend (node-ctxs-key :mint [term]))))
      (conj [:add-to-set mint-terms-key term]))))

(defn- mint-retires
  "Write ops taking `h` out from under `term` in context `c`, or nil when it is not filed
  there.  The node reads run before the batch (`node-retire`)."
  [backend term c h]
  (when (kv-member? backend (node-leaf-key :mint [term] c) h)
    (let [by-term (node-retire backend :mint [term] c h)
          by-ctx  (node-retire backend :mint-in [] c h)]
      (cond-> (-> [[:remove-from-set (node-leaf-key :mint [term] c) h]]
                  (into (:ops by-term))
                  (conj [:remove-from-set (node-leaf-key :mint-in [] c) h])
                  (into (:ops by-ctx)))
        (:dies? by-term) (conj [:remove-from-set mint-terms-key term])))))

(def sealed-prefix
  "The count prefix of the batch-seal counter: incremented as the **last** op of every
  `index-sentex` batch and decremented as the last op of an unindex's cleanup batch,
  so it equals the indexed-sentex count exactly when every batch landed whole.  The
  durable open's coverage gate compares it against the record count: the WAL logs one
  frame per op, so a torn tail keeps a batch's *prefix* — the root counter `count-at
  []` reads is op 0 and survives every tear, which is what makes it the wrong
  instrument — while this counter is the op a tear loses first.  A namespaced keyword,
  so it collides with no term path; only the count key is written, so no trie walk
  ever meets it.  Zero on a store whose index arrived by `index-load` replay or was
  written before the counter existed — the gate falls back to the root count there."
  [::sealed])

(defn- unindex-present!
  "Take `handle`, stored at the trie leaf of `pth` (`sx/path sentex`), out of every
  index family — the caller has established it is there (`unindex-sentex!`).  Two
  batches instead of a round trip per trie level: one to drop the leaf handle and
  decrement every level's counter, whose replies decide which nodes died; one to delete
  the dead nodes' keys, detach them from their parents, and clean the term index and
  roots."
  [backend sentex pth handle]
  (let [n        (count pth)
        flat     (flat-family-retires backend (kv-trie backend) sentex handle) ; reads the pre-write postings
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
               (:ops flat)
               ;; the batch seal, last on purpose — `sealed-prefix` says why
               [[:decrement (count-key sealed-prefix)]]))
    ;; the mirror of the assert tally in `index-sentex`, and the reason it is a separate
    ;; one: `dead` is the only quantity here the sentex does not decide.  Every other
    ;; number is a property of what is being retracted; how many trie nodes empty
    ;; is a property of what is left behind it (`vaelii.impl.profile`).
    (when (prof/profiling?)
      (prof/record-index-retract sentex (assoc (:counts flat)
                                               :levels (inc n)
                                               :dead   (count dead))))
    handle))

(defrecord KvIndexStore [backend]
  p/IndexStore
  ;; One batch, not three round trips: the trie levels, the inverted term index, and
  ;; the secondary roots land together.  On the in-memory backends the batch applies
  ;; in one swap, so a reader never sees a sentex half-indexed.  Durability is
  ;; another matter: the disk WAL logs one frame per op, all in one write
  ;; (`disk/kv.clj`, `apply-ops!`), so a crash that tears that write persists a
  ;; *prefix* — e.g. an argument-root posting whose predicate never entered the slot
  ;; roster, which under-answers the predicate-agnostic reads while the trie and the
  ;; scoped reads see the fact.  The
  ;; record/index boundary remains; `vaelii.impl.reindex` is the repair for both.
  (index-sentex [_ sentex handle]
    (let [pth  (sx/path sentex)
          n    (count pth)
          flat (flat-family-adds backend (kv-trie backend) sentex handle)] ; reads the pre-write postings
      (kv-batch backend
                (-> (reduce (fn [ops i]
                              (let [prefix (subvec pth 0 i)]
                                (-> ops
                                    (conj! [:increment (count-key prefix)])
                                    (conj! (if (< i n)
                                             [:add-to-set (set-key prefix)  (nth pth i)] ; child edge
                                             [:add-to-set (leaf-key prefix) handle])))))  ; leaf handle
                            (transient []) (range (inc n)))
                    (as-> ops (reduce conj! ops (:ops flat)))
                    ;; the batch seal, last on purpose — `sealed-prefix` says why
                    (conj! [:increment (count-key sealed-prefix)])
                    persistent!))
      ;; what this assert cost the index, per family, when somebody is asking
      ;; (`vaelii.impl.profile`).  The trie depth is this store's own number; the four
      ;; family counts come back with the ops that produced them, so the tally cannot
      ;; disagree with `ColumnarIndexStore`'s.
      (when (prof/profiling?)
        (prof/record-index-write sentex (assoc (:counts flat) :levels (inc n))))
      handle))

  ;; **Gated on the handle being at the leaf.**  The counters are decremented without
  ;; looking, and a node whose count reaches zero is deleted with every handle at its
  ;; leaf — so one stray unindex (a handle never indexed here, or indexed and already
  ;; removed) would take live nodes, and the sentexes stored under them, out of the
  ;; trie.  One membership probe on the leaf — a hash lookup on every backend, no
  ;; protocol read tallied — makes a stray unindex a no-op instead.
  ;;
  ;; **And says so**, because the no-op is safe and not therefore right.  The caller is
  ;; `integrate/sentex-removed!`, which deletes the record on the next line whether or
  ;; not anything came out of the index: a genuine record/index divergence therefore
  ;; leaves the trie handing out a handle whose record is gone, which shows up as a
  ;; corrupted store several operations later and nowhere near here.  Silence made that
  ;; indistinguishable from a caller retracting a handle twice.  `reindex` is the repair,
  ;; and the log is what tells somebody to run it.
  (unindex-sentex! [_ sentex handle]
    (let [pth (sx/path sentex)]
      (if (kv-member? backend (leaf-key pth) handle)
        (unindex-present! backend sentex pth handle)
        (trove/log! {:level :warn :id ::unindex-absent
                     :data {:handle handle :path pth :context (:context sentex)}})))
    handle)

  ;; Every read below tallies the **family** that answered it (`vaelii.impl.profile`),
  ;; one entry per protocol call: a deref and a `nil?` check when nobody is asking, and
  ;; the one measurement that says whether a family a KB pays to maintain is ever read.
  ;; What a call *cost* is a separate question — the trie's is the fan tally in `lookup`.
  ;;
  ;; The trie is two families to a reader even though it is one structure on disk, and
  ;; the split is the whole reason the tally is worth reading: these three are the
  ;; **cost model's** probes (`plan`'s selectivity and fan-out divisor), and `lookup`
  ;; below is **retrieval**.  A run that reads the counts a hundred times per walk is
  ;; using the trie to plan, not to fetch, and a family roster that added them together
  ;; would report that as one number meaning neither.
  (count-at [_ prefix] (prof/record-read :trie-counts) (count-at* backend prefix))

  (children [_ prefix] (prof/record-read :trie-counts) (vec (kv-members backend (set-key prefix))))
  ;; the set's cardinality, which every backend answers without building the set —
  ;; `children` above would materialize it into a vector for the same number
  (count-children [_ prefix] (prof/record-read :trie-counts) (kv-count backend (set-key prefix)))

  ;; The terminus reads the *leaf* key, so an under-long pattern — which stops on an
  ;; interior node — yields nothing instead of that node's child tokens, and a full
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
  ;; superset filter — `res/unify` is the source of truth — and a markerless (flat)
  ;; key, holding no marker for the skip to read, walks one level per token.
  ;;
  ;; With a `ctxs` set the last token, the context level, keeps only the children in
  ;; `ctxs` (`seen-ctxs`, the argument roots' by-context read), so the walk reads no leaf
  ;; stated where the reader cannot see.  A context is an atom, so no marker is in `ctxs`.
  (lookup [this pattern] (p/lookup this pattern nil))
  (lookup [_ pattern ctxs]
    (prof/record-read :trie-lookup)
    ;; Eager vectors throughout: a lazy `mapcat` per level is a seq and a lock per child
    ;; token, on the walk every join's partially bound literal takes.
    (letfn [(child-tokens [prefix] (kv-members backend (set-key prefix)))
            (skip-one [prefix]                         ; advance past one complete form
              (reduce (fn [acc c]
                        (if (sx/subterm-mark? c)
                          (into acc (skip-n (conj prefix c) (sx/subterm-arity c)))
                          (conj acc (conj prefix c))))
                      []
                      (child-tokens prefix)))
            (skip-n [prefix n]                         ; advance past n complete forms
              (if (zero? n)
                [prefix]
                (reduce (fn [acc p] (into acc (skip-n p (dec n)))) [] (skip-one prefix))))]
      ;; `visits` and `widest` describe the walk itself: one probe per frontier node per
      ;; level, and how wide the frontier ever got.  A narrowing walk holds the frontier
      ;; at one node and visits one per level; a walk that got stuck behind a variable
      ;; visits that level's whole child set, which is the fan the secondary roots exist
      ;; to avoid.  Two long ops per level whether or not anybody is counting; the tally
      ;; itself is a deref when the instrument is off.
      (loop [frontier [[]]                             ; node prefixes reached so far
             qs pattern
             visits 0
             widest 1]
        (if (empty? qs)
          ;; one node reached — the walk that narrowed all the way — answers its leaf set
          ;; as stored rather than copied into a new one
          (let [hs (if (== 1 (count frontier))
                     (set (kv-members backend (leaf-key (nth frontier 0))))
                     (into #{} (mapcat (fn [prefix] (kv-members backend (leaf-key prefix)))) frontier))]
            (prof/record-fan pattern (+ visits (count frontier)) widest (count hs))
            hs)
          (let [q (first qs)
                ctx-level? (and ctxs (nil? (next qs)))
                frontier'
                (into []
                      (mapcat
                       (fn [prefix]
                         (cond
                           (and ctx-level? (sx/variable? q))
                           (mapv #(conj prefix %) (seen-ctxs backend :trie prefix ctxs))
                           (sx/variable? q) (skip-one prefix)
                           (and ctx-level? (not (contains? ctxs q))) nil
                           (pos? (count-at* backend (conj prefix q))) [(conj prefix q)])))
                      frontier)]
            (recur frontier' (rest qs)
                   (+ visits (count frontier))
                   (max widest (count frontier'))))))))

  ;; The exact leaf — one hash read of the node the path names, no walk and no fan.
  ;; Tallied as retrieval like `lookup` beside it, because that is what it is; it records
  ;; no fan, having none to record.
  (leaf-at [_ path] (prof/record-read :trie-lookup) (kv-members backend (leaf-key (vec path))))

  (sentexes-in-context [_ context] (prof/record-read :context-root) (kv-members backend (ctx-key context)))
  (count-in-context    [_ context] (prof/record-read :context-root) (kv-count    backend (ctx-key context)))

  ;; The predicate extent: every context's leaf, or the one leaf a predicate stated in one
  ;; context has, handed back as stored.  The count is the node's own.
  (sentexes-with-functor [_ pred]
    (prof/record-read :predicate-extent)
    (node-handles backend :predicate-extent [pred] nil))
  (count-with-functor    [_ pred]
    (prof/record-read :predicate-extent)
    (->count (kv-get backend (node-count-key :predicate-extent [pred]))))

  ;; Predicate-agnostic reads, answered as a union over the slot roster's predicates.
  ;; One node in the overwhelmingly common case (a term occupies a given position under
  ;; one predicate); a handful otherwise.  A node stated in one context hands its leaf
  ;; back as stored, so on the two set-backed backends that read is allocation-free.
  ;; `sx/canon` is the read boundary's half of what `arg-slots` does on the write side:
  ;; the term a backend's argument read receives is canonical, so a compound arriving as a
  ;; lazy seq keys identically to the `PersistentList` that was stored.  Once here rather
  ;; than inside each key constructor, since a single agnostic read builds one key per
  ;; predicate in the slot roster.
  (sentexes-with-arg [_ pos term]
    (prof/record-read :argument-slot)
    (prof/record-read :argument-root)
    (let [term (sx/canon term)]
      (roster-union backend (kv-members backend (slot-key pos term)) pos term nil)))
  (count-with-arg   [_ pos term]
    (prof/record-read :argument-slot)
    (prof/record-read :argument-root)
    (let [term (sx/canon term)]
      (roster-tally backend (kv-members backend (slot-key pos term)) pos term)))

  ;; Multi-column narrowing. With the argument roots scoped by predicate, a named
  ;; functor needs NO predicate-extent intersection: `(rel ?x B C)` reads the nodes
  ;; `[rel 2 B]` and `[rel 3 C]`, a single bound argument is one node, and no bound
  ;; argument is the predicate extent's node `[rel]`.  With `ctxs`, each node's contexts
  ;; are intersected with the reader's ancestor set before a leaf is read, so no handle
  ;; stored where the reader cannot see is returned.  A `nil` pred
  ;; (a variable functor) has no scope to read, so it unions the slot roster's nodes per
  ;; column and intersects the columns.  The result stays a superset of the
  ;; positional-trie hits — it does not constrain numeric arguments — which the caller's
  ;; `unify` filters exact.
  (sentexes-with-args [this pred pos-terms] (p/sentexes-with-args this pred pos-terms nil))
  (sentexes-with-args [_ pred pos-terms ctxs]
    (cond
      (nil? pred)
      (if (empty? pos-terms)
        #{}
        (reduce (fn [acc [pos term]]
                  (prof/record-read :argument-slot)
                  (prof/record-read :argument-root)
                  (let [term (sx/canon term)
                        s    (roster-union backend (kv-members backend (slot-key pos term))
                                           pos term ctxs)]
                    (if (nil? acc) s (set/intersection acc s))))
                nil pos-terms))
      (empty? pos-terms) (do (prof/record-read :predicate-extent)
                             (node-handles backend :predicate-extent [pred] ctxs))
      :else
      (do (prof/record-read :argument-root)
          (let [nodes (mapv (fn [[pos term]] [pred pos (sx/canon term)]) pos-terms)]
            (if (nil? (next nodes))
              (node-handles backend :argument-root (nth nodes 0) ctxs)
              (nodes-intersect backend nodes ctxs))))))

  ;; Both key sets are complete — every rule is registered under all of its antecedent
  ;; keys and its consequent key, whatever its direction — so "what could conclude P?"
  ;; is answerable for forward-only rules too.  Direction is not indexed: it is a field
  ;; on the rule's own sentex, which chaining reads.  Each index is a count trie ending
  ;; in the rule's context, so a read with `ctxs` reads only the contexts a reader sees.
  (index-rule [_ handle ante-preds conseq-pred context]
    (kv-batch backend (rule-adds backend handle ante-preds conseq-pred context))
    nil)

  (unindex-rule! [_ handle ante-preds conseq-pred context]
    (kv-batch backend (rule-retires backend handle ante-preds conseq-pred context))
    nil)

  (rules-by-antecedent [_ pred] (prof/record-read :rule-index)
    (node-handles backend :rule-antecedent [pred] nil))
  (rules-by-consequent [_ pred] (prof/record-read :rule-index)
    (node-handles backend :rule-consequent [pred] nil))
  (rules-by-consequent [_ pred ctxs] (prof/record-read :rule-index)
    (node-handles backend :rule-consequent [pred] ctxs))

  ;; The exception re-check index.  A rule carrying an `exceptWhen` is posted under
  ;; every predicate its exception query mentions, so asserting or retracting a fact on
  ;; that predicate finds the rules whose exception it could have flipped; and into the
  ;; `:rules` roster, which a genl/genlCx edge change re-checks wholesale (a
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

  (rules-with-exception-on [_ pred] (prof/record-read :exception-index)
    (kv-members backend (exception-pred-key pred)))
  (exception-rules [_] (prof/record-read :exception-index) (kv-members backend (exception-rules-key)))
  ;; the roster *probe*, not the roster: `kv-member?` so a backend that packs the family
  ;; into int postings tests membership rather than materializing every rule that carries
  ;; an exception, once per candidate rule per new datum
  (exception-rule? [_ handle] (prof/record-read :exception-index)
    (kv-member? backend (exception-rules-key) handle))

  (sentexes-with-term [_ term] (prof/record-read :term-index) (kv-members backend (term-key term)))
  (sentexes-with-terms [_ terms]
    (prof/record-read :term-index)
    (if (empty? terms) #{} (kv-intersect backend (mapv term-key terms))))

  ;; the roster reads: one set fetch and one size read, both O(distinct terms) at worst and
  ;; neither touching a record — the whole point of maintaining the roster.
  (terms      [_] (prof/record-read :term-roster) (kv-members backend roster-key))
  (term-count [_] (prof/record-read :term-roster) (kv-count    backend roster-key))

  ;; the flat-map index *is* the portable projection, so both directions are the
  ;; backend's own enumeration and install — no key is reshaped on the way through.
  ;; minus the batch-seal counter: it describes the WAL's own health, not the
  ;; records, so it is no part of the portable projection — a dump carries it to no
  ;; store that can read it as anything, and the cross-backend parity of this seq is
  ;; what `index-dump-test` pins
  (index-entries [_]         (remove (fn [[k _]] (= k (count-key sealed-prefix)))
                                     (kv-entries backend)))
  (index-load    [_ entries] (kv-load    backend entries))

  (clear-index! [_] (kv-clear! backend) nil)

  ;; The unary slice, read off its own roster and otherwise the same shape as the two
  ;; predicate-agnostic reads above — one roster read, then the predicate-scoped
  ;; postings, tallied as the same two families because it is the same two key shapes.
  ;; The roster is a superset (`unary-slot-key` says why), so this is too, and
  ;; `kb/types-of` filters it exact on the records it was going to read anyway.
  (unary-sentexes-with-arg [_ term]
    (prof/record-read :argument-slot)
    (prof/record-read :argument-root)
    (let [term (sx/canon term)]
      (roster-union backend (kv-members backend (unary-slot-key term)) 1 term nil))))

;; ---- the roots, read on their own -------------------------------------------

(defn- roots-store
  "The `KvIndexStore` holding `index`'s root families: `index` itself, or the one a
  `ColumnarIndexStore` delegates its roots to as `:embedded`, or nil."
  [index]
  (cond (instance? KvIndexStore index)             index
        (instance? KvIndexStore (:embedded index)) (:embedded index)))

(defn roots-backend
  "The `KvBackend` under `index`'s root families (`roots-store`), or nil."
  [index]
  (:backend (roots-store index)))

(defn slot-predicates
  "The predicates the slot roster lists at `(pos, term)` — every predicate holding a fact,
  in either polarity, with `term` at 1-based argument `pos` — or nil for an index store
  this finds no roster in.

  The roster read the two predicate-agnostic reads above open with, without the postings
  they then union: a caller asking *which predicates* hold a term pays one set read and no
  handle.  Not an `IndexStore` op.  Every index store the engine builds keeps the roster
  in a `KvIndexStore` — itself, or the one a `ColumnarIndexStore` delegates its roots to
  as `:embedded` — and this reads it there.  An empty slot answers `#{}`, so nil means
  only that the store holds neither (a test's `reify`), and the caller falls back to the
  reads the protocol has."
  [index pos term]
  (when-let [kis (roots-store index)]
    (prof/record-read :argument-slot)
    (or (kv-members (:backend kis) (slot-key pos (sx/canon term))) #{})))

(defn unary-multi-terms
  "The terms the unary roster lists two or more predicates of, as a set, or nil for an
  index store this finds no roster in.  A superset of the terms holding two memberships,
  as the unary roster is a superset (`unary-slot-key`)."
  [index]
  (when-let [kis (roots-store index)]
    (prof/record-read :argument-slot)
    (or (kv-members (:backend kis) unary-multi-key) #{})))

(defn self-tuples
  "The handles of the ground positive binary self tuples `(f a a)` of functor `f` stated
  in a context of `ctxs` (every context when nil), or nil for an index store this finds no
  roots store in: the `:self-tuple` node's children intersected with `ctxs`, and a leaf
  read per context kept."
  [index f ctxs]
  (when-let [kis (roots-store index)]
    (prof/record-read :predicate-extent)
    (node-handles (:backend kis) :self-tuple [f] ctxs)))

(defn shape-lengths
  "The lengths the positive facts of functor `f` are stored at, as a set, or nil for an
  index store this finds no shape roster in."
  [index f]
  (when-let [kis (roots-store index)]
    (prof/record-read :predicate-extent)
    (or (kv-members (:backend kis) (shape-lengths-key f)) #{})))

(defn extent-contexts
  "The contexts of `contexts` (every context when nil) stating a fact of functor `pred`,
  either polarity: the predicate extent's children intersected with `contexts`, which costs
  min(|children|, |contexts|) probes and reads no leaf — or nil for an index store this
  finds no extent in (a test's `reify`).  Not an `IndexStore` op; read where
  `slot-predicates` reads."
  [index pred contexts]
  (when-let [kis (roots-store index)]
    (prof/record-read :predicate-extent)
    (seen-ctxs (:backend kis) :predicate-extent [pred] contexts)))

(defn rule-keys
  "The antecedent keys some stored rule takes (`rules/antecedent-key`), as a set, or nil
  for an index store this finds no rule index in."
  [index]
  (when-let [kis (roots-store index)]
    (prof/record-read :rule-index)
    (or (kv-members (:backend kis) rule-keys-key) #{})))

(defn rule-key?
  "Does a stored rule take the antecedent key `k`?  One membership test, or nil for an
  index store this finds no rule index in."
  [index k]
  (when-let [kis (roots-store index)]
    (prof/record-read :rule-index)
    (kv-member? (:backend kis) rule-keys-key k)))

(defn rule-extent
  "The handles of the rules of `kind` (`:rule`, every rule; `:solve`, the rules a solve
  reads) stated in one of `contexts` (every context when nil): the rule extent's children
  intersected with `contexts`, and a leaf read per context kept.  nil for an index store
  this finds no rule extent in."
  [index kind contexts]
  (when-let [kis (roots-store index)]
    (prof/record-read :rule-index)
    (node-handles (:backend kis) :rule-extent [kind] contexts)))

(defn rule-extent-contexts
  "The contexts of `contexts` (every context when nil) stating a rule of `kind`, with no
  leaf read, or nil for an index store this finds no rule extent in."
  [index kind contexts]
  (when-let [kis (roots-store index)]
    (prof/record-read :rule-index)
    (seen-ctxs (:backend kis) :rule-extent [kind] contexts)))

(defn opposed-count
  "How many bodies are stored in both polarities: the size of `opposed-bodies-key`, one
  read.  nil for an index store this finds no `KvIndexStore` in."
  [index]
  (when-let [kis (roots-store index)]
    (prof/record-read :opposed)
    (kv-count (:backend kis) opposed-bodies-key)))

(defn opposed-body?
  "Is `body` stored in both polarities?  One membership test, or nil for an index store
  this finds no `KvIndexStore` in."
  [index body]
  (when-let [kis (roots-store index)]
    (prof/record-read :opposed)
    (kv-member? (:backend kis) opposed-bodies-key body)))

(defn opposed-bodies
  "Every body stored in both polarities, as a set, or nil for an index store this finds
  no `KvIndexStore` in."
  [index]
  (when-let [kis (roots-store index)]
    (prof/record-read :opposed)
    (or (kv-members (:backend kis) opposed-bodies-key) #{})))

(defn opposed-members
  "The handles of `body`'s facts of both polarities while it is stored in both, in every
  context, or nil for an index store this finds no `KvIndexStore` in."
  [index body]
  (when-let [kis (roots-store index)]
    (prof/record-read :opposed)
    (node-handles (:backend kis) :opposed [body] nil)))

(defn opposed-in
  "The members of every opposed body stated in a context of `ctxs`: one leaf read per
  context, `[:opposed-in ctx]`, so the read costs |ctxs| plus the members it returns.  nil
  for an index store this finds no `KvIndexStore` in."
  [index ctxs]
  (when-let [kis (roots-store index)]
    (prof/record-read :opposed)
    (let [b (:backend kis)]
      (into #{} (mapcat #(kv-members b (opposed-in-key %))) ctxs))))

;; ---- the mint family -----------------------------------------------------------
;; Written and read where the rule extent is, in the `KvIndexStore` `roots-store` finds.
;; Each read is nil for an index store this finds no family in.

(defn justification-family-entry?
  "Is `entry`, a `[key value]` index entry, one of the mint family's, which the stored
  justifications derive rather than the stored sentexes?"
  [entry]
  (let [k (when (sequential? entry) (first entry))]
    (and (vector? k) (contains? #{:mint :mint-in :mint-terms} (first k)))))

(defn post-mint!
  "File record `h` under `term` in context `c` in one batch, unless it is filed there."
  [index term c h]
  (when-let [kis (roots-store index)]
    (let [b (:backend kis)]
      (some->> (mint-adds b term c h) (kv-batch b))))
  nil)

(defn retire-mint!
  "Take record `h` out from under `term` in context `c` in one batch, when it is filed
  there."
  [index term c h]
  (when-let [kis (roots-store index)]
    (let [b (:backend kis)]
      (some->> (mint-retires b term c h) (kv-batch b))))
  nil)

(defn mint-count
  "How many records the mint family files: the count of the `:mint-in` node."
  [index]
  (when-let [kis (roots-store index)]
    (prof/record-read :mint)
    (->count (kv-get (:backend kis) (node-count-key :mint-in [])))))

(defn mint-terms
  "The terms some mint is about, as a set: the `:mint` trie's root level."
  [index]
  (when-let [kis (roots-store index)]
    (prof/record-read :mint)
    (or (kv-members (:backend kis) mint-terms-key) #{})))

(defn mint-term-count
  "How many terms some mint is about, read without building the set."
  [index]
  (when-let [kis (roots-store index)]
    (prof/record-read :mint)
    (kv-count (:backend kis) mint-terms-key)))

(defn mint-term?
  "Is some mint about `term`?  One membership test."
  [index term]
  (when-let [kis (roots-store index)]
    (prof/record-read :mint)
    (kv-member? (:backend kis) mint-terms-key term)))

(defn mints-about
  "The handles of the mints about `term`, in every context."
  [index term]
  (when-let [kis (roots-store index)]
    (prof/record-read :mint)
    (node-handles (:backend kis) :mint [term] nil)))

(defn mint-filed?
  "Is record `h` filed as a mint about `term` in context `c`?  One membership test."
  [index term c h]
  (when-let [kis (roots-store index)]
    (prof/record-read :mint)
    (kv-member? (:backend kis) (node-leaf-key :mint [term] c) h)))

(defn mint-contexts
  "The contexts some mint is stored in, as a set: the `:mint-in` node's children."
  [index]
  (when-let [kis (roots-store index)]
    (prof/record-read :mint)
    (or (kv-members (:backend kis) (node-ctxs-key :mint-in [])) #{})))

(defn mint-context-count
  "How many contexts some mint is stored in, read without building the set."
  [index]
  (when-let [kis (roots-store index)]
    (prof/record-read :mint)
    (kv-count (:backend kis) (node-ctxs-key :mint-in []))))

(defn mints-in
  "The handles of the mints stored in context `c`: one `:mint-in` leaf."
  [index c]
  (when-let [kis (roots-store index)]
    (prof/record-read :mint)
    (kv-members (:backend kis) (node-leaf-key :mint-in [] c))))

(defn children-held
  "The child tokens under the trie's interior `prefix` as the backend holds them, a set, or
  nil when `index` is not a `KvIndexStore` (a `ColumnarIndexStore` holds its trie itself).
  On the map backends the answer is the stored set, so two reads with no write between
  them answer one object; `children` copies it into a vector."
  [index prefix]
  (when (instance? KvIndexStore index)
    (prof/record-read :trie-counts)
    (or (kv-members (:backend index) (set-key prefix)) #{})))

(defn extent-census
  "`[seen n]`: the contexts of the set `ctxs` (every context when nil) in which a fact with
  functor `pred` is stored, either polarity, and how many contexts state one.  The children
  of the predicate extent's node `[pred]`: one count read, then, when it is not zero, the
  intersection with `ctxs` on the smaller side, with no leaf read.  nil for an index store
  this finds no `KvIndexStore` in, as `slot-predicates`."
  [index pred ctxs]
  (when-let [kis (roots-store index)]
    (prof/record-read :predicate-extent)
    (let [b (:backend kis)
          n (long (kv-count b (node-ctxs-key :predicate-extent [pred])))]
      [(if (zero? n) [] (seen-ctxs b :predicate-extent [pred] ctxs)) n])))

(defn- node-count-in
  "How many handles the `tag` trie's `node` holds in the contexts `seen-ctxs` keeps: one
  leaf count per kept context."
  [backend tag node ctxs]
  (transduce (map #(kv-count backend (node-leaf-key tag node %))) + 0
             (seen-ctxs backend tag node ctxs)))

(defn extent-count-in
  "How many facts with functor `pred` are stored in the contexts of the set `ctxs`: one
  leaf count per context `extent-census` keeps.  nil where `extent-census` is nil."
  [index pred ctxs]
  (when-let [kis (roots-store index)]
    (prof/record-read :predicate-extent)
    (node-count-in (:backend kis) :predicate-extent [pred] ctxs)))

(defn arg-count-in
  "How many facts with functor `pred` and `term` at argument `pos` are stored in the
  contexts of the set `ctxs`: one leaf count per context of the argument node `seen-ctxs`
  keeps.  nil where `extent-census` is nil."
  [index pred pos term ctxs]
  (when-let [kis (roots-store index)]
    (prof/record-read :argument-root)
    (node-count-in (:backend kis) :argument-root [pred pos (sx/canon term)] ctxs)))

(defn arg-census
  "`[n k]`: how many facts with functor `pred` and `term` at argument `pos` are stored, in
  every context, and how many contexts state one.  The argument node's own count and its
  context-children count, two count reads.  nil where `extent-census` is nil."
  [index pred pos term]
  (when-let [kis (roots-store index)]
    (prof/record-read :argument-root)
    (let [b    (:backend kis)
          node [pred pos (sx/canon term)]]
      [(->count (kv-get b (arg-count-key node))) (long (kv-count b (arg-ctxs-key node)))])))

;; ---- the taxonomy's supporter families ------------------------------------
;; The taxonomy writers (`vaelii.impl.taxonomy`) post two families here, keyed by the key a
;; declaration installs: `[:genl a b]` or `[:genlCx a b]` for an edge, a flat-cache key
;; (`[:disjoint #{a b}]`, `[:prop kind pred]`, …) otherwise.
;;
;;   :tax-support   a count trie ending in the context: node `k`, count the supporter
;;                  count, children the supporting contexts, leaf `(conj k ctx)` the
;;                  supporting handles stated in `ctx`
;;   :tax-installs  `[:tax-installs h]`, the keys handle `h` installs: one edge for a
;;                  `genl` fact, one per part for a cover, two for `(commutative P)`
;;
;; A cover's handle is posted under each edge it installs, so the node `[:genl part whole]`
;; lists it beside the `genl` facts stating that edge.  Both writes read before they write:
;; the post skips a handle already under `k` in `ctx`, and the retire reads whether the
;; leaf and the node empty (`node-retire`).

(defn- installs-key [h] [:tax-installs h])

(defn supporter-adds
  "Write ops entering handle `h`, stated in `ctx`, as a supporter of taxonomy key `k`, or
  nil when it already is one."
  [backend k h ctx]
  (let [leaf (node-leaf-key :tax-support k ctx)]
    (when-not (kv-member? backend leaf h)
      (-> [[:add-to-set leaf h]]
          (into (node-add :tax-support k ctx))
          (conj [:add-to-set (installs-key h) k])))))

(defn supporter-retires
  "Write ops taking handle `h` out of taxonomy key `k`'s supporters, or nil when it is not
  one.  Reads the contexts under `k` for the one whose leaf holds `h`."
  [backend k h]
  ;; the context may be nil (a raw taxonomy's supporter with none), so it is found boxed
  (when-let [[c] (some #(when (kv-member? backend (node-leaf-key :tax-support k %) h) [%])
                       (kv-members backend (node-ctxs-key :tax-support k)))]
    (-> [[:remove-from-set (node-leaf-key :tax-support k c) h]]
        (into (:ops (node-retire backend :tax-support k c h)))
        (conj [:remove-from-set (installs-key h) k]))))

(defn post-supporter!
  "Enter `h` (stated in `ctx`) as a supporter of taxonomy key `k` in `index`'s roots
  store, in one batch, and answer `k`'s supporter count after it: the batch's reply to
  the node's increment, nil where the backend replies none (a bulk load's transient).  A
  no-op answering nil when `h` already is one, or when `index` keeps no roots store."
  [index k h ctx]
  (when-let [kis (roots-store index)]
    (when-let [ops (supporter-adds (:backend kis) k h ctx)]
      ;; the node's increment is the third op `supporter-adds` writes
      (some-> (nth (kv-batch (:backend kis) ops) 2) ->count))))

(defn retire-supporter!
  "Take `h` out of taxonomy key `k`'s supporters in `index`'s roots store, in one batch,
  and answer true; a no-op answering false when it is not one."
  [index k h]
  (boolean
   (when-let [kis (roots-store index)]
     (when-let [ops (supporter-retires (:backend kis) k h)]
       (kv-batch (:backend kis) ops)
       true))))

(defn supporters
  "Taxonomy key `k`'s supporters as `{handle ctx}`: the node's children, then one leaf
  read per context.  nil for an index store this finds no roots store in."
  [index k]
  (when-let [kis (roots-store index)]
    (prof/record-read :tax-support)
    (let [b (:backend kis)]
      (reduce (fn [m c] (reduce #(assoc %1 %2 c) m (kv-members b (node-leaf-key :tax-support k c))))
              {} (kv-members b (node-ctxs-key :tax-support k))))))

(defn supporter-count
  "How many handles support taxonomy key `k`: the node's count, one read."
  [index k]
  (when-let [kis (roots-store index)]
    (prof/record-read :tax-support)
    (->count (kv-get (:backend kis) (node-count-key :tax-support k)))))

(defn installed-keys
  "The taxonomy keys handle `h` installs, as a set: one read."
  [index h]
  (when-let [kis (roots-store index)]
    (prof/record-read :tax-support)
    (or (kv-members (:backend kis) (installs-key h)) #{})))

(defn all-supporters
  "Every taxonomy key with a supporter, as `{k {handle ctx}}`, by a walk of every entry in
  `index`'s roots store: O(store), for a raw taxonomy's private store, which holds the
  supporter families and nothing else."
  [index]
  (when-let [kis (roots-store index)]
    (prof/record-read :tax-support)
    (reduce (fn [m [ek hs]]
              (if (and (vector? ek) (= :tax-support (nth ek 0)) (= :handles (nth ek 1)))
                (let [leaf (nth ek 2)
                      k    (pop leaf)
                      c    (peek leaf)]
                  (reduce #(assoc-in %1 [k %2] c) m hs))
                m))
            {} (kv-entries (:backend kis)))))

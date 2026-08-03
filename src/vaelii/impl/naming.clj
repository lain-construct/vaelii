;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.naming
  "KB naming invariants, as predicates over symbols — and the walk that applies them to
  every **literal** of a sentence rather than to its outermost functor alone.

    predicate    camelCase, lowercase-initial, no underscore   parentOf, genl, argIsa
    individual   CapitalCamelCase                               Fido, Tom
    type         snake_case, lowercase, unary predicate         dog, physical_object
    context      CapitalCamelCase ending in Context             UniverseContext, CoreContext

  Single lowercase words (dog, genl, parentOf) satisfy both `predicate?` and
  `type-symbol?`; role is disambiguated by position and arity, not the symbol alone.
  A functor carrying an **underscore** is a type name and nothing else, and types are
  used as *unary* predicates — `(dog Fido)`, not `(isa Fido Dog)` — so it is legal at
  arity 1 and nowhere else.  `(lives_in penguin cold_place)` is a type name doing a
  relation's job; admitting it fragments the vocabulary into one-off predicates
  (`lives_in_antarctica`, `capable_of_swimming`) that can never join a rule or match
  another sentence.

  How hard these are enforced is the **KB's** to say, not this namespace's: `open-kb`'s
  `:naming` selects `:strict` / `:warn` / `:off` (`policies`, below) and `assert` reads
  it.  The predicates themselves do not move — `:off` stores a name nothing can classify,
  not one classified differently.

  `problems` checks the functor of every literal a sentence contains — a rule's
  antecedents, its consequent, an `exceptWhen` query's conjuncts, a `not` body, an
  `ist`-directed sentence, a negation-as-failure query — not only the outermost one.
  A rule consequent is exactly where generated content lands, and the outermost
  functor there is `implies`."
  (:refer-clojure :exclude [name])
  (:require [clojure.string :as str]
            [taoensso.trove :as trove]
            [vaelii.impl.sentex :as sx]))

(defn- nm [s] (clojure.core/name s))

(defn context?    [x] (and (symbol? x) (some? (re-matches #"[A-Z][A-Za-z0-9]*Context" (nm x)))))
(defn individual? [x] (and (symbol? x) (some? (re-matches #"[A-Z][A-Za-z0-9]*" (nm x)))
                           (not (context? x))))
(defn predicate?  [x] (and (symbol? x) (some? (re-matches #"[a-z][a-zA-Z0-9]*" (nm x)))))
(defn type-symbol? [x] (and (symbol? x) (some? (re-matches #"[a-z][a-z0-9_]*" (nm x)))))

(defn functor [sentence] (when (sequential? sentence) (first sentence)))
(defn args    [sentence] (when (sequential? sentence) (rest sentence)))
(defn arity   [sentence] (if (sequential? sentence) (dec (count sentence)) 0))

;; ---- the literals of a sentence ------------------------------------------
;; A naming invariant is about a **literal** — a predicate applied to arguments.
;; Everything else a sentence is built from is a *frame*: a structural connective
;; (`not` / `and` / `implies`), a virtual rule wrapper (`set/*Rule`), an `exceptWhen`,
;; an `ist` redirection, a negation-as-failure quantifier, a `sentexHandle` naming
;; another sentex.  A frame's functor is engine vocabulary rather than a name the
;; author chose, so the walk descends through it and checks what it holds.
;;
;; Arguments are deliberately **not** walked: a compound in argument position is a
;; term, not a literal — an arithmetic expression `(+ 1 2)`, a NAUT `(QuantityFn 5
;; Meter)`, a quoted connective `(comment not "…")` — and its head names a function or
;; is plain data, neither of which the predicate conventions govern.

(def ^:private literal-roles
  "The frame a literal sits in, as it reads in a rejection.  A repair loop is handed
  the message verbatim, so it has to say *which* literal of the sentence broke."
  {:sentence   "sentence"
   :antecedent "rule antecedent"
   :consequent "rule consequent"
   :exception  "exceptWhen exception"})

(def problem-classes
  "What a naming violation *is*, as a keyword, with the human line under it.  A rejection
  reads as prose, but a caller that counts them needs to group without parsing English —
  an operator auditing a corpus wants five numbers, not eleven million sentences — so the
  class is the datum and the message is rendered from it."
  {:context-name  "the KB context named is not a context"
   :functor       "a functor matching no convention"
   :functor-arity "a snake_case functor (a type) at an arity other than 1"
   :argument      "a symbol argument matching no convention"
   :ist-context   "an ist context slot that does not name a context"
   :dot-marker    "a dotted rest marker outside a rule pattern"})

(defn- rule-wrapper?
  "One of the virtual wrappers that wrap a single rule form — direction, defeasible,
  assumption, constraint.  Each canonicalizes into a record field, so none of them is
  ever a predicate application."
  [h]
  (or (contains? sx/rule-direction-wrappers h)
      (= sx/default-rule-wrapper h)
      (= sx/assumption-rule-wrapper h)
      (contains? sx/constraint-rule-wrappers h)))

(defn- exception-query-conjuncts
  "The conjunct literals of an `exceptWhen` wrapper's query: a vector is a conjunction,
  anything else a single literal.  The shape `sentex/exception-conjuncts` normalizes,
  read here without canonicalizing — a check must not intern the symbols of content it
  is about to refuse."
  [q]
  (if (vector? q) q [q]))

(defn literals
  "The `[role literal]` pairs of `sentence` as written — every position at which it
  applies a predicate to arguments, tagged with the frame that position sits in
  (`:sentence` / `:antecedent` / `:consequent` / `:exception`).

  Frames are descended through, arguments are not, so this is exactly the set of
  functors an author named."
  ([sentence] (literals :sentence sentence))
  ([role form]
   (if-not (and (sequential? form) (seq form))
     []
     (let [h (first form)
           n (count form)]
       (cond
         ;; a variable in functor position is a pattern — the dotted rest `(?pred
         ;; . ?args)`, or a bare `(?p ?x)` — and names no predicate to check
         (sx/variable? h) []

         ;; a `do/` imperative is an instruction; it is refused outright inside a rule
         ;; (`core/check-no-imperative`) and dispatched at the top level, never named
         (sx/do-form? form) []

         ;; `(sentexHandle N)` names a stored sentex by integer id
         (= sx/sentex-handle-functor h) []

         (rule-wrapper? h) (literals role (second form))

         ;; `(exceptWhen <query> <rule-or-handle>)` — the query's conjuncts are
         ;; literals of their own, then whatever the exception qualifies
         (and (= sx/except-wrapper h) (= 3 n))
         (into (vec (mapcat #(literals :exception %)
                            (exception-query-conjuncts (second form))))
               (literals role (nth form 2)))

         (and (= sx/not-functor h) (= 2 n)) (literals role (second form))

         (= sx/and-functor h) (vec (mapcat #(literals role %) (rest form)))

         (and (= sx/rule-functor h) (= 3 n))
         (into (vec (mapcat #(literals :antecedent %) (sx/rule-antecedents form)))
               (literals :consequent (sx/rule-consequent form)))

         ;; `(ist Ctx S)` directs S into Ctx; S is the literal (Ctx is checked by
         ;; `ist-context-problems`)
         (and (= sx/ist-functor h) (= 3 n)) (literals role (nth form 2))

         ;; negation as failure: `(unknown S)` and `(thereExists <vars> S)` frame a
         ;; query, and a head `(exists <vars> C)` frames the consequent it quantifies
         (sx/unknown? form)      (literals role (second form))
         (sx/there-exists? form) (literals role (nth form 2))
         (sx/head-exists? form)  (literals role (sx/head-exists-body form))

         ;; an aggregate frames a query too: `(agg/count ?n ?v <body>)` says
         ;; nothing itself, and its body is a goal rather than an argument — read as a
         ;; literal it would be a three-place `agg/count` and the body inside it
         ;; would never be checked at all
         (sx/aggregate? form)    (literals role (sx/aggregate-body form))

         :else [[role form]])))))

;; ---- the invariants, per literal -----------------------------------------

(defn- camel-case
  "The camelCase spelling of a snake_case symbol — `lives_in` ⇒ `livesIn`.  Named in
  the rejection so whoever reads it is told what to write, not only what is wrong."
  [s]
  (let [[head & more] (str/split (nm s) #"_+")]
    (apply str head (map str/capitalize more))))

(defn- functor-problem
  "The naming violation of one `[role literal]` pair's functor, or nil.  Two ways to
  fail: the symbol matches no convention at all, or it is snake_case — a type name —
  used at an arity other than 1."
  [[role literal]]
  (let [f (functor literal)]
    (cond
      (nil? f) nil

      (not (or (predicate? f) (type-symbol? f)))
      {:class :functor :role role :symbol f :literal literal}

      (and (not (predicate? f)) (not= 1 (arity literal)))
      {:class :functor-arity :role role :symbol f :literal literal})))

(defn- pascal-case
  "The CapitalCamelCase spelling of an underscored symbol — `South_Pole` ⇒ `SouthPole`."
  [s]
  (apply str (map str/capitalize (str/split (nm s) #"_+"))))

(defn- argument-problem
  "The naming violation of one atomic symbol argument, or nil.  An argument *names*
  something — an individual, a type, a predicate, a context — so it is held to the
  same conventions as a functor.  `Baby_Penguin` matches none of them: CapitalCamelCase
  admits no underscore and snake_case no capital, so the symbol claims two roles and
  fills neither.  Both repairs are named, since which one is meant is the author's to
  say: `BabyPenguin` if it is an individual, `baby_penguin` if it is a type.

  Only the literal's **own** arguments are checked, never a compound one's insides: a
  compound in argument position is a term — `(+ 1 2)`, a NAUT `(QuantityFn 5 Meter)` —
  and its head is a function, not a name this can judge.  Non-symbols (a number, a
  comment's string) name nothing and are skipped, as is a variable and the dotted rest
  marker."
  [[role literal] a]
  (when (and (symbol? a)
             (not (sx/variable? a))
             (not= sx/dot-marker a)
             (not (or (individual? a) (context? a) (predicate? a) (type-symbol? a))))
    {:class :argument :role role :symbol a :literal literal}))

(defn- ist-context-problems
  "The `(ist Ctx S)` context slots that do not name a context.  A rule consequent
  `(ist Ctx S)` places S into Ctx, so that slot is a context name like the asserting
  context — or a variable an antecedent binds, which is resolved at firing time."
  [sentence]
  (for [f (tree-seq sequential? seq sentence)
        :when (and (sequential? f) (= sx/ist-functor (first f)) (= 3 (count f)))
        :let [c (second f)]
        :when (not (or (sx/variable? c) (context? c)))]
    {:class :ist-context :role :sentence :symbol c :literal f}))

(defn message
  "One `problems*` map rendered as the line a rejection carries.  Every message names
  the offending symbol, the frame it sits in and the spelling to write instead: whoever
  reads it is mid-repair, and a violation reported without its fix is a second lookup."
  [{:keys [class role symbol literal]}]
  (let [where (str (literal-roles role) " " (pr-str literal))]
    (case class
      :context-name
      (str "context " symbol " must be CapitalCamelCase ending in Context")

      :functor
      (str "functor " (pr-str symbol) " in " where " matches no naming convention: a"
           " predicate is camelCase (parentOf, argIsa), a type is snake_case"
           " (physical_object) and only unary")

      :functor-arity
      (str "functor " symbol " in " where " is snake_case, which names a type and is legal"
           " only as a unary predicate, but has " (arity literal) " arguments — write it"
           " camelCase as " (camel-case symbol) ", or as (" symbol " <one argument>)")

      :argument
      (str "argument " (pr-str symbol) " in " where
           " matches no naming convention: an individual is CapitalCamelCase (Fido), a"
           " type is snake_case (physical_object), a predicate is camelCase (parentOf)"
           " — write it " (pascal-case symbol) " for an individual, or "
           (str/lower-case (nm symbol)) " for a type")

      :ist-context
      (str "ist directs " (pr-str literal) " into " (pr-str symbol)
           ", which must be CapitalCamelCase ending in Context, or a variable an"
           " antecedent binds")

      :dot-marker
      "'.' is not a valid argument (dotted rest patterns belong in rule patterns)")))

(defn problems*
  "Checkable naming violations for a sentence in a context, as **data**: a vector of
  `{:class :role :symbol :literal}` maps in the order `problems` reports them.  `:class`
  is one of `problem-classes`, `:role` the frame the offending literal sits in, `:symbol`
  the name that broke the convention, and `message` renders the line.

  Data rather than prose because the two callers want different halves of it.  `assert`
  wants the sentence it refused spelled out; an audit over a whole corpus wants to
  *group* — how many violations, of which class, over how many distinct spellings — and
  a message that embeds the literal is unique per record, so counting them counts
  records.  Rendering is therefore separate and paid only where a message is read."
  [sentence context]
  (into []
        cat
        [(when-not (context? context)
           [{:class :context-name :role :sentence :symbol context :literal nil}])
         (keep functor-problem (literals sentence))
         (for [pair (literals sentence)
               a    (args (second pair))
               :let [p (argument-problem pair a)]
               :when p]
           p)
         (ist-context-problems sentence)
         ;; a bare `.` is the dotted rest-pattern marker; it belongs inside a rule
         ;; antecedent, never as a top-level argument of an asserted sentence.
         (when (some #(= sx/dot-marker %) (args sentence))
           [{:class :dot-marker :role :sentence :symbol sx/dot-marker :literal sentence}])]))

(defn problems
  "Checkable naming violations for a sentence in a context (seq of strings): the
  context's own name, then every literal's functor (outermost frame first), then every
  literal's atomic symbol arguments, then any `ist` context slot, then the dotted rest
  marker where it cannot appear.

  **This is a check on the shape of a name, not on whether the name is worth having.**
  A *unary* snake_case functor is a well-formed type name, so
  `(implies (penguin ?x) (has_black_and_white_feathers ?x))` passes here, and so would
  `capable_of_swimming` or `thermoregulates_via_blubber_and_feathers` — each is exactly
  what the invariants say a type looks like.  Nothing about a symbol distinguishes a
  type the ontology wants from a one-off coined for a single sentence, so nothing here
  can refuse the second: judging that needs the KB's existing vocabulary, which is a
  separate question asked elsewhere.  Read this as a guard against *misnamed* content,
  never as a guard against vocabulary fragmentation."
  [sentence context]
  (mapv message (problems* sentence context)))

;; ---- the policy: whose invariants, and how hard ---------------------------
;;
;; The conventions above are what *this* KB reads a role off, and a KB holding a corpus
;; that spells its names differently is not thereby malformed — it is a KB whose front
;; door is set to a different opinion.  So the policy is per-KB (`open-kb`'s `:naming`),
;; not a property of the build: one process can hold a strict KB beside a corpus loaded
;; verbatim, and neither has to win.
;;
;; What the setting does **not** change is the role reading.  `predicate?` and its three
;; siblings answer the same way under every policy, so `:off` is a KB that stores a name
;; it cannot classify — `term-role` says nil, a `(Type Individual)` goal takes the general
;; path rather than the shortcut — rather than one that classifies differently.  That is
;; the whole cost, and it is why the check is worth keeping on where the content is
;; hand-written.

(def policies
  "What a KB does with a naming violation, and the one line each is for.

  A bulk path is not on this list because it does not consult it: a corpus import builds
  records directly and never asks (`docs/naming.md`, \"The two doors\").  What it does
  instead is *report* — an operator learns the refused fraction at load time, from a
  count rather than from a failed experiment a year later."
  {:strict "refuse the assertion (the default: names stay legible)"
   :warn   "log each one and store anyway (a corpus being cleaned up)"
   :off    "store in silence (a corpus with its own spelling conventions)"})

(defn blocking-problems
  "The naming violations that **stop** something under `policy` — the messages, or nil.
  Empty under `:warn` and `:off` by construction, so a caller that has to yield a value
  rather than throw (`special/definitional-violation`, the `assert` dry run) asks this
  and needs no policy branch of its own."
  [policy sentence context]
  (when (= :strict policy) (seq (problems sentence context))))

;; ---- the other door: count what it would have refused ---------------------
;;
;; A bulk path stores what `assert` refuses, which is the point of having one — but a
;; store whose contents the front door disagrees with is a fact about that store, and the
;; only moment anybody is in a position to learn it cheaply is while the records are
;; going past.  So the bulk paths **count** what they do not check.  The tally is a
;; running map rather than a scan afterwards: a second pass over a corpus that needed a
;; bulk path in the first place is a second pass nobody will run.

(def empty-tally
  "A fresh `tally` accumulator: records seen, records with at least one violation, and
  the per-class breakdown.  Counts records rather than violations — one sentence can
  break three conventions, and what an operator is deciding is what fraction of the
  corpus is re-assertable."
  {:checked 0 :refused 0 :by-class {}})

(defn tally
  "Fold one sentence's violations into `t`.  Counts and classes only, never spellings: a
  corpus large enough to need a bulk path has a vocabulary large enough that holding its
  distinct offending names would cost more than the load
  (`vaelii.bench.survey`'s `naming` audit is where that question is asked)."
  [t sentence context]
  (let [ps (problems* sentence context)
        t  (update t :checked inc)]
    (if (empty? ps)
      t
      (-> t
          (update :refused inc)
          (update :by-class
                  #(reduce (fn [m c] (update m c (fnil inc 0)))
                           % (into #{} (map :class) ps)))))))

(defn tally-line
  "The one line a load prints about `t`, or nil when the front door agrees with the
  corpus — which is the common case and deserves no output at all."
  [t]
  (let [{:keys [checked refused by-class]} t]
    (when (pos? (long refused))
      (str (format "%,d of %,d records (%.1f%%) hold names `assert` would refuse: "
                   (long refused) (long checked)
                   (* 100.0 (/ (double refused) (double (max 1 checked)))))
           (str/join ", " (for [[c n] (sort-by val > by-class)]
                            (str (clojure.core/name c) " " (format "%,d" (long n)))))
           " — they are stored, findable and countable, but re-asserting one throws"
           " under :naming :strict"))))

(defn check!
  "Enforce `policy` on `sentence` in `context`: throw `:naming` under `:strict`, log
  under `:warn`, do nothing under `:off`.  The one place the three differ, so no caller
  spells the throw out and none can drift from another."
  [policy sentence context]
  (when (not= :off policy)
    (when-let [ps (seq (problems sentence context))]
      (if (= :warn policy)
        (trove/log! {:level :warn :id ::naming-violation
                     :msg  (str "naming invariant (stored anyway, :naming :warn): "
                                (str/join "; " ps))
                     :data {:sentence sentence :context context}})
        (throw (ex-info (str "naming invariant: " (str/join "; " ps))
                        {:type :naming :sentence sentence :context context}))))))

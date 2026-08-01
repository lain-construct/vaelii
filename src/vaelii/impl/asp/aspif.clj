(ns vaelii.impl.asp.aspif
  "Pure ASPIF text emitter. No vaelii deps, no I/O.

   ASPIF is the Potassco Answer Set Programming Intermediate Format, the
   ground-program protocol between gringo and clasp. We emit the full set
   of ground statement types: facts, normal rules, single- and multi-head
   choice atoms/rules, disjunctive heads, integrity constraints,
   weight/cardinality bodies, minimize (weak constraints), show output,
   projection (type 3), externals (type 5), assumptions (type 6),
   heuristics (type 7), and acyclicity edges (type 8).

   Wire format (line-oriented, space-separated):
     Line 1: `asp 1 0 0`
     Rule:     1 <head_type> <head_size> <head...> <body_type> <body_size> <lits...>
                 head_type = 0 disjunctive | 1 choice
                 head_size may exceed 1 (disjunction `a|b`, choice `{a;b;c}`)
                 body_type = 0 normal (list of signed literals)
                            = 1 weight body — see below
                 body literal: +atom for positive, -atom for default-negated
     Weight rule:
               1 <head_type> <head_size> <head...> 1 <lower_bound> <body_size>
                                                  <lit_1> <w_1> ... <lit_n> <w_n>
                 head fires when the sum of weights of satisfied body
                 literals is at least <lower_bound>. Cardinality is
                 the all-weights-equal-1 special case.
     Minimize: 2 <priority> <n> <lit_1> <w_1> ... <lit_n> <w_n>
     Project:  3 <n> <atoms...>
     Output:   4 <str_len> <str> <n_conditions> <atoms...>
     External: 5 <atom> <init>   init = 0 free | 1 true | 2 false | 3 release
     Assume:   6 <n> <signed_lits...>   (static assumption block)
     Heuristic:7 <modifier> <atom> <value> <priority> <body_size> <lits...>
                 modifier = 0 level | 1 sign | 2 factor | 3 init | 4 true | 5 false
     Edge:     8 <u> <v> <body_size> <lits...>   (acyclicity edge u→v)
     End:      0

   ASPIF has no native *bound* on a choice head (`lb {…} ub`); a bound is
   expressed by putting weight-rule + integrity-constraint cardinality
   enforcement beside a multi-head choice, the same way gringo does.

   Atom ids are positive integers; 0 is the terminator and must not
   appear as an atom. String lengths in show statements count bytes
   (equal to character count for ASCII); non-ASCII names need UTF-8
   byte counting which we do not currently handle.

   The public API has two halves:

     (1) Statement constructors (`fact`, `choice`, `rule`, `choice-rule`,
         `constraint`, `minimize`, `show`) that return plain data maps.
         Data form is inspectable, easy to assemble programmatically,
         and trivial to unit-test.

     (2) `render` turns a sequence of statements into the full ASPIF
         text with header and terminator."
  (:require
   [clojure.string :as str]))

(defn fact
  "Unconditional fact: `atom-id` is true in every model."
  [atom-id]
  {:type :fact :atom atom-id})

(defn choice
  "Choice atom `{atom-id}.` — solver may include it or not."
  [atom-id]
  {:type :choice :atom atom-id})

(defn rule
  "Normal rule `head :- body`. `body` is a seq of signed literals
   (positive atom-id or negative for default negation)."
  [head body]
  {:type :rule :head head :body (vec body)})

(defn choice-rule
  "Choice rule `{head} :- body`. Solver may include `head` if the body
   holds."
  [head body]
  {:type :choice-rule :head head :body (vec body)})

(defn constraint
  "Integrity constraint `:- body`. Forbids models in which every body
   literal is satisfied."
  [body]
  {:type :constraint :body (vec body)})

(defn weight-rule
  "Weight rule `head :- LB { L1 = w1 ; L2 = w2 ; … }`. The head atom
   is derived when the sum of weights of satisfied body literals is
   at least `lower-bound`. For cardinality use weight 1 on every
   literal; `lower-bound` then becomes the cardinality lower bound.

   `weighted-literals` is a seq of `[signed-atom-id weight]` pairs.
   Signs work the same as in normal bodies (negative atom id means
   default negation)."
  [head lower-bound weighted-literals]
  {:type :weight-rule
   :head head
   :lower-bound lower-bound
   :literals (vec weighted-literals)})

(defn minimize
  "Weak constraint (minimize statement). `weighted-literals` is a seq of
   `[literal weight]` pairs. Priorities combine lexicographically when
   multiple minimize statements are present; within a priority, the
   cost is the sum of weights of satisfied literals."
  [priority weighted-literals]
  {:type :minimize
   :priority priority
   :literals (vec weighted-literals)})

(defn show
  "Output mapping `atom-id` to `text` in solver output. `text` must be
   ASCII and must not contain newline characters."
  [atom-id text]
  {:type :show :atom atom-id :text text})

(defn disjunction
  "Disjunctive rule `a | b | … :- body`. `head-atoms` is a seq of
   positive atom ids; the solver must make at least one of them true
   when `body` holds. A single-atom head is equivalent to `rule`."
  [head-atoms body]
  {:type :disjunction :head (vec head-atoms) :body (vec body)})

(defn choices
  "Multi-head choice rule `{a; b; c} :- body`. The solver may include
   any subset of `head-atoms` when `body` holds. A single-atom head is
   equivalent to `choice-rule`."
  [head-atoms body]
  {:type :choices :head (vec head-atoms) :body (vec body)})

(defn project
  "Projection statement `#project { atoms }`. Restricts enumeration /
   answer-set output to the listed `atoms`."
  [atoms]
  {:type :project :atoms (vec atoms)})

(def ^:private external-init
  "ASPIF external initial-value codes (clingo external value enum)."
  {:free 0 :true 1 :false 2 :release 3})

(defn external
  "`#external atom-id` with initial truth `init` (:free / :true / :false /
   :release; default :false). The atom is exempt from the closed-world
   default and its truth can be assigned at solve time."
  [atom-id & [init]]
  {:type :external :atom atom-id :init (or init :false)})

(defn assume
  "Static assumption block over `signed-literals` (positive atom id to
   assume true, negative to assume false), baked into the loaded program.
   For *per-call* assumptions in-process, use the solve-time assumptions
   argument instead; this line is primarily for the clasp fallback path."
  [signed-literals]
  {:type :assume :literals (vec signed-literals)})

(def ^:private heuristic-modifier
  "ASPIF #heuristic modifier codes."
  {:level 0 :sign 1 :factor 2 :init 3 :true 4 :false 5})

(defn heuristic
  "`#heuristic atom-id [value@priority, modifier] : body`. Steers the
   solver's search: `modifier` is one of :level / :sign / :factor / :init /
   :true / :false; `value` and `priority` are integers; `body` is a seq of
   signed literals gating the directive (empty = unconditional)."
  [modifier atom-id value priority body]
  {:type :heuristic :modifier modifier :atom atom-id
   :value value :priority priority :body (vec body)})

(defn edge
  "Acyclicity edge `#edge (u, v) : body` between node ids `u` and `v`.
   The solver rejects answer sets whose active edges form a cycle.
   `body` is a seq of signed literals gating the edge (empty = always)."
  [u v body]
  {:type :edge :u u :v v :body (vec body)})

(defn- body-tail
  "Render a normal body: `0 <n> <lit_1> ... <lit_n>`. Returns a string
   with a leading space so it can be concatenated directly to a head."
  [body]
  (if (seq body)
    (str " 0 " (count body) " " (str/join " " body))
    " 0 0"))

(defn- lit-list
  "Render `<n> <l_1> ... <l_n>` with a leading space — a bare literal/atom
   list with NO body_type prefix. Used by project/external/assume/heuristic/
   edge, whose tails are plain lists (no normal-vs-weight body distinction)."
  [items]
  (str " " (count items) (str/join (for [i items] (str " " i)))))

(defn- multi-head
  "Render `1 <head_type> <n> <atoms...>` followed by `body`'s tail. Shared
   by disjunctive (head_type 0) and choice (head_type 1) multi-head rules."
  [head-type head-atoms body]
  (str "1 " head-type " " (count head-atoms) " " (str/join " " head-atoms)
       (body-tail body)))

(defmulti ^:private emit-line :type)

(defmethod emit-line :fact [{:keys [atom]}]
  ;; 1 0 1 <atom> 0 0
  (str "1 0 1 " atom " 0 0"))

(defmethod emit-line :choice [{:keys [atom]}]
  ;; 1 1 1 <atom> 0 0
  (str "1 1 1 " atom " 0 0"))

(defmethod emit-line :rule [{:keys [head body]}]
  ;; 1 0 1 <head> 0 <|body|> <lits...>
  (str "1 0 1 " head (body-tail body)))

(defmethod emit-line :choice-rule [{:keys [head body]}]
  ;; 1 1 1 <head> 0 <|body|> <lits...>
  (str "1 1 1 " head (body-tail body)))

(defmethod emit-line :constraint [{:keys [body]}]
  ;; 1 0 0 0 <|body|> <lits...>
  (str "1 0 0" (body-tail body)))

(defmethod emit-line :weight-rule [{:keys [head lower-bound literals]}]
  ;; 1 0 1 <head> 1 <lb> <size> <lit_1> <w_1> ... <lit_n> <w_n>
  (str "1 0 1 " head
       " 1 " lower-bound " " (count literals)
       (str/join (for [[lit w] literals] (str " " lit " " w)))))

(defmethod emit-line :minimize [{:keys [priority literals]}]
  ;; 2 <priority> <n> <lit_1> <w_1> ... <lit_n> <w_n>
  (str "2 " priority " " (count literals)
       (str/join (for [[lit w] literals] (str " " lit " " w)))))

(defmethod emit-line :show [{:keys [atom text]}]
  ;; 4 <len> <text> 1 <atom>   (always a single-atom condition)
  (str "4 " (count text) " " text " 1 " atom))

(defmethod emit-line :disjunction [{:keys [head body]}]
  ;; 1 0 <n> <atoms...> 0 <|body|> <lits...>
  (multi-head 0 head body))

(defmethod emit-line :choices [{:keys [head body]}]
  ;; 1 1 <n> <atoms...> 0 <|body|> <lits...>
  (multi-head 1 head body))

(defmethod emit-line :project [{:keys [atoms]}]
  ;; 3 <n> <atoms...>
  (str "3" (lit-list atoms)))

(defmethod emit-line :external [{:keys [atom init]}]
  ;; 5 <atom> <init>
  (str "5 " atom " " (external-init init)))

(defmethod emit-line :assume [{:keys [literals]}]
  ;; 6 <n> <signed_lits...>
  (str "6" (lit-list literals)))

(defmethod emit-line :heuristic [{:keys [modifier atom value priority body]}]
  ;; 7 <modifier> <atom> <value> <priority> <|body|> <lits...>
  (str "7 " (heuristic-modifier modifier) " " atom " " value " " priority
       (lit-list body)))

(defmethod emit-line :edge [{:keys [u v body]}]
  ;; 8 <u> <v> <|body|> <lits...>
  (str "8 " u " " v (lit-list body)))

(defn render
  "Render a sequence of statements as a complete ASPIF program string
   with header and terminator. The input order is preserved."
  [statements]
  (apply str "asp 1 0 0\n"
         (concat (map #(str (emit-line %) "\n") statements)
                 ["0\n"])))

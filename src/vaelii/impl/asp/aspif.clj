;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.aspif
  "Pure ASPIF text emitter. No vaelii deps, no I/O.

   ASPIF is the Potassco Answer Set Programming Intermediate Format, the
   ground-program protocol between gringo and clasp.

   **This emits what the engine's programs are built from**, and no more:
   the rule line (type 1) as facts, choice atoms, normal rules and
   integrity constraints, plus minimize (2) and output (4).

   The rest of the format — projection (3), externals (5), assumptions
   (6), heuristics (7), acyclicity edges (8), and type 1's disjunctive
   and multi-head choice heads and weight bodies — was written out here
   once and never emitted, so nothing ever called it and no test ever
   checked it. An encoder nobody has executed is not coverage of a
   format; it is unverified text generation claiming to be. What the
   engine needs, it emits and its tests exercise; another type arrives
   with the caller that wants it.

   Wire format of what is emitted (line-oriented, space-separated):
     Line 1: `asp 1 0 0`
     Rule:     1 <head_type> <head_size> <head...> <body_type> <body_size> <lits...>
                 head_type = 0 disjunctive | 1 choice
                 body_type = 0 normal (list of signed literals)
                 body literal: +atom for positive, -atom for default-negated
     Minimize: 2 <priority> <n> <lit_1> <w_1> ... <lit_n> <w_n>
     Output:   4 <str_len> <str> <n_conditions> <atoms...>
     End:      0

   Atom ids are positive integers; 0 is the terminator and must not
   appear as an atom. String lengths in show statements count bytes
   (equal to character count for ASCII); non-ASCII names need UTF-8
   byte counting which we do not currently handle.

   The public API has two halves:

     (1) Statement constructors (`fact`, `choice`, `rule`, `constraint`,
         `minimize`, `show`) that return plain data maps. Data form is
         inspectable, easy to assemble programmatically, and trivial to
         unit-test.

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

(defn constraint
  "Integrity constraint `:- body`. Forbids models in which every body
   literal is satisfied."
  [body]
  {:type :constraint :body (vec body)})

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

(defn- body-tail
  "Render a normal body: `0 <n> <lit_1> ... <lit_n>`. Returns a string
   with a leading space so it can be concatenated directly to a head."
  [body]
  (if (seq body)
    (str " 0 " (count body) " " (str/join " " body))
    " 0 0"))

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

(defmethod emit-line :constraint [{:keys [body]}]
  ;; 1 0 0 0 <|body|> <lits...>
  (str "1 0 0" (body-tail body)))

(defmethod emit-line :minimize [{:keys [priority literals]}]
  ;; 2 <priority> <n> <lit_1> <w_1> ... <lit_n> <w_n>
  (str "2 " priority " " (count literals)
       (str/join (for [[lit w] literals] (str " " lit " " w)))))

(defmethod emit-line :show [{:keys [atom text]}]
  ;; 4 <len> <text> 1 <atom>   (always a single-atom condition)
  (str "4 " (count text) " " text " 1 " atom))

(defn render
  "Render a sequence of statements as a complete ASPIF program string
   with header and terminator. The input order is preserved."
  [statements]
  (apply str "asp 1 0 0\n"
         (concat (map #(str (emit-line %) "\n") statements)
                 ["0\n"])))

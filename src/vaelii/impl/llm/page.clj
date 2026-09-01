;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.llm.page
  "The page-scoped prompt: **the unit of work is the term the reader is looking at.**

  `vaelii.impl.llm.selection` prompts about lines the reader picked and asks for them
  back edited.  This namespace prompts about a *term page* — `/term?q=penguin` — and asks
  for knowledge the KB does not have yet:

  1. what the page already says about the term, as bare sentences,
  2. the vocabulary that term's `genl` neighbourhood licenses
     (`vaelii.impl.llm.inventory`) — arity and argument types included,
  3. the reader's free-text instruction (\"flesh out the capabilities of this\").

  Three things differ from the edit path, each because it was measured:

  * **The context is dropped.**  A page is already about one context, so the caller
    supplies it and the model writes bare sentences.  That removes a whole class of
    answer the model gets wrong for no gain — and it shortens every line it writes.
  * **Decoding is constrained** (`output-schema`, Ollama's `format`).  On generation this
    *rescues* models that otherwise answer in markdown prose; on the edit path the same
    parameter silently drops lines, so the two contracts are deliberately different and
    are not unified.
  * **The content is type-level.**  Common sense about a *kind* is a `genl` edge or a
    rule, not a fact about an individual, so the prompt asks for those shapes and shows
    them.

  The prompt's one job beyond the shape is to stop the model coining vocabulary — see
  `vaelii.impl.llm.inventory`, which is where both guards against that live."
  (:require [clojure.string :as str]
            [vaelii.core :as v]
            [vaelii.impl.llm.inventory :as inventory]
            [vaelii.impl.llm.selection :as selection]
            [vaelii.impl.naming :as nm]
            [vaelii.impl.protocols :as p]
            [vaelii.impl.reads :as reads]
            [vaelii.impl.sentex :as sx]))

;; ---- what the page already says -----------------------------------------

(defn- scanned
  "The first `n` sentexes mentioning `term`, **oldest first** — the candidates
  `stored-lines` sorts by content and cuts to its line bound.

  The term index answers with a *set* of handles, so a scan that took whatever it
  enumerated first would sample the term's knowledge by hash of handle: an order no reader
  can name, and one that moves with the index's representation.  Sorting the handles ahead
  of the fetch makes the sample the term's earliest `n` mentions instead — one answer per
  knowledge base, on every backend and every read.  The set is materialized by the index
  either way, so this costs a sort over handles and not one extra record fetch.

  A **compound** term is narrowed by the atoms it holds and each candidate verified against
  its own sentence, which is `vaelii.core/find-sentexes`' work rather than this
  namespace's, so one is scanned in the order the index answered.  A page's term is a
  name."
  [kb term n]
  (if (symbol? term)
    (into [] (comp (map #(p/get-sentex (:records kb) %)) (remove nil?))
          (take n (sort (reads/as-stored-with-term (:index kb) (sx/canon term)))))
    (into [] (take n) (v/find-sentexes kb term))))

(defn- line-of
  "The sentence as the one string the prompt shows, deduplicates on, and sorts by.

  Printed with the print bounds released: `*print-length*` or `*print-level*` bound by a
  caller would elide the tail of a line the model is asked to read as knowledge, and two
  sentences agreeing up to the elision would collapse into one key."
  [sentence]
  (binding [*print-length* nil *print-level* nil]
    (pr-str sentence)))

(defn stored-lines
  "What the term page shows, as `[{:handle :sentence :context :line} …]` — the stored
  sentexes mentioning the term, deduped and **sorted by content before `:max-lines` (40)
  cuts**, so which of what was scanned the model is shown is a function of the KB rather
  than of the order the knowledge arrived in.

  Rendered as **bare sentences**: the context is deliberately absent, because the answer
  shape has no context in it either and showing one invites the model to write one.  A
  rule keeps its `set/*Rule` wrappers, since that is how its direction and defeasibility
  are written.  An `exceptWhen` meta-sentex is left out — it names the rule it qualifies by
  raw handle, which is engine bookkeeping and not something to show a model, let alone ask
  it to imitate.

  **`:max-scan` (4000) is the cost bound, and it is the one thing here that is not a
  content choice.**  Content order is what a cap has to key on, so the sort must happen
  over everything the cut chooses between — which means fetching it.  Below the bound the
  page is therefore a function of the knowledge alone: the same sentences loaded in any
  order give the same lines.  At the bound it is a **sample**, and `scanned` decides which
  one — the term's earliest mentions, since what a sentence says cannot be known without
  fetching it and fetching all of them is the cost the bound refuses.  A page term
  mentioned more often than that is a term whose page is already a sample, so the scan
  stops and the answer says so: the metadata carries `:found` (distinct lines within the
  scan) and `:truncated?`, and `user-turn` writes both into the heading rather than
  letting 40 lines read as the whole of what is stored.  Ten record fetches per line shown
  is noise beside the model call this prompt is built for; a million is not."
  ([kb term] (stored-lines kb term {}))
  ([kb term {:keys [max-lines max-scan] :or {max-lines 40 max-scan 4000}}]
   ;; one past the bound, so the take says both how much was wanted and whether there
   ;; was more — the same reading `settle`'s budgeted sweeps take of theirs
   (let [raw   (scanned kb term (inc max-scan))
         cut?  (> (count raw) max-scan)
         lines (->> (cond-> raw cut? (subvec 0 max-scan))
                    (map (fn [s] {:handle (:id s)
                                  :sentence (selection/wrapped-sentence s)
                                  :context (:context s)}))
                    (remove #(some (fn [f] (= 'sentexHandle f))
                                   (tree-seq sequential? seq (:sentence %))))
                    (map #(assoc % :line (line-of (:sentence %))))
                    ;; **The context is the second half of the key, and has to be.**  One
                    ;; sentence can be stored in two contexts, and the dedup below keeps
                    ;; the first row of an equal-`:line` run.  Keyed on `:line` alone that
                    ;; run is in `scanned`'s handle order, so which context survives — and
                    ;; therefore `page-context`'s modal reading of the rows — would be a
                    ;; function of which load allocated the lower handle.  `[line context]`
                    ;; names a sentex uniquely, so no tie is left to fall anywhere.
                    ;; the context is keyed through the guarded printer: a context may be
                    ;; a NAT, and one keyed with `str` collapses under an ambient print bound
                    (sort-by (juxt :line (comp nm/print-key :context)))
                    (partition-by :line)
                    (map first))]
     (with-meta (vec (take max-lines lines))
       {:found (count lines) :truncated? cut?}))))

(defn page-context
  "The context new assertions are filed in: the caller's `:context` when given, else the
  context most of the page's own sentexes are in, else `CxUniverse`.

  A modal context is the honest default — a page about `penguin` whose sentexes sit in
  `CxOrganism` is a page about `CxOrganism` — and ties break on the context name so
  the choice cannot depend on arrival order.  The **vocabulary head is never chosen**: a term
  carries derived bookkeeping there (`(arity penguin 1)`, `(unary_predicate penguin)`) which can
  outnumber its definitional sentexes, and new domain knowledge does not belong in the
  context that defines the vocabulary.  Reported back by
  `vaelii.impl.llm.session/propose-page`, because which context knowledge lands in is a
  decision a reviewer must see."
  [rows given]
  (or given
      (->> (map :context rows)
           (remove nil?)
           (remove #(= inventory/head-context %))
           frequencies
           (sort-by (fn [[c n]] [(- n) (nm/print-key c)]))
           ffirst)
      'CxUniverse))

;; ---- the output contract ------------------------------------------------

(def output-schema
  "The JSON schema Ollama's `format` constrains decoding to — **the contract on this
  path**, unlike the edit path where it is an opt-in optimization.

  Measured: constrained decoding is what makes generation work at all on a local model.
  Models that answered a generation request with a markdown essay produce clean
  s-expressions under this schema, and the strongest coder model went from nothing usable
  to a full answer.  An **object per assertion**, never a bare string, so the sampler
  cannot choose its own line shape; `sentence` is one s-expression and carries **no
  context** — the caller supplies that."
  {"type" "object"
   "properties"
   {"assertions"
    {"type" "array"
     "description" "The new knowledge, one assertion per element. Omit anything already stored."
     "items" {"type" "object"
              "properties" {"sentence" {"type" "string"
                                        "description" (str "One s-expression and nothing else, "
                                                           "e.g. (genl penguin aquatic_bird) or "
                                                           "(implies (penguin ?x) (livesIn ?x Antarctica))")}
                            "strength" {"type" "string" "enum" ["monotonic" "default"]
                                        "description" (str "monotonic = known true of every such "
                                                           "thing; default = true by default and "
                                                           "defeasible. Omit for default.")}}
              "required" ["sentence"]}}
    "notes" {"type" "string"
             "description" "Anything you were unsure of, or vocabulary you had to invent. One or two sentences."}}
   "required" ["assertions"]})

(defn stored-heading
  "How many of the term's stored lines the prompt is showing — `40`, `40 of 137`, or
  `40 of more than 137`.

  A bare count of what is on screen reads as the whole of what is stored, and the model
  is asked in the same breath not to repeat anything already there.  Where the cut or
  `stored-lines`' scan bound bit, saying so is what keeps that instruction honest: a
  model shown a sample and told it is one writes about the gaps rather than assuming it
  has seen them.  Reads `stored-lines`' metadata, and answers the plain count for rows
  built without it."
  [rows]
  (let [{:keys [found truncated?]} (meta rows)
        shown (count rows)]
    (cond (nil? found)              (str shown)
          (and (= shown found)
               (not truncated?))    (str shown)
          truncated?                (str shown " of more than " found)
          :else                     (str shown " of " found))))

;; ---- the instruction half -----------------------------------------------

(def ^:private worked-example
  "The measured failure and its fix, shown side by side.

  Every model that writes usable s-expressions on this task fails the same way — it folds
  the claim into the predicate name — and the naming checks cannot catch it, because a
  unary snake_case functor is a legal type.  Telling the model to use arguments is not
  enough; showing the wrong answer next to the right one is what moves it."
  (str "### Example\n\n"
       "Page: `bat`. Instruction: flesh out how it gets around and where it lives.\n\n"
       "**Wrong** — every claim is folded into a new predicate name, so none of it joins "
       "anything already in the knowledge base:\n\n"
       "    (implies (bat ?x) (flies_at_night ?x))\n"
       "    (implies (bat ?x) (lives_in_caves ?x))\n"
       "    (implies (bat ?x) (capable_of_echolocation ?x))\n\n"
       "**Right** — the same three claims, said with predicates that already exist and "
       "arguments that carry the detail:\n\n"
       "    (genl bat mammal)\n"
       "    (implies (bat ?x) (flies ?x))\n"
       "    (implies (bat ?x) (activeAt ?x Night))\n"
       "    (implies (bat ?x) (livesIn ?x Cave))\n"
       "    (implies (bat ?x) (capableOf ?x Echolocation))"))

(def system-prompt
  "The instruction half of the page-scoped turn — static, because everything KB-specific
  rides in the user turn.

  It carries four things the model gets wrong without them: that a claim about a *kind*
  is a rule or a `genl` edge rather than a sentence with a loose variable, that the
  context is not the model's to write, that detail belongs in **arguments** and not in
  predicate names, and that the vocabulary on the card is there to be reused."
  (str
   "You add knowledge to a formal common-sense knowledge base. Every answer is a list of "
   "**assertions**, each one Lisp s-expression.\n\n"
   "You are given the term the reader is looking at, everything the knowledge base "
   "already says about it, the vocabulary its part of the type hierarchy licenses, and an "
   "instruction. Answer with assertions that are **new** — do not repeat a sentence that "
   "is already stored, and do not repeat yourself.\n\n"
   "**Write no context.** Every assertion is filed in the context named in the user turn; "
   "a context symbol in your answer is an error.\n\n"
   "The knowledge is about a **kind**, not about one individual, so it takes one of three "
   "shapes:\n\n"
   "    (genl <subtype> <supertype>)                        a taxonomy edge\n"
   "    (implies (<type> ?x) (<property> ?x))               a property of every such thing\n"
   "    (implies (<type> ?x) (<relation> ?x <Something>))   a relation to a named thing\n\n"
   "**`?x` is the only variable you may use.** A second variable is rejected: "
   "`(implies (penguin ?x) (parentOf ?x ?y))` says nothing, because nothing says what `?y` "
   "is. Name the other argument (`Antarctica`, `Fish`) or leave the assertion out — a "
   "relation whose other argument you cannot name is not a fact about the kind. A bare "
   "`(livesIn ?x Antarctica)` outside a rule is rejected too.\n\n"
   "Naming is mechanical and enforced:\n\n"
   "| role | form | example |\n"
   "|---|---|---|\n"
   "| predicate | camelCase | `livesIn`, `capableOf` |\n"
   "| individual | CapitalCamelCase | `Antarctica`, `Muffet` |\n"
   "| type | snake_case, used as a **unary** predicate | `aquatic_bird`, `physical_object` |\n\n"
   "**Detail belongs in arguments, never in a predicate name.** This is the one rule that "
   "matters most, because breaking it produces answers that look right and are useless: a "
   "predicate invented for one sentence can never join a rule or match another sentence. "
   "Write `(livesIn ?x Antarctica)`, not `(lives_in_antarctica ?x)`. Write "
   "`(bodyCovering ?x Feathers)`, not `(has_feathers ?x)`. Reuse a predicate from the card "
   "with its arguments; reach for a new name only when no argument of an existing "
   "predicate can carry the claim, and say so in `notes` when you do.\n\n"
   "**A card predicate under a new name is still a coined predicate.** If the card offers "
   "`flies`, the assertion is `(flies ?x)` — not `canFly`, `isFlying`, `hasFlight` or "
   "`capable_of_flight`. Before writing any predicate, look for it on the card under a "
   "plainer name: `can…`, `has…`, `is…` and `…able` prefixes are almost always something "
   "the card already has.\n\n"
   worked-example))

(defn user-turn
  "The volatile half: the page's term, its own stored sentences, the vocabulary card, the
  context new assertions land in, and the reader's instruction — instruction last, so it
  is the newest thing in the window.

  `opts` is passed through to `vaelii.impl.llm.inventory/inventory` and `render`
  (`:max-predicates`, `:max-types`, `:max-tokens`, …) and to `stored-lines`
  (`:max-lines`, `:max-scan`).  `:max-assertions` (24) caps what is asked for, which is
  what bounds the answer's length and so its latency.

  The stored block's heading is `stored-heading`'s rather than a bare count, so a capped
  page reads as capped."
  ([kb term rows context instruction] (user-turn kb term rows context instruction {}))
  ([kb term rows context instruction {:keys [max-assertions] :or {max-assertions 24}
                                      :as opts}]
   (let [inv (inventory/inventory kb term opts)]
     (str "## The page: " (selection/tick term)
          " (" (name (or (inventory/term-kind kb term) :unknown)) ")\n\n"
          "New assertions are filed in " (selection/tick context) ".\n\n"
          "## Already stored about " (selection/tick term)
          " (" (stored-heading rows) ")\n\n"
          (if (seq rows)
            (str/join "\n" (map :line rows))
            "_nothing yet_")
          "\n\n## Vocabulary you may use\n\n"
          (inventory/render inv opts)
          "\n\n## Instruction\n\n"
          (str/trim (str instruction))
          "\n\nAnswer with at most " max-assertions
          " assertions, every one of them new."))))

;; ---- reading the answer -------------------------------------------------

(defn assertion-entry
  "One read sentence -> the `[sentence context opts?]` entry `vaelii.core/edit!` takes,
  with the caller's context supplied.  `strength` rides across as
  `{:strength :monotonic}` when the model claimed the assertion is known-true; a default
  needs no opts, since that is `assert`'s own default."
  [sentence context strength]
  (cond-> [sentence context]
    (= :monotonic strength) (conj {:strength :monotonic})))

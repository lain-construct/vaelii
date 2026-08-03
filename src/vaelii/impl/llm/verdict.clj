;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.llm.verdict
  "What a reviewer needs to know about one proposed line, gathered in one place.

  A proposal is judged on **four independent axes**, and they are independent in the
  strong sense: a line can be admissible and still wrong-shaped, refused and still worth
  keeping once rewritten, admissible and shaped right and still quietly fragmenting the
  vocabulary.  Prose about a batch buries all four; a reviewer reads a gutter.

    :problems    what the KB itself says — `vaelii.core/check-edit`, typed
    :correction  what shape it should have been in — `vaelii.impl.llm.correct`
    :coined      what vocabulary it invents — `vaelii.impl.llm.inventory/coined`
    :confidence  how sure the correction is, which is a fifth thing only in the sense
                 that a rewrite the engine cannot decide is a decision handed back

  Each already exists; what did not is one call that runs all of them over one batch and
  lines the answers up **by entry**, so a caller renders a row rather than joining three
  reports by index.  Nothing here stores, checks a rewrite, or applies one: this is a
  reading of a proposal, and the proposal is still a proposal afterwards."
  (:require [vaelii.core :as v]
            [vaelii.impl.llm.correct :as correct]
            [vaelii.impl.llm.inventory :as inventory]))

(def verdict-rank
  "The four verdicts, worst first — the order a reviewer's eye should be drawn in.

  A line's verdict is the **worst** thing true of it, and only the leading glyph is
  ordered this way: every axis is still reported beside it, because ranking is for
  attention and not for hiding.

    :refused    the KB will not take it — nothing else about the line matters yet
    :uncertain  a rewrite exists but the engine cannot decide it (`:confidence :low`),
                so the judgement is the reader's and they have to be told.  A rewrite it
                *can* decide leaves the verdict alone: the line is admissible, the
                correction is a chip beside it, and demoting every restated line would
                make the worst rank the common one and say nothing
    :coins      it introduces vocabulary.  Third rather than harmless: the measured
                failure mode of this whole path is a batch accepted without being read,
                and coined vocabulary is what that costs
    :ok         admissible, in a shape the checker recognizes, in the KB's own words"
  [:refused :uncertain :coins :ok])

(defn- verdict-of
  [{:keys [problems correction coined]}]
  (cond
    (seq problems)                       :refused
    (= :low (:confidence correction))    :uncertain
    (seq coined)                         :coins
    :else                                :ok))

(defn coined-kind
  "Which of the two coining risks this is, by the **arity the sentence used it at** and
  not by its spelling: a one-place `:property` is a new claim about things, an n-place
  `:relation` is a new way for things to relate.  They are triaged differently — a
  property is usually a type or a predicate the ontology could absorb, a relation is a
  new edge in the graph that nothing else will ever join — so they are different chips.

  Arity rather than `:role` because the two can disagree and arity is the one that says
  what the sentence did: a bare lowercase word satisfies the predicate convention and the
  type convention alike, and `(swims penguin)` coins a property whichever way `term-role`
  reads the name."
  [{:keys [arity]}]
  (if (= 1 arity) :property :relation))

(defn verdicts
  "One verdict per `:add` entry of `batch`, in batch order:

    {:index :entry :sentence :context
     :problems   [{:type :message …}]   ; empty when the KB would take it
     :correction {:to :alternatives :rule :rules :confidence :why} | nil
     :coined     [{:predicate :arity :role :kind} …]
     :verdict    :refused | :uncertain | :coins | :ok}

  `opts :problems` takes a `check-edit` result already computed — `propose-page` runs
  one to decide its own status, and checking a batch twice to render it is a whole
  second pass of `assert`'s chain for an answer already in hand.  Without it, this runs
  the check itself, so a caller with nothing precomputed still gets a full reading.

  A `:remove` entry has no verdict here: removal is checked (`:unknown-handle`) but has
  no sentence to correct and coins nothing, and the generating paths never remove."
  ([kb batch] (verdicts kb batch {}))
  ([kb batch {:keys [problems]}]
   (let [entries (vec (:add batch))
         probs   (or problems (v/check-edit kb batch))
         by-i    (group-by :index (filter #(= :add (:in %)) probs))
         corr    (group-by :index (:corrections (correct/corrections kb entries)))
         coins   (group-by :index (:coined (inventory/coined kb batch)))]
     (vec (for [[i entry] (map-indexed vector entries)
                :let [[sentence context] entry
                      v {:index i
                         :entry entry
                         :sentence sentence
                         :context context
                         :problems (vec (by-i i))
                         :correction (first (corr i))
                         :coined (mapv #(assoc % :kind (coined-kind %)) (coins i))}]]
            (assoc v :verdict (verdict-of v)))))))

(defn shapes
  "Every shape a proposed line could take, in the order a reviewer should meet them: the
  sentence **as the model wrote it** first, then the correction's rewrite, then its
  alternatives.

  The original leads because it is what was actually proposed and a reviewer must be able
  to get back to it; the rewrite follows because when there is one it is usually right.
  Numbering is by position, so a caller can offer them as `1`, `2`, `3` and a choice is
  one keystroke.  A line with no correction has exactly one shape, and nothing to choose."
  [sentence correction]
  (into [sentence]
        (concat (when (:to correction) [(:to correction)])
                (:alternatives correction))))

(defn chosen-verdict
  "The verdict of the shape a reviewer has settled on, judged **in light of where it came
  from**: `:problems` and `:coined` are of the chosen sentence, because that is the one
  that would be stored, while `:correction` is the one that produced the choice.

  Both halves matter and neither is derivable from the other.  Re-deriving a correction
  from a rewrite would report nothing (`correct` does not re-check its own output, by
  contract) and the line would look as though it had never been restated — erasing the
  one thing a reviewer needs in order to change their mind.  Keeping the original's
  problems instead would be worse: it would grade a sentence nobody is proposing any
  more."
  [kb sentence context correction]
  (let [batch {:add [[sentence context]] :remove []}
        v {:sentence sentence
           :context context
           :problems (vec (v/check-edit kb batch))
           :correction correction
           :coined (mapv #(assoc % :kind (coined-kind %))
                         (:coined (inventory/coined kb batch)))}]
    (assoc v :verdict (verdict-of v))))

;; ---- one line, under review ---------------------------------------------

(defn acceptable?
  "May a reviewer store the shape this line is on?

  No, when the correction is **report-only** — it found something it cannot repair (which
  argument of an over-long sentence is surplus is not inferable) and offers no shape to
  store instead.  `correct/apply-correction` is the authority rather than a rule spelled
  out again here: it answers nil for exactly that case, and accepting the line would
  store the sentence the correction was warning about."
  [{:keys [correction]}]
  (or (nil? correction) (some? (correct/apply-correction correction))))

(defn- reviewing
  "The review row for `sentence` in `context` given its `correction`, the 1-based shape
  `n` the reviewer is on, and `known` — the verdict of the sentence as written, when a
  caller already has it.  `n` out of range is clamped rather than refused: it arrives
  from a keystroke."
  [kb sentence context correction n known]
  (let [opts   (shapes sentence correction)
        n      (min (max 1 (or n (if (:to correction) 2 1))) (count opts))
        chosen (nth opts (dec n))
        row    {:from sentence :context context :shapes opts :n n :chosen chosen
                :correction correction
                :verdict (if (and known (= chosen sentence))
                           known
                           (chosen-verdict kb chosen context correction))}
        report-only? (not (acceptable? row))]
    (assoc row
           :report-only? report-only?
           ;; **is there anything here to store?** — two ways there is not, and a
           ;; reviewer needs them told apart: a correction that found something it
           ;; cannot repair, and a shape the KB itself refuses.  Either way the row
           ;; offers no accept, which is also what stops one refused line from poisoning
           ;; a batch that is applied whole or not at all.
           :storable? (and (not report-only?)
                           (empty? (:problems (:verdict row)))))))

(defn review
  "One line under review: what the model wrote (`:from`), every shape it could take
  (`:shapes`), which one the reviewer is on (`:n` / `:chosen`), the verdict of that shape
  (`:verdict`), whether there is anything here to store (`:storable?`), and whether the
  reason there is not is a correction that could only report (`:report-only?`).

  **The rewrite leads when there is one** (`:n` defaults to 2): a correction exists
  because the sentence as written says the right thing in the wrong shape, and leading
  with the wrong one would put the keystroke on the common case.  The original stays
  shape 1, so getting back to it costs a keystroke too — which is the point, since
  `correct` deliberately refuses to decide between them."
  ([kb sentence context] (review kb sentence context nil))
  ([kb sentence context n]
   (reviewing kb sentence context (correct/correction kb sentence) n nil)))

(defn review-of
  "The same row from a verdict `verdicts` already computed — the batch case, which has
  both the correction and the sentence's own verdict in hand and re-derives neither."
  [kb {:keys [index sentence context correction] :as verdict}]
  (assoc (reviewing kb sentence context correction nil verdict) :index index))

(defn summary
  "How many lines fell under each verdict — `{:refused n :uncertain n :coins n :ok n}`,
  every key present so a caller can render a fixed row of counts rather than a variable
  one."
  [verdicts]
  (merge (zipmap verdict-rank (repeat 0))
         (frequencies (map :verdict verdicts))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.host.lines
  "The browser editor's line format: a stored sentex as the sentence its author would
  type back in.

  The editor seeds its textarea with these sentences and diffs the text it gets back
  against them **by content**, so a sentence spelled two ways would turn an untouched line
  into a retract plus an assert of the same fact.  It lives here rather than in the
  browser because spelling a rule's wrappers reads the rule record's slots
  (`rules/rewrap-sentex`), and the browser requires no `vaelii.impl` namespace."
  (:require [vaelii.core :as v]
            [vaelii.impl.rules :as rules]))

(defn wrapped-sentence
  "A sentex's editable sentence: the readable sentence (the author's variable names),
  and for a rule the `set/*` wrappers its record holds spelled back around it
  (`rules/rewrap-sentex`) so a re-assert preserves them.  A rule's `exceptWhen`
  / `unknown` guard lives in a separate meta-sentex and is **not** carried, so editing a
  guarded rule drops its guard — the browser's editor hint says so."
  [s]
  (let [base (v/readable-sentence s)]
    (cond
      (nil? (:antecedent s)) base
      ;; a backward rule is spelled with its wrapper too, so the line shows the direction
      ;; a bare `implies` would leave the reader to know
      (and (= :derive (:effect s)) (= #{:backward} (:engines s)))
      (cond->> (list 'set/backwardRule base) (:defeasible s) (list 'set/defaultRule))
      :else (rules/rewrap-sentex base s))))

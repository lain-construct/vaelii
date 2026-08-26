;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.regen-client
  "`lein regen-client` — rewrite the client's wrapper sections from the daemon's op
  table.

  **The op table is the single source, and the client cannot read it.**
  `vaelii.impl.serve/ops` names a `vaelii.core` fn per op; `vaelii.impl.client` runs no
  engine and requires neither, which is the whole of what \"a client is a thin thing\"
  means — so the two cannot be joined at load time by a macro without dragging the
  engine, jetty and reitit onto the classpath of a namespace whose point is not needing
  them. They are joined here instead, at build time: this reads the table, resolves each
  op in `vaelii.core`, and writes one wrapper per op between two markers in each file.

  Everything outside the markers is hand-written and is kept: the connection, `call`,
  `health`, the change feed (which is `serve/feed-ops`, not a `vaelii.core` fn) and the
  deprecated spellings. In `vaelii.client` a hand-written wrapper also **wins** — an op
  whose name is already defined above the marker is skipped, so prose written for one
  survives a regeneration.

  **A red `client_surface_test` is the point, not the cost.** The test compares each
  file against what this would write now, so an op added to `serve/ops` fails the suite
  until somebody runs this and reads the diff — the same bargain the three goldens make
  (`vaelii.api-surface-test`). Regenerating is how a deliberate change is recorded, never
  how a red is silenced."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [vaelii.impl.serve :as serve]))

(def begin-marker
  "The line the generated section starts after.  Matched whole, so a section boundary
  cannot drift by whitespace."
  ";; ---- generated: one wrapper per daemon op, from serve/ops ---------------")

(def end-marker
  "The line the generated section ends before."
  ";; ---- end generated ------------------------------------------------------")

;; ---- reading the op table ------------------------------------------------

(defn core-var
  "The `vaelii.core` var op `op` runs, or nil.

  The daemon's op keywords drop the `!` a destructive fn carries — `:retract` runs
  `retract!`, `:edit` runs `edit!` — so both spellings are tried, bare first.  No op
  resolves under both, and `client_surface_test` holds that: an op whose two spellings
  were live vars would generate a wrapper for whichever this tried first."
  [op]
  (or (ns-resolve 'vaelii.core (symbol (name op)))
      (ns-resolve 'vaelii.core (symbol (str (name op) "!")))))

(defn wrapper-name
  "The symbol a wrapper for `op` is spelled with — `vaelii.core`'s own, bare or
  `!`-marked exactly as it spells it, never the op keyword's."
  [op]
  (:name (meta (core-var op))))

(defn signatures
  "The wrapper's parameter lists for `op`: `vaelii.core`'s, with the leading `kb`
  replaced by `conn` — the network mirror of the explicit-KB API — shortest first.

  A `serve/kbless-ops` op has no leading `kb` to replace, so `conn` is prepended to the
  whole list instead: the daemon supplies a KB to every row of its table and those rows
  drop it, which means the fn's first parameter is an argument the caller sends."
  [op]
  (let [drop-kb (if (serve/kbless-ops op) identity rest)]
    (->> (:arglists (meta (core-var op)))
         (map #(vec (cons 'conn (drop-kb %))))
         (sort-by count)
         vec)))

;; ---- rendering -----------------------------------------------------------

(def ^:private abbreviations
  "Full stops that do not end a sentence.  Two, because two docstrings have one and a
  first sentence cut at `e.g.` reads as a truncation rather than as a summary."
  #{"e.g." "i.e."})

(defn- first-sentence
  "The first sentence of `doc`, whitespace-collapsed — enough to say what the wrapper is
  for, with `vaelii.core`'s own var holding the rest.  The whole first paragraph is a
  page for the larger doors."
  [doc]
  (let [p (-> (first (str/split (or doc "") #"\n\s*\n"))
              (str/replace #"\s+" " ")
              str/trim)
        n (count p)]
    (loop [i 0]
      (cond
        (>= i n) p
        (and (= \. (nth p i))
             (or (= (inc i) n) (= \space (nth p (inc i))))
             (not (abbreviations (subs p (max 0 (- i 3)) (inc i)))))
        (subs p 0 (inc i))
        :else (recur (inc i))))))

(defn- wrap-doc
  "`doc` as docstring lines under a 2-space indent, wrapped so no line runs past 92
  columns.  Greedy, and deterministic on the input, which is what makes the file this
  writes byte-stable across runs."
  [doc]
  (let [width 88]
    (->> (str/split doc #" ")
         (reduce (fn [lines w]
                   (let [cur (peek lines)]
                     (if (and cur (<= (+ (count cur) 1 (count w)) width))
                       (conj (pop lines) (str cur " " w))
                       (conj lines w))))
                 [])
         (map-indexed (fn [i line] (if (zero? i) line (str "  " line)))))))

(defn- defn-form
  "One wrapper as text: `(defn <name> \"<doc>\" <arities>)`, formatted the way `cljfmt`
  would leave it — a single-arity fn writes its parameter vector and body flat, a
  multi-arity one writes one parenthesized arity per line."
  [nm doc sigs body-of]
  (let [;; the doc is copied out of a docstring and goes back into one, so the two
        ;; characters a string literal cannot hold bare are escaped here — a core
        ;; docstring quoting a question (`describe`'s) is otherwise an unreadable file
        doc-lines (wrap-doc (str/escape doc {\\ "\\\\" \" "\\\""}))
        head      (str "(defn " nm "\n  \"" (str/join "\n" doc-lines) "\"\n")]
    (if (= 1 (count sigs))
      (let [sig (first sigs)]
        (str head "  " (pr-str sig) "\n  " (body-of sig) ")\n"))
      (str head
           (str/join "\n" (map (fn [sig] (str "  (" (pr-str sig) " " (body-of sig) ")"))
                               sigs))
           ")\n"))))

(defn- direct-body
  "`vaelii.impl.client`'s body: the op and its args, over `call`."
  [op]
  (fn [sig] (str "(call conn " op " [" (str/join " " (rest sig)) "])")))

(defn- delegate-body
  "`vaelii.client`'s body: the same call, one delegation deep, so the shim stays a shim."
  [nm]
  (fn [sig] (str "(c/" nm " " (str/join " " sig) ")")))

(defn- section
  "The generated section's text for one target — every op it is to cover, sorted by the
  name the wrapper carries so the file is stable under a re-run."
  [ops body]
  (->> ops
       (sort-by (comp str wrapper-name))
       (map (fn [op]
              (let [nm (wrapper-name op)]
                (defn-form nm
                  (first-sentence (:doc (meta (core-var op))))
                  (signatures op)
                  (case body
                    :direct   (direct-body op)
                    :delegate (delegate-body nm))))))
       (str/join "\n")))

;; ---- the two files -------------------------------------------------------

(def targets
  "`[path body skip-hand-written?]` per generated file, in the order they are written.

  `vaelii.client` skips an op whose wrapper is already hand-written above the marker:
  the shim is where a reader looks first, so prose written for `why` or `belief-status`
  is worth more than a generated line, and the coverage claim is the same either way —
  `client_surface_test` asks whether a wrapper exists, not who wrote it."
  [{:path "src/vaelii/impl/client.clj" :body :direct   :skip-hand-written? false}
   {:path "src/vaelii/client.clj"      :body :delegate :skip-hand-written? true}])

(defn- defined-names
  "The names `text` defines with a top-level `defn`."
  [text]
  (set (map second (re-seq #"(?m)^\(defn (\S+)" text))))

(defn rendered
  "The whole text of `target`'s file as this generator would write it now — the
  hand-written halves as they stand, with the section between the markers rebuilt."
  [{:keys [path body skip-hand-written?]}]
  (let [text   (slurp (io/file path))
        b-at   (str/index-of text begin-marker)
        e-at   (str/index-of text end-marker)
        _      (when-not (and b-at e-at)
                 (throw (ex-info (str path " carries no generated section — the two"
                                      " marker lines are what this rewrites between")
                                 {:path path})))
        before (subs text 0 (+ b-at (count begin-marker)))
        after  (subs text e-at)
        held   (if skip-hand-written? (defined-names before) #{})
        ops    (remove #(contains? held (str (wrapper-name %))) (keys serve/ops))]
    (str before "\n\n" (section ops body) "\n" after)))

(defn write!
  "Rewrite every target in place.  Returns the paths whose bytes changed."
  []
  (into []
        (keep (fn [{:keys [path] :as target}]
                (let [next-text (rendered target)]
                  (when (not= next-text (slurp (io/file path)))
                    (spit (io/file path) next-text)
                    path))))
        targets))

(defn -main [& _]
  (let [changed (set (write!))]
    (doseq [{:keys [path]} targets]
      (println (str "  " (if (changed path) "✓ rewritten" "· unchanged") "  " path)))
    (println (str (count (keys serve/ops)) " ops, one wrapper each. Review the diff, and"
                  " commit it in the SAME commit as the change that moved it."))
    (shutdown-agents)
    (System/exit 0)))

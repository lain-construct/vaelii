;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.doc-examples-test
  "The fenced `clojure` examples in `README.md` and `docs/*.md`, evaluated.

  Nothing else evaluates them.  `scripts/check-doc-drift.py` reads the pages as text,
  and its E13 asks only whether a block *balances* — so an example may name a fn that
  no longer exists, pass a map key the door now refuses, or print a value the engine
  stopped producing, and read as current for as long as nobody pastes it.  This
  namespace pastes it.

  **The marker is opt-in, and the exception list is why.**  A block runs here when its
  fence info string carries `run`:

      ```clojure run

  Almost every block in the tree is a *fragment* — KB sentences written as bare
  s-expressions (`(genl dog animal)`), a signature listing, a map showing the shape of
  a result, a call over a `kb` the surrounding prose introduced.  None of those is a
  program, and none can be made one without rewriting the page into a transcript.  The
  whole-program blocks are a handful.  So opt-out would need a marker on nearly every
  block in `docs/` and opt-in needs one on a handful, which is the same rule read from
  the shorter end.

  Two consequences follow from opt-in and are checked below rather than trusted: a
  block that reaches past its own stores carries no marker — a model provider, a
  server, or the process-wide log dial — so `lein test` still makes no network call
  (`CONTRIBUTING.md` §5) and no page's demonstration outlives its own block; and a
  marker the runner does not know is a typo rather than a silent skip.

  **`=>` comments are checked.**  A comment that follows a form and whose text begins
  with `=>` states that form's value:

      (v/isa? kb 'Muffet 'animal)   ;=> true (via genl — no context arg)

  The rule, which is what makes the loose ones harmless: read **one** EDN form from
  the text after the arrow.  If what is left is empty, or is a `(` opening a
  parenthetical remark, an em-dash aside, or a further comment, that form is the
  expectation and is compared with `=`.  Anything else — prose (`;=> derived, placed
  in CxNaturalWorld`), an elision (`…`, `...`), text that does not read — is a
  sketch of a result rather than a claim about one, and is left alone.

  **Each block gets its own stores.**  `open-kb`'s `:space` defaults to 0, which is
  the process-wide in-RAM store every other default-space KB shares, so a block that
  opens `(v/open-kb {})` would land on it and read another block's facts.  The runner
  rewrites every `:space` a block names — including the absent one — to a value of its
  own, one per *distinct* space the block names, so a block demonstrating that two KBs
  share a store still demonstrates it.  The key is a namespaced vector, so it collides
  with no number a test uses.

  The scratch namespace a block runs in has `clojure.core` referred and `v` /
  `starter` aliased, exactly as the README's own first line requires them; a block
  needing anything else requires it itself, in the block, where a reader can see it."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is]]
            [vaelii.core :as v]
            [vaelii.starter])
  (:import (java.io File PushbackReader StringReader)))

;; ---- the pages, and the blocks in them ----------------------------------

(defn- doc-files
  "`README.md` and every page under `docs/`, in a fixed order.  Paths are relative,
  like every other source scan in the suite: the runner's cwd is the project root."
  []
  (cons (io/file "README.md")
        (->> (file-seq (io/file "docs"))
             (filter #(.isFile ^File %))
             (filter #(str/ends-with? (.getName ^File %) ".md"))
             (sort-by #(.getName ^File %)))))

(defn- fenced-blocks
  "Every ```` ``` ```` block in `text` as `{:file :line :info :body}`, `:line` being the
  fence's own line.  The closing fence must be bare, which is what the pages write."
  [file text]
  (loop [lines (map-indexed (fn [i l] [(inc i) l]) (str/split-lines text))
         open  nil
         buf   []
         out   []]
    (if-let [[n line] (first lines)]
      (cond
        (and (nil? open) (str/starts-with? line "```"))
        (recur (rest lines) {:file file :line n :info (str/trim (subs line 3))} [] out)

        (and open (= "```" (str/trim line)))
        (recur (rest lines) nil [] (conj out (assoc open :body (str/join "\n" buf))))

        open  (recur (rest lines) open (conj buf line) out)
        :else (recur (rest lines) open buf out))
      out)))

(defn- clojure-blocks
  "Every fenced block whose info string names `clojure`, across all the pages."
  []
  (for [^File f (doc-files)
        blk     (fenced-blocks (.getPath f) (slurp f))
        :when   (= "clojure" (first (str/split (str/trim (:info blk)) #"\s+")))]
    blk))

(def ^:private known-markers
  "The info-string words this runner understands, beyond the language itself."
  #{"run"})

(defn- markers [blk]
  (set (rest (str/split (str/trim (:info blk)) #"\s+"))))

(defn- marked? [blk] (contains? (markers blk) "run"))

;; ---- reading a block into forms, with the comment that follows each ------

(defn- comment-after
  "Consume whitespace and whole-line comments up to the next form, returning the
  comment text with each leading `;` dropped and the lines joined.  A `=>` comment
  written on the line the form ends on, and one written under it, read the same."
  [^PushbackReader r]
  (loop [acc []]
    (let [c (.read r)]
      (cond
        (neg? c) (str/join " " acc)
        (Character/isWhitespace (char c)) (recur acc)
        (= \; (char c))
        (let [sb (StringBuilder.)]
          (loop []
            (let [d (.read r)]
              (when (and (not (neg? d)) (not= \newline (char d)))
                (.append sb (char d))
                (recur))))
          (recur (conj acc (str sb))))
        :else (do (.unread r c) (str/join " " acc))))))

(defn- has-ellipsis?
  "Is `x` a sketch — does an elision appear anywhere in it?"
  [x]
  (boolean (some #(and (symbol? %) (contains? #{"…" "..."} (name %)))
                 (tree-seq coll? seq x))))

(defn- expectation
  "The value a `=>` comment claims, or nil when the comment is prose or a sketch."
  [text]
  (when-let [after (second (re-find #"^[;\s]*=>\s*(.*)$" (or text "")))]
    (let [r (PushbackReader. (StringReader. after))
          v (try (edn/read {:eof ::eof} r) (catch Exception _ ::unreadable))]
      (when-not (contains? #{::eof ::unreadable} v)
        (let [remainder (str/trim (slurp r))]
          (when (and (not (has-ellipsis? v))
                     (or (str/blank? remainder)
                         (some #(str/starts-with? remainder %) ["(" "—" "--" ";"])))
            {:value v}))))))

(defn- forms-of
  "`[{:form … :expectation …}]` for `body`, one entry per top-level form.  A block that
  does not read throws, which for a marked block is the finding."
  [body]
  (binding [*read-eval* false]
    (let [r (PushbackReader. (StringReader. body))]
      (loop [out []]
        (let [f (read {:eof ::eof} r)]
          (if (= f ::eof)
            out
            (recur (conj out {:form f :expectation (expectation (comment-after r))}))))))))

(defn- expectations-of
  "Only the `=>` comments that state a value, in order.  Read from the text, so the
  number of them does not depend on how far a failing block got."
  [body]
  (into [] (keep :expectation) (forms-of body)))

;; ---- running one block ---------------------------------------------------

(def ^:private space-counter (atom 0))

(defn- run-block
  "Evaluate `body` in a scratch namespace on stores of its own.  Returns
  `{:values [v …] :error t?}` — one value per `=>` expectation, in order, and the
  throwable that stopped the block if one did."
  [body]
  (let [open   v/open-kb
        spaces (atom {})
        space  (fn [named]
                 (get (swap! spaces update named
                             #(or % [::doc-example (swap! space-counter inc)]))
                      named))
        nsym   (gensym "vaelii.doc-example")
        values (atom [])]
    (create-ns nsym)
    (try
      (with-redefs [v/open-kb (fn ([] (open {:space (space ::unnamed)}))
                                ([opts] (open (assoc opts :space (space (:space opts ::unnamed))))))]
        (binding [*ns* (the-ns nsym)]
          (refer 'clojure.core)
          (alias 'v 'vaelii.core)
          (alias 'starter 'vaelii.starter)
          (doseq [{:keys [form expectation]} (forms-of body)]
            (let [value (eval form)]
              (when expectation (swap! values conj value))))))
      {:values @values}
      (catch Throwable t {:values @values :error t})
      (finally (remove-ns nsym)))))

(defn- describe [^Throwable t]
  (str (.getSimpleName (class t)) ": " (.getMessage t)))

;; ---- the tests -----------------------------------------------------------

(deftest a-marker-the-runner-does-not-know-is-a-typo
  ;; `​```clojure runn` would otherwise be a block that silently never runs, which is
  ;; the failure mode opt-in has and opt-out does not.  Naming the vocabulary is what
  ;; buys it back.
  (let [unknown (for [blk  (clojure-blocks)
                      word (markers blk)
                      :when (not (contains? known-markers word))]
                  (str (:file blk) ":" (:line blk) "  " (pr-str word)))]
    (is (empty? unknown)
        (str "an unknown word in a ```clojure fence's info string; the runner knows "
             (pr-str known-markers) ":\n" (str/join "\n" unknown)))))

(deftest a-block-with-reach-beyond-its-own-stores-carries-no-marker
  ;; Three things a marked block may not do, refused here rather than discovered by a
  ;; suite that hangs on a socket or runs the rest of its namespaces at `:trace`:
  ;; `docs/llm.md` is every model example, `vaelii.client` is the wire client (whose
  ;; examples all want a server), and `set-log-level` is the one dial in the API that
  ;; moves the **process** rather than a KB, with no call that puts it back.
  (let [reaching (for [blk   (clojure-blocks)
                       :when (and (marked? blk)
                                  (or (str/ends-with? (:file blk) "llm.md")
                                      (str/includes? (:body blk) "vaelii.client")
                                      (str/includes? (:body blk) "set-log-level")))]
                   (str (:file blk) ":" (:line blk)))]
    (is (empty? reaching)
        (str "a block that reaches a provider, a server or the process-wide log dial "
             "carries `run`:\n" (str/join "\n" reaching)))))

(deftest every-marked-doc-example-runs
  (let [blocks (filter marked? (clojure-blocks))]
    (is (seq blocks)
        "no ```clojure run block was found — the scan reads relative paths, so this is
         what it says when the runner's cwd is not the project root")
    (doseq [{:keys [file line body]} blocks]
      (let [expected (expectations-of body)
            {:keys [values error]} (run-block body)]
        (is (nil? error)
            (str file ":" line " — the example does not run: "
                 (when error (describe error))))
        (dotimes [i (count expected)]
          (let [want (:value (nth expected i))
                got  (get values i ::the-block-stopped-first)]
            (is (= want got)
                (str file ":" line " — a `=>` comment says " (pr-str want)))))))))

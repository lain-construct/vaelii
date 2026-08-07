;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.config-surface-test
  "The configuration surface, pinned: every `VAELII_*` environment variable and every
  `vaelii.*` JVM system property the build reads, collected from the sources at runtime
  and frozen against `test/golden/config-surface.edn`.

  **Why a golden and not a roster.** `kb/opt-keys` and its eleven neighbours are public
  *because* a caller should be able to ask \"is this a real option?\", and a caller that
  can ask does not have to find out from a wrong answer.  Nothing outside a map carries
  that promise: a misspelt environment variable is unset, a renamed one is unset, and
  the process runs on the default reporting nothing.  So the names are pinned here
  instead, and the pin is what makes a rename a failing test rather than a support
  ticket — deployment scripts, systemd units and `docs/operations.md` reference them by
  name.

  ## On failure

  - **A REMOVED name is breaking.**  Restore it, or take the CHANGELOG entry:
    CONTRIBUTING §3.8 files a renamed or deleted switch as **Breaking**, with the
    migration line naming the new spelling.
  - **An ADDED name is not noise.**  Run `regenerate-golden!` and commit the golden in
    the same commit as the switch.  This is the half that gets waived, and it is the
    half that makes the golden a record rather than a ratchet: a new name nobody wrote a
    table row for is how a surface grows six undocumented switches, one at a time.

  ## What the scan reads

  Four forms over `src/`, `test/`, `bench/`, `project.clj` and `scripts/*.sh`, all
  normalized to the name as it is spelled where it is set:

  - `(System/getenv \"VAELII_…\")` — a literal environment variable.
  - `(System/getProperty \"vaelii.…\")` — a literal system property.
  - `(prop-bool \"…\")` / `prop-long` / `prop-double` / `prop-enum`, alias-qualified or
    not — `vaelii.impl.config`'s readers, which take the name as an **argument**.  Ten
    of the eighteen properties reach `System/getProperty` only this way, so a scanner
    built on the two literal forms alone finds eight of them and reports itself
    complete.  `the-scan-catches-the-helper-form` is the test that says so.
  - `${VAELII_…}` in a shell script.  One regex over `.sh` text rather than a shell
    parser, and it is enough because the name carries its own prefix.

  A name is an environment variable when it is spelled in caps and a system property
  otherwise — the same rule `config/raw` dispatches on, and nothing in the tree names a
  switch both ways.

  This namespace spells the forms in order to test them, so it is the one source file
  the scan skips: its own matches are not the tree's."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.pprint :as pprint]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.test :refer [deftest is testing]])
  (:import [java.io File]))

(def ^:private golden-file "test/golden/config-surface.edn")
(def ^:private doc-file "docs/operations.md")
(def ^:private self-file "test/vaelii/config_surface_test.clj")

;; ---- the scan -----------------------------------------------------------

(def clj-forms
  "The three Clojure spellings of a read, each capturing the switch's name.  The helper
  form is the third and it is the one worth having: `prop-long` takes the name as an
  argument, so the property it reads appears in no `System/getProperty` literal
  anywhere."
  [#"System/getenv\s+\"([A-Z][A-Z0-9_]*)\""
   #"System/getProperty\s+\"(vaelii\.[a-z0-9.-]+)\""
   #"\((?:[a-z][\w.-]*/)?prop-(?:bool|long|double|enum)\s+\"([A-Za-z][\w.-]*)\""])

(def shell-form
  "`${VAELII_…}` in a shell script.  Deliberately prefix-anchored: a regex for every
  `${CAPS}` collects each script's own local variables, and telling those from a knob
  needs a shell parser."
  #"\$\{(VAELII_[A-Z0-9_]+)")

(def ^:private not-a-switch
  "Names the scan finds that configure nothing, each with why.  Explicit rather than a
  pattern — a pattern excusing `vaelii.test.*` would excuse a real switch the day
  somebody names one `vaelii.test.mode`."
  {"vaelii.test.bool"
   (str "config_test's probe for `prop-bool` itself. The reader takes the name as an "
        "argument, so exercising it needs a name; nothing reads this one.")})

(defn- clj-sources []
  (->> (concat (mapcat (comp file-seq io/file) ["src" "test" "bench"])
               [(io/file "project.clj")])
       (filter #(.isFile ^File %))
       (filter #(str/ends-with? (.getPath ^File %) ".clj"))
       (remove #(= self-file (.getPath ^File %)))))

(defn- shell-sources []
  (->> (file-seq (io/file "scripts"))
       (filter #(.isFile ^File %))
       (filter #(str/ends-with? (.getPath ^File %) ".sh"))))

(defn scan-text
  "Every switch `text` names under `forms`, as a set.  Separated from the file walk so
  the scanner is testable on a string — which is how the helper form is asserted without
  planting a fake switch in a source file."
  [forms text]
  (into #{} (mapcat (fn [rx] (map second (re-seq rx text)))) forms))

(defn- sites-in
  "`{name [\"path:line\" …]}` for one file, in line order."
  [forms ^File f]
  (let [path (.getPath f)]
    (->> (str/split-lines (slurp f))
         (map-indexed (fn [i line] [(inc i) line]))
         (reduce (fn [acc [n line]]
                   (reduce (fn [acc nm] (update acc nm (fnil conj []) (str path ":" n)))
                           acc
                           (mapcat (fn [rx] (map second (re-seq rx line))) forms)))
                 {}))))

(defn surface-sites
  "`{name [\"path:line\" …]}` over the whole tree, the names that configure nothing
  dropped."
  []
  (apply dissoc
         (apply merge-with into
                (concat (map (partial sites-in clj-forms) (clj-sources))
                        (map (partial sites-in [shell-form]) (shell-sources))))
         (keys not-a-switch)))

(defn- env-var? [nm] (some? (re-find #"^[A-Z]" nm)))

(defn current-surface
  "`{:env-vars #{…} :properties #{…}}` as the sources read today."
  []
  (let [names (keys (surface-sites))]
    {:env-vars   (into (sorted-set) (filter env-var?) names)
     :properties (into (sorted-set) (remove env-var?) names)}))

(defn regenerate-golden!
  "Rewrite `test/golden/config-surface.edn` from the sources.  Call it from a REPL after
  a **deliberate** change to the surface — adding a switch, or removing one with the
  CHANGELOG entry beside it — and commit the golden in that same commit."
  []
  (let [{:keys [env-vars properties]} (current-surface)]
    (spit golden-file
          (str ";; Frozen configuration surface — every VAELII_* environment variable\n"
               ";; and vaelii.* system property the build reads.\n"
               ";; Regenerate: (vaelii.config-surface-test/regenerate-golden!), and read\n"
               ";; that namespace's docstring first — a removed name is a breaking change.\n"
               ";; Each one has a row in docs/operations.md, which the same test checks.\n"
               (with-out-str
                 (pprint/pprint {:env-vars (vec env-vars)
                                 :properties (vec properties)}))))))

(defn- golden []
  (let [{:keys [env-vars properties]} (edn/read-string (slurp golden-file))]
    {:env-vars (set env-vars) :properties (set properties)}))

;; ---- the pin, both ways -------------------------------------------------

(deftest the-configuration-surface-is-frozen
  (let [current (current-surface)
        frozen  (golden)]
    (doseq [k [:env-vars :properties]]
      (let [removed (set/difference (frozen k) (current k))
            added   (set/difference (current k) (frozen k))]
        (is (empty? removed)
            (str "BREAKING: " (name k) " removed or renamed: " (sort removed)
                 ". Deployment scripts, systemd units and docs/operations.md name"
                 " these — restore them, or take the CONTRIBUTING §3.8 Breaking entry"
                 " with the migration line, and regenerate the golden in that commit."))
        (is (empty? added)
            (str "New " (name k) ": " (sort added) " — this extends the published"
                 " surface. Run (vaelii.config-surface-test/regenerate-golden!), give"
                 " each one a row in docs/operations.md, and commit the golden in this"
                 " same commit."))))))

(deftest the-scan-catches-the-helper-form
  ;; The assertion legacy's version of this scanner did not have, and the five switches
  ;; it therefore missed are the argument for it: a reader that takes the name as an
  ;; argument shadows the literal the scan looks for.
  (testing "a switch read through a config helper is found"
    (doseq [form ["(prop-long \"vaelii.disk.nonsense\" 1 0 nil)"
                  "(config/prop-bool \"vaelii.disk.nonsense\" false)"
                  "(prop-double \"vaelii.disk.nonsense\" 0.5 0 1)"
                  "(prop-enum \"VAELII_NONSENSE\" {} nil \"a nonsense\")"]]
      (is (seq (set/intersection #{"vaelii.disk.nonsense" "VAELII_NONSENSE"}
                                 (scan-text clj-forms form)))
          (str "the scan missed " form))))
  (testing "and the helper form is the ONLY way most of the store's switches are read"
    ;; So a scanner that dropped the third regex would lose these ten and report a
    ;; complete surface: this is the assertion that fails when somebody simplifies it.
    ;; `src/` alone, because a test that saves and restores a property around a case
    ;; names it literally without reading it as configuration.
    (let [literal-only (into #{}
                             (comp (filter #(str/starts-with? (.getPath ^File %) "src/"))
                                   (mapcat #(scan-text (subvec clj-forms 0 2) (slurp %))))
                             (clj-sources))]
      (doseq [nm ["vaelii.disk.auto-compact" "vaelii.disk.fsync" "vaelii.disk.compress"
                  "vaelii.disk.tokens" "vaelii.disk.cache" "vaelii.disk.sync-ms"
                  "vaelii.disk.compact-dead-ratio" "vaelii.disk.compact-min-interval-ms"
                  "vaelii.disk.lock" "vaelii.index.snapshot"]]
        (is (not (contains? literal-only nm))
            (str nm " now has a literal System/getProperty read too — if that is"
                 " deliberate, drop it from this list; the point of the list is that"
                 " the two literal forms alone do not see these."))))))

;; ---- and the table that describes it ------------------------------------

(def ^:private unpinned
  "Switches `docs/operations.md` documents that this scan cannot reach, each with the
  reason.  All three are shell-only and unprefixed, which is exactly what puts them out
  of range: `${VAELII_…}` is name-shaped enough for one regex, `${GATE_JOBS}` is not,
  and a regex for every `${CAPS}` collects each script's own locals.  A rename of one of
  these is caught by review rather than by this test."
  {"GATE_JOBS"         "scripts/gate.sh, the test stage's shard count"
   "PERF_TOLERANCE"    "scripts/gate.sh, passed through to `lein perf --tolerance`"
   "TEST_BACKENDS_OUT" "scripts/test-backends.sh, its log directory"})

(def ^:private undocumented-by-design
  "Switches the scan finds that the table deliberately has no row for.

  Empty, and that is the finding rather than an oversight: the table groups by who sets
  a switch — operator, developer, CI and bench — so there is a place in it for every
  name the tree reads, and a switch with nowhere to go is a switch somebody would have
  to guess at.  A name belongs here only when a row would misdescribe the surface
  rather than describe it, and it carries the sentence saying which."
  {})

(defn- config-section
  "The lines of `docs/operations.md` under the configuration heading, up to the next
  `##`.  Scoped to that section so the interface table at the top of the file, and any
  other table added later, are not read as claims about switches."
  []
  (->> (str/split-lines (slurp doc-file))
       (drop-while #(not (str/starts-with? % "## Configuration")))
       rest
       (take-while #(not (str/starts-with? % "## ")))))

(defn documented
  "`{name \"path:line\"}` off the table: every row whose first cell is a backticked name
  and whose second is a backticked citation."
  []
  (into {}
        (keep (fn [line]
                (when (str/starts-with? (str/triml line) "|")
                  (let [cells (mapv str/trim (str/split line #"\|"))
                        nm    (second (re-matches #"`([A-Za-z][\w.-]*)`" (get cells 1 "")))
                        cite  (second (re-matches #"`([\w./-]+:\d+)`" (get cells 2 "")))]
                    (when (and nm cite) [nm cite])))))
        (config-section)))

(deftest every-switch-the-code-reads-has-a-row-in-the-operational-doc
  (let [rows    (set (keys (documented)))
        missing (-> (set (keys (surface-sites)))
                    (set/difference rows)
                    (set/difference (set (keys undocumented-by-design))))]
    (is (empty? missing)
        (str "no row in " doc-file " for: " (sort missing)
             ". A switch nothing documents is one an operator finds by reading the"
             " source. Give each a row — name, where it is read, its legal values, its"
             " default, and what it decides — or list it in `undocumented-by-design`"
             " with the sentence saying why a row would misdescribe it."))))

(deftest every-switch-the-doc-documents-is-one-the-code-reads
  ;; The reverse, and the one a doc-only edit introduces: a row for a name nothing reads
  ;; is the same lie as a name with no row, and it is the more convincing of the two.
  (let [real  (into (set (keys (surface-sites))) (keys unpinned))
        ghost (set/difference (set (keys (documented))) real)]
    (is (empty? ghost)
        (str "rows in " doc-file " for switches nothing reads: " (sort ghost)
             ". Either the name is misspelt, or the reader it described is gone and the"
             " row went with it."))))

(deftest every-citation-in-the-table-resolves-to-a-line-that-names-the-switch
  ;; What makes a `file:line` citation worth carrying: it is checked. A line number
  ;; drifts the moment anything above it is edited, and drift here is a failing test
  ;; naming the line the switch moved to rather than a table a reader trusts and lands
  ;; in the wrong place from.
  (let [sites (surface-sites)]
    (doseq [[nm cite] (sort (documented))]
      (let [[path n] (str/split cite #":")
            f        (io/file path)
            line     (when (.isFile f) (get (vec (str/split-lines (slurp f)))
                                            (dec (parse-long n))))]
        (is (some? line) (str nm ": " cite " names no line"))
        (is (and line (str/includes? line nm))
            (str nm ": " cite " does not name it"
                 (when-let [real (seq (sites nm))]
                   (str " — it is read at " (str/join ", " real)))))))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.seed
  "Ontology KB files: declarative content held as **plain text on the classpath**
  rather than as code.

  A KB file is a list of ordinary vaelii sentences — one s-expression each, with
  `;;` line comments and blank lines allowed — named for the context its sentences
  assert into, and grouped **term-centrically**: every sentence about a vocabulary
  term sits together, and the terms run in natural sort order.  Nothing is
  interpreted here that `assert` would not interpret anyway: a rule is just a
  sentence carrying an `implies` / `set/*Rule` / `exceptWhen` wrapper.

  The files live under `resources/kb/`, in a shallow tree that mirrors the context
  spindle:

      kb/CoreContext.txt        the vocabulary head (see vaelii.impl.core-context)
      kb/upper/<C>.txt          definitional layers, between Core and Universe
      kb/middle/<C>.txt         theory layers, between Universe and Well

  The file *name* is the context; the sub-directory is the layer.  What stays in
  **code** (vaelii.impl.starter) is the *order* the files load in and the handful of
  genuinely computed assertions.  Sentences read with `clojure.edn`, so a KB file is
  data and can never run code."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [vaelii.core :as v])
  (:import [java.io PushbackReader]))

(defn- layer-files
  "The `<Context>.txt` file names in layer sub-directory `dir`, read off whichever
  classpath shape holds them: a filesystem tree (repl / lein / test) is listed as a
  directory, and a packaged jar is listed by its own entries — anchored on
  `kb/CoreContext.txt` when the jar carries no directory entry for `kb/<dir>` to
  resolve.  Any other protocol is refused rather than answered nil: nil here starts
  a KB with the upper and middle layers silently absent, the exact failure
  `read-sentences` exists to refuse one file at a time."
  [dir]
  (let [want (str "kb/" dir "/")
        res  (or (io/resource (str "kb/" dir)) (io/resource "kb/CoreContext.txt"))]
    (when res
      (case (.getProtocol res)
        "file" (when-let [d (io/resource (str "kb/" dir))]
                 (keep (fn [^java.io.File f]
                         (let [n (.getName f)]
                           (when (str/ends-with? n ".txt") n)))
                       (.listFiles (io/file d))))
        "jar"  (let [conn ^java.net.JarURLConnection (.openConnection res)]
                 (seq (for [^java.util.jar.JarEntry e (enumeration-seq (.entries (.getJarFile conn)))
                            :let [n (.getName e)]
                            :when (and (str/starts-with? n want)
                                       (str/ends-with? n ".txt")
                                       (not (str/includes? (subs n (count want)) "/")))]
                        (subs n (count want)))))
        (throw (ex-info (str "kb/" dir " sits behind classpath protocol "
                             (.getProtocol res) ", which layer discovery cannot list")
                        {:type :missing-resource :dir dir :url (str res)}))))))

(defn layer-contexts
  "The context symbols whose KB files live in the layer sub-directory `dir`
  (\"upper\" / \"middle\"), sorted for determinism.  Discovered from the classpath, so
  dropping a new `<Context>.txt` in `kb/<dir>/` loads it with no code change — every
  context is loaded on kb start by default, from a filesystem tree and from a
  packaged jar alike (`layer-files`)."
  [dir]
  (some->> (layer-files dir)
           (map #(symbol (subs % 0 (- (count %) 4))))
           (sort-by str)
           vec))

(defn- resource-path
  "The classpath path of the KB file for `context`, optionally under layer `dir`."
  [context dir]
  (str "kb/" (when dir (str dir "/")) (name context) ".txt"))

(defn read-sentences
  "Read every sentence from the KB file for `context` (a symbol or string), in file
  order.  `dir` names the layer sub-directory (\"upper\" / \"middle\"), nil for a file
  at the `kb/` root.  Throws if the resource is missing: a silently empty ontology is
  worse than a failure to start."
  ([context] (read-sentences context nil))
  ([context dir]
   (let [path (resource-path context dir)]
     (if-let [res (io/resource path)]
       (with-open [r (PushbackReader. (io/reader res))]
         (let [eof (Object.)]
           (loop [acc []]
             (let [form (edn/read {:eof eof} r)]
               (if (identical? form eof)
                 acc
                 (recur (conj acc form)))))))
       (throw (ex-info (str "ontology KB file not found on the classpath: " path)
                       {:type :missing-resource :context context :dir dir :resource path}))))))

(defn load-sentences
  "Assert `sentences` into `context`, **order-insensitively**: a sentence refused
  because content further down the list has not arrived yet is retried rather than
  fatal.  Returns kb.

  A KB file's order is its *terms'*, not its dependencies' — blocks run in natural
  sort order, which is the whole point of grouping term-centrically — so a file cannot
  also be dependency-ordered.  `(argPreserving largerThan 1 partOf)` sits under
  `largerThan` and `(transitive partOf)` under `partOf`, and `l` sorts before `p`.
  Several checks read the store (a preservation's transitivity, an `argIsa` clash, a
  disjointness), so without this a term-centric file is refused for where its author
  filed a sentence.

  Retry rounds run while each one makes progress; the sentences that survive a round
  that changed nothing are re-asserted **without a catch**, so a genuinely ill-formed
  one still throws — carrying the error it has once everything that could have helped
  it is stored, which is the error worth reporting.  A list that loads clean pays one
  `try` per sentence and no second round."
  [kb sentences context]
  (let [attempt (fn [ss]
                  (reduce (fn [acc s]
                            (try (v/assert kb s context) acc
                                 (catch clojure.lang.ExceptionInfo _ (conj acc s))))
                          [] ss))]
    (loop [pending (attempt sentences)]
      (when (seq pending)
        (let [remaining (attempt pending)]
          (if (< (count remaining) (count pending))
            (recur remaining)
            (doseq [s remaining] (v/assert kb s context)))))))
  kb)

(defn load-context
  "Assert every sentence of the KB file for `context` into that context, through
  `load-sentences` — so the file's term order is not also asked to be a dependency
  order.  `dir` names the layer sub-directory, nil for the `kb/` root.  Returns kb."
  ([kb context] (load-context kb context nil))
  ([kb context dir]
   (load-sentences kb (read-sentences context dir) context)))

(defn load-layer
  "Load several context files from one layer sub-directory, in the order given.
  Returns kb."
  [kb dir contexts]
  (doseq [c contexts] (load-context kb c dir))
  kb)

(defproject com.vaelii/vaelii "0.4.0"
  :description "Vaelii — a contextualized common-sense knowledge base with a
                count-aware trie index, forward/backward inference,
                and JTMS truth maintenance, over an in-memory or on-disk store."
  :url "https://github.com/vaelii/vaelii"
  :license {:name "SSPL-1.0"
            :url "https://www.mongodb.com/licensing/server-side-public-license"}
  ;; Generated into the POM. A Clojars page without it offers a reader no route
  ;; from the artifact back to the source it was built from.
  :scm {:name "git" :url "https://github.com/vaelii/vaelii"}
  ;; `lein deploy clojars` reads the credentials from the environment rather than
  ;; from here — a token in project.clj is a token in the public tree. The pair is
  ;; CLOJARS_USERNAME and a Clojars DEPLOY TOKEN as CLOJARS_PASSWORD, never the
  ;; account password; ~/.lein/credentials.clj.gpg is the other supported route
  ;; and needs no change here.
  ;;
  ;; `:sign-releases false` because Clojars does not require a signature and the
  ;; default is to try: without a GPG key on the machine the deploy fails at the
  ;; signing step, after the artifact has been built and named.
  :deploy-repositories [["clojars" {:url "https://repo.clojars.org/"
                                    :username :env/clojars_username
                                    :password :env/clojars_password
                                    :sign-releases false}]]
  ;; README states this too, so it is refused rather than claimed. 2.10 rather than
  ;; 2.9 because `:preserve-eval-meta` below needs it: on 2.9 the key is silently
  ;; ignored and every `lein run` prints the reflection warning it exists to suppress.
  :min-lein-version "2.10.0"
  :dependencies [[org.clojure/clojure "1.12.5"]
                 [com.taoensso/nippy "3.8.1"]
                 [com.taoensso/trove "1.2.0"]
                 [metosin/reitit-ring "0.10.1"]
                 [ring/ring-core "1.15.5"]
                 [ring/ring-jetty-adapter "1.15.5"]
                 ;; escapes body position as well as attributes, so KB content and
                 ;; query params cannot inject markup (docs/web.md)
                 [hiccup "2.0.0"]
                 ;; a no-op SLF4J binding: silences Jetty's "no providers" line.
                 ;; Our own logging goes through Trove, above.
                 [org.slf4j/slf4j-nop "2.0.18"]
                 ;; clasp's `--outf=2` JSON, and libclingo through JNA (docs/asp.md)
                 [cheshire "6.2.0"]
                 [net.java.dev.jna/jna "5.19.1"]
                 ;; the dense and columnar index backends, both off by default
                 ;; (docs/density.md)
                 [org.roaringbitmap/RoaringBitmap "1.6.19"]
                 [it.unimi.dsi/fastutil-core "8.5.19"]
                 ;; XZ (LZMA2) for the exporter's `:xz`. nippy brings it transitively;
                 ;; naming it is what makes the codec a promise rather than an accident
                 ;; of somebody else's dependency graph (docs/api.md).
                 [org.tukaani/xz "1.12"]]
  :main ^:skip-aot vaelii.core
  :target-path "target/%s"
  ;; an unhinted interop call names itself at compile time instead of paying a silent
  ;; runtime lookup.  It WARNS and does not fail — nothing greps the output, here or in
  ;; scripts/lint.sh — so a warning is a defect to fix at the call site rather than a gate
  ;; that stops the build.  Say so, because a comment promising a gate is how four of them
  ;; sat in the test tree printing on every run of every backend.
  :global-vars {*warn-on-reflection* true}
  ;; leiningen `pr-str`s the form it evaluates into a temp file, and that drops
  ;; metadata — including the `^Class` hint in leiningen's own `run` form, which the
  ;; line above then reports as a reflection warning on every `lein run`. This keeps
  ;; the hint. Needs lein 2.10+; an older one ignores the key.
  :preserve-eval-meta true
  ;; `^:slow` defers a test costing about a second or more, `^:llm` one that can reach
  ;; a model provider. What each mark selects, and the separate consent gate beside the
  ;; llm one: CONTRIBUTING.md §5.
  :test-selectors {:default #(not (or (:slow %) (:llm %)))
                   :slow    #(and (:slow %) (not (:llm %)))
                   :llm     :llm
                   :all     (complement :llm)}
  :profiles {:uberjar {:aot :all}
             ;; point JNA at libclingo (docs/asp.md). `VAELII_CLINGO_LIB` names the
             ;; directory holding it; the default is Homebrew's on Apple silicon, which
             ;; is where a macOS `brew install clingo` puts it and nowhere a Linux
             ;; package manager does — set the variable there (/usr/lib,
             ;; /usr/local/lib, /usr/lib/x86_64-linux-gnu).
             :with-clingo {:jvm-opts [~(str "-Djna.library.path="
                                            (or (System/getenv "VAELII_CLINGO_LIB")
                                                "/opt/homebrew/lib"))]}
             ;; a foreign-format reader on the classpath for the one command you
             ;; prefix; scripts/link-checkouts.sh is the other route (docs/foreign.md).
             ;;
             ;; GROUP-QUALIFIED, and it has to be. A bare `vaelii-foreign` means
             ;; groupId AND artifactId `vaelii-foreign`, which is not what is
             ;; published — the release is `com.vaelii/vaelii-foreign`.
             ;;
             ;; `:exclusions` on vaelii itself: the plugin depends on the released
             ;; vaelii, so without this the profile drags that jar onto the classpath
             ;; of a *checkout of vaelii*, beside the `src/` being edited. Source paths
             ;; win today, so it works and hides itself — until local source diverges
             ;; from the release and a stale class answers instead.
             ;; The snapshot of the version being cut, in step with `defproject`
             ;; above: the release carve strips the snapshot suffix tree-wide, so
             ;; this pin ships naming the sibling release that goes out beside it.
             ;; Naming a *released* coordinate here would resolve from Clojars today
             ;; and then ship a release pinning the previous one. The sibling is
             ;; developed from source — scripts/link-checkouts.sh — or `lein install`ed.
             :with-foreign {:dependencies [[com.vaelii/vaelii-foreign "0.3.0"
                                            :exclusions [com.vaelii/vaelii]]]}
             ;; static analysis, dev-only so none of it reaches an uberjar. Keep
             ;; lein-cloverage's version in step with scripts/coverage.sh, which injects
             ;; the same plugin at the root level so `cloverage` registers under
             ;; `with-profile +test`.
             :dev {:plugins [[dev.weavejester/lein-cljfmt "0.16.5"]
                             [lein-shell "0.5.0"]
                             [lein-cloverage "1.2.4"]]}
             ;; property-based tests, in :test rather than :dev because a local
             ;; gitignored profiles.clj may redefine :dev and replace it wholesale
             :test {:dependencies [[org.clojure/test.check "1.1.3"]]
                    ;; Quiet the engine's own logging under test. Trove's default
                    ;; backend is the console one at `:info` and nothing sets it, so
                    ;; a GREEN run printed 777 lines of `:warn`/`:info` — two thirds
                    ;; of the suite's output, and none of it a verdict. The suite
                    ;; provokes those on purpose: `::dropped-conclusion`,
                    ;; `:no-placement` and the aggregate refusals are what the
                    ;; assertions are checking for, so the log is the test working.
                    ;;
                    ;; The floor is `:error`, not off — an unexpected error still
                    ;; prints next to the failure it explains. Turn the rest back on
                    ;; when a red run needs them: `VAELII_TEST_LOG_LEVEL=info lein test`.
                    ;;
                    ;; Runtime `resolve` rather than `trove/set-log-fn!` because
                    ;; injections compile as one `do`: a macro in the same form as the
                    ;; `require` that loads it has no var to resolve yet.
                    :injections
                    [(require 'taoensso.trove 'taoensso.trove.console)
                     (alter-var-root
                      (resolve 'taoensso.trove/*log-fn*)
                      (constantly
                       ((resolve 'taoensso.trove.console/get-log-fn)
                        {:min-level (keyword (or (System/getenv "VAELII_TEST_LOG_LEVEL")
                                                 "error"))})))]}
             ;; sampling profiler for a repl: `(prof/profile (…))`, flamegraphs under
             ;; /tmp/clj-async-profiler/results/, `(prof/serve-ui 8080)`. The -XX pair
             ;; keeps inlined frames off their caller's line; the attach flag is how it
             ;; starts without a separate agent.
             :repl {:dependencies [[com.clojure-goes-fast/clj-async-profiler "2.0.0-beta1"]]
                    :jvm-opts ["-Djdk.attach.allowAttachSelf"
                               "-XX:+UnlockDiagnosticVMOptions"
                               "-XX:+DebugNonSafepoints"]}
             ;; the benchmark harnesses, on their own source path so they never ship.
             ;; They build a whole index in the heap, and jol sizes a KB structurally
             ;; (`bench-scale`) — the --add-opens and self-attach are what let it read
             ;; field layout rather than estimate it.
             :bench {:source-paths ["bench"]
                     :dependencies [[org.openjdk.jol/jol-core "0.17"]
                                    [org.roaringbitmap/RoaringBitmap "1.6.19"]
                                    [it.unimi.dsi/fastutil-core "8.5.19"]]
                     :jvm-opts ["-Xmx6g" "--add-opens=java.base/java.lang=ALL-UNNAMED"
                                "-Djdk.attach.allowAttachSelf=true"]}
             ;; `lein browser`: the browser running inside a repl with a reload channel
             ;; into it. Both halves bind loopback — a write route with no auth beside
             ;; an nREPL is a remote shell (CONTRIBUTING.md §6).
             :browser {:repl-options
                       {:host "127.0.0.1"
                        :init (do ((requiring-resolve 'vaelii.impl.web/dev-repl)) nil)}}
             ;; outdated-dependency report, isolated from every other classpath
             :antq {:dependencies [[com.github.liquidz/antq "2.11.1276"]]}}
  ;; indent rules come from an optional cljfmt-indents.edn at the repo root, so a
  ;; custom macro can be taught to cljfmt without editing this file
  :cljfmt {:indentation?                    true
           :indent-line-comments?           true
           :remove-surrounding-whitespace?  true
           :remove-trailing-whitespace?     true
           :insert-missing-whitespace?      true
           :remove-consecutive-blank-lines? true
           :sort-ns-references?             true
           ;; `clojure.edn/read-string`, never `clojure.core`'s: this file is untracked,
           ;; so a pull request can add it, and lein evaluates project.clj on *every*
           ;; invocation.  `core/read-string` honours `#=(...)` reader-eval, which would
           ;; make checking out a contributor's branch and typing `lein test` arbitrary
           ;; code execution on the reviewer's machine.
           :extra-indents ~(let [f (java.io.File. "cljfmt-indents.edn")]
                             (if (.exists f)
                               (do (require 'clojure.edn)
                                   ((resolve 'clojure.edn/read-string) (slurp f)))
                               {}))}
  ;; `lein lint` is the unified report; the lint-* aliases run one check each, and
  ;; `lein fix` reformats in place.
  :aliases {"lint"            ["shell" "bash" "scripts/lint.sh"]
            "lint-glossary"   ["shell" "bash" "scripts/lint-glossary.sh"]
            "lint-links"      ["shell" "python3" "scripts/check-doc-links.py" "--public-view"]
            "lint-drift"      ["shell" "python3" "scripts/check-doc-drift.py"]
            "lint-kondo"      ["shell" "clj-kondo" "--lint" "src" "test" "bench"]
            "lint-cljfmt"     ["cljfmt" "check"]
            "lint-shellcheck" ["shell" "shellcheck" "scripts/lint.sh" "scripts/lint-glossary.sh" "scripts/coverage.sh" "scripts/test-backends.sh" "scripts/gate.sh" "scripts/update-badges.sh" "scripts/link-checkouts.sh"]
            ;; lint, the suite and the perf claims in one run, not fail-fast
            ;; (scripts/gate.sh says why)
            "gate"            ["shell" "bash" "scripts/gate.sh"]
            ;; the suite across JVMs — what the gate's test stage runs.  Memory stores
            ;; only: a durable half is one lock and three usable space blocks, so the
            ;; script refuses one rather than sharding into it.
            "test-parallel"   ["shell" "bash" "scripts/test-parallel.sh"]
            ;; feeds the README deps badge, via scripts/update-badges.sh --deps
            "antq"            ["with-profile" "+antq" "run" "-m" "antq.core" "--skip=pom"]
            ;; the whole suite once per backend — seven record×index pairs plus the
            ;; overlay decorator (scripts/test-backends.sh)
            "test-backends"   ["shell" "bash" "scripts/test-backends.sh"]
            "fix"             ["cljfmt" "fix"]
            "bench-memory"    ["with-profile" "+bench" "run" "-m" "vaelii.bench.memory"]
            "bench-memconjoin" ["with-profile" "+bench" "run" "-m" "vaelii.bench.memconjoin"]
            "bench-scale"     ["with-profile" "+bench" "run" "-m" "vaelii.bench.scale"]
            "bench-postings"  ["with-profile" "+bench" "run" "-m" "vaelii.bench.postings"]
            "bench-survey"    ["with-profile" "+bench" "run" "-m" "vaelii.bench.survey"]
            "bench-densetrie" ["with-profile" "+bench" "run" "-m" "vaelii.bench.densetrie"]
            "bench-records"   ["with-profile" "+bench" "run" "-m" "vaelii.bench.records"]
            "bench-jtms"      ["with-profile" "+bench" "run" "-m" "vaelii.bench.jtms"]
            "bench-backward"  ["with-profile" "+bench" "run" "-m" "vaelii.bench.backward"]
            "bench-forward"   ["with-profile" "+bench" "run" "-m" "vaelii.bench.forward"]
            "bench-plan"      ["with-profile" "+bench" "run" "-m" "vaelii.bench.plan"]
            "bench-qcn"       ["with-profile" "+bench" "run" "-m" "vaelii.bench.qcn"]
            "bench-qcnchain"  ["with-profile" "+bench" "run" "-m" "vaelii.bench.qcnchain"]
            "bench-aggchain"  ["with-profile" "+bench" "run" "-m" "vaelii.bench.aggchain"]
            "bench-corpus"    ["with-profile" "+bench" "run" "-m" "vaelii.bench.corpus"]
            "bench-reindex"   ["with-profile" "+bench" "run" "-m" "vaelii.bench.reindex"]
            "bench-residency" ["with-profile" "+bench" "run" "-m" "vaelii.bench.residency"]
            "bench-cyclic"    ["with-profile" "+bench" "run" "-m" "vaelii.bench.cyclic"]
            "bench-checks"    ["with-profile" "+bench" "run" "-m" "vaelii.bench.checks"]
            "bench-inherit"   ["with-profile" "+bench" "run" "-m" "vaelii.bench.inherit"]
            "bench-tactics"   ["with-profile" "+bench" "run" "-m" "vaelii.bench.tactics"]
            ;; the performance *gate*, as against the bench-* reports above: scaling
            ;; claims as growth ratios, non-zero exit on a regression
            "perf"            ["with-profile" "+bench" "run" "-m" "vaelii.bench.perf"]
            "browser"         ["with-profile" "+browser" "repl"]
            ;; the daemon and the CLI (docs/operations.md)
            "serve"           ["run" "-m" "vaelii.serve"]
            "cli"             ["run" "-m" "vaelii.cli"]}
  :repl-options {:init-ns vaelii.core})

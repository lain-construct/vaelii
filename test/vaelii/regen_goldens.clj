;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.regen-goldens
  "`lein regen-goldens` — rewrite every checked-in golden from the live tree.

  Three surfaces are frozen against a golden, and each one's test owns its own
  `regenerate-golden!`.  This is the headless way to call all three: no REPL, and so no
  browser or profiler server booting behind it.

  **Regeneration is the deliberate half of a two-part step, never the fix for a red
  suite.**  A golden goes red to say a published surface moved; running this makes the
  red go away without answering the question it asked.  So: read the failure, decide
  whether the move is a Breaking change (CONTRIBUTING §3.8), write the entry if it is,
  and *then* run this — committing the golden diff in the same commit as the change,
  where a reviewer sees the two together.  That pairing is the whole mechanism.  A
  golden committed on its own is a surface change nobody reviewed.

  Prints one line per golden and exits non-zero if any of them throws, so a scripted
  caller can tell a rewrite from a failure."
  (:require [vaelii.api-surface-test :as api-surface]
            [vaelii.config-surface-test :as config-surface]
            [vaelii.spi-surface-test :as spi]))

(def ^:private goldens
  "`[label regenerate-fn file]`, in the order they are written."
  [["public API surface" #(api-surface/regenerate-golden!)    "test/golden/api-surface.edn"]
   ["extension points"    #(spi/regenerate-golden!)            "test/golden/spi-protocols.edn"]
   ["config surface"     #(config-surface/regenerate-golden!) "test/golden/config-surface.edn"]])

(defn -main [& _]
  (let [failed (reduce (fn [failed [label f file]]
                         (try
                           (f)
                           (println (str "  ✓ " file "  — " label))
                           failed
                           (catch Throwable t
                             (println (str "  ✗ " file "  — " label ": " (.getMessage t)))
                             (inc failed))))
                       0
                       goldens)]
    (if (pos? failed)
      (println (str failed " golden(s) failed to regenerate — nothing to commit."))
      (println (str "Goldens regenerated. Review the diff, and commit it in the SAME"
                    " commit as the change that moved it.")))
    (shutdown-agents)
    (System/exit (if (pos? failed) 1 0))))

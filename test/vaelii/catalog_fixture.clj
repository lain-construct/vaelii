;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.catalog-fixture
  "The `:each` fixture and the helpers `catalog-test`, `catalog-unload-test` and
  `catalog-export-test` share."
  (:require [vaelii.browser.catalog :as cat]
            [vaelii.test-util :as tu]))

;; The catalog is process-global (one registry, one active KB), so every test starts and
;; ends with it empty — and the loads run on the catalog's own spaces, well clear of the
;; block the suite owns.
(defn empty-registry
  "An `:each` fixture: run `f` with the catalog's registry empty, and empty it after."
  [f]
  (cat/reset-registry!)
  (try (f) (finally (cat/reset-registry!))))

(defn beside-the-block
  "A memory space of the calling namespace's own, **derived from the block the run owns**
  rather than fixed.  Two `catalog-unload-test` tests open a KB directly (they need a
  second `open-kb` over the same stores, which is what makes an unrecovered store
  reproducible without a disk fixture) and the in-memory backend keys its process-global
  registry by this value — so a literal number is a store two runs on different blocks
  would share, and `scripts/test-backends.sh` moves the block with `VAELII_TEST_SPACE`
  precisely so two runs can proceed at once.

  Spelled as `[::name block]`, which is `tu/plain-memory-space`'s own idiom: the block is
  read back off that map because it is the only *public* spelling of what
  `VAELII_TEST_SPACE` was parsed and range-checked into, and re-parsing the variable here
  would be a second reading of it to keep in step."
  [tag]
  [tag (second (:space tu/plain-memory-space))])

(defn wait-for
  "Block until no load is running (or `ms`, 120 s by default, passes) — the tests drive an
  API that is deliberately asynchronous."
  ([] (wait-for 120000))
  ([ms]
   (let [deadline (+ (System/currentTimeMillis) ms)]
     (while (and (cat/loading?) (< (System/currentTimeMillis) deadline))
       (Thread/sleep 20))
     (not (cat/loading?)))))

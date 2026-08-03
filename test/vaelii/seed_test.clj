;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.seed-test
  "Ontology KB files: declarative KB content held as plain text under resources/kb/,
  one file per context, the file name the context, the sub-directory the layer.
  Every context present is discovered and loaded on kb start (vaelii.impl.starter)."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.seed :as seed]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(deftest the-kb-files-are-on-the-classpath
  (testing "the vocabulary head reads as a non-empty list of sentences"
    (let [ss (seed/read-sentences 'CoreContext)]
      (is (seq ss))
      (is (every? seq? ss) "every form is an s-expression")))
  (testing "a layer file reads by (context, dir), by symbol or string alike"
    (is (seq (seed/read-sentences 'OrganismContext "upper")))
    (is (= (seed/read-sentences 'OrganismContext "upper")
           (seed/read-sentences "OrganismContext" "upper")))))

(deftest every-context-in-a-layer-is-discovered
  ;; the point of layer discovery: a KB is added by dropping a file, no code change
  (testing "upper holds the definitional contexts, sorted"
    (is (= '[AbstractContext LifeContext MeasureContext OrganismContext
             SocietyContext SpaceContext TimeContext]
           (seed/layer-contexts "upper"))))
  (testing "middle holds the theory contexts"
    (is (= '[AnatomyContext BiologyContext KinshipContext MereologyContext
             SizeContext SocialContext]
           (seed/layer-contexts "middle"))))
  (testing "an absent layer is nil, not a crash"
    (is (nil? (seed/layer-contexts "no-such-layer")))))

(deftest a-missing-kb-file-fails-loudly
  ;; a silently empty ontology is worse than a failure to start
  (testing "an absent context file throws rather than yielding nil"
    (is (thrown? clojure.lang.ExceptionInfo (seed/read-sentences 'NoSuchContext)))
    (is (thrown? clojure.lang.ExceptionInfo (seed/load-context nil 'NoSuchContext)))))

(deftest the-dotted-rest-pattern-round-trips-through-the-reader
  ;; CoreContext.txt carries the one form an EDN reader could choke on
  (let [core (seed/read-sentences 'CoreContext)]
    (is (some #(= % '(set/inertRule
                      (implies (?pred . ?args) (ist UniverseContext (?pred . ?args)))))
              core))))

;; ---- a file's order is its terms', not its dependencies' ------------------

(tu/deftest-kb a-sentence-refused-for-what-has-not-arrived-yet-is-retried
  ;; The blocks of a KB file run in natural sort order, so it cannot also be
  ;; dependency-ordered: `(argPreserving largerThan 1 partOf)` is filed under
  ;; `largerThan` and `(transitive partOf)` under `partOf`, and `l` sorts before `p`.
  ;; The preservation's transitivity check reads the store, so in file order it is
  ;; refused — for where its author filed a sentence, which is not a property of the
  ;; knowledge.
  (tu/with-terms [largerThan1 partOf1 A1 B1 C1]
    (let [sentences [(list 'argPreserving largerThan1 1 partOf1)  ; needs the next line
                     (list 'transitive partOf1)
                     (list partOf1 B1 C1)
                     (list partOf1 A1 B1)
                     (list largerThan1 C1 'thing)]]
      (testing "in that order, one at a time, the declaration is refused"
        (is (thrown? clojure.lang.ExceptionInfo
                     (doseq [s sentences] (v/assert kb s 'UniverseContext)))))
      (testing "and loaded as a file is loaded, every sentence lands"
        (seed/load-sentences kb sentences 'UniverseContext)
        (is (every? some? (map #(v/handle-of kb % 'UniverseContext) sentences)))
        (is (v/ask? kb (list largerThan1 A1 'thing) 'UniverseContext)
            "two hops, so the declaration is not merely stored but usable")))))

(tu/deftest-kb a-sentence-nothing-could-heal-still-throws
  ;; The retry is for a sentence waiting on its file, not an amnesty.  A round that
  ;; changes nothing re-asserts what is left without a catch, so the error that comes
  ;; out is the one the sentence has once everything that could help it is stored.
  (tu/with-terms [cursed2 begat2 dog2_t Nobody2]
    (is (thrown-with-msg?
         clojure.lang.ExceptionInfo #"not transitive"
         (seed/load-sentences kb [(list 'argPreserving cursed2 1 begat2)
                                  (list dog2_t Nobody2)]
                              'UniverseContext)))
    (testing "and what could load, did"
      (is (some? (v/handle-of kb (list dog2_t Nobody2) 'UniverseContext))))))

(tu/deftest-kb a-layer-context-loads-into-its-own-context
  ;; the file name is the context — OrganismContext.txt lands in OrganismContext, on
  ;; top of the CoreContext vocabulary, and the genl closure is built from the file.
  (seed/load-context kb 'CoreContext)
  (seed/load-context kb 'OrganismContext "upper")
  (testing "its sentences land in the context the file names"
    (is (seq (v/sentexes-matching kb '(genl dog mammal) 'OrganismContext)))
    (is (empty? (v/sentexes-matching kb '(genl dog mammal) 'CoreContext))))
  (testing "and the genl closure is built from the file"
    (tu/with-terms [Rex]
      (v/assert kb (list 'dog Rex) 'OrganismContext)
      (is (v/isa? kb Rex 'mammal))
      (is (v/isa? kb Rex 'animal))              ; the whole biological chain is in this one file
      (is (not (v/isa? kb Rex 'plant))))))

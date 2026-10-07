;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.except-monotonic-test
  "A visibility `(except (sentexHandle H))` hides a sentex on the forced-monotonic roster
  from the context it is asserted in and every context below, as it hides a `:default`
  one, and the consequences the engine computes from it follow.  See docs/contexts.md,
  \"except: removing visibility down a context subtree\"."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(def ^:private mono {:strength :monotonic})

(defn- parent-and-child
  "`CxParent` under `CxWell`, and `CxChild` seeing `CxParent`."
  [kb parent child]
  (v/assert kb (list 'genlCx parent 'CxWell) 'CxUniverse mono)
  (v/assert kb (list 'genlCx child parent) 'CxUniverse mono))

(defn- relation
  "A gensym'd temporary predicate spelled camelCase, so a `genl` between two of them is a
  `genl` between predicates (docs/naming.md); `tu/with-terms` folds the capitals out."
  [base]
  (gensym (str base "Tmp")))

;; ---- roster target 1: disjoint ---------------------------------------------

(tu/deftest-kb an-except-hides-a-forced-monotonic-disjoint-from-its-subtree-only
  (tu/with-terms [dog_t cat_t Rex CxParent CxChild]
    (parent-and-child kb CxParent CxChild)
    (let [decl  (list 'disjoint dog_t cat_t)
          _     (is (checks/forced-monotonic? kb decl) "the target is on the roster")
          dh    (v/assert kb decl CxParent mono)
          _dog  (v/assert kb (list dog_t Rex) CxParent mono)
          cat-h (v/assert kb (list cat_t Rex) CxParent)]
      (testing "(a) before the except: visible from both, and the :default membership loses"
        (is (v/ask? kb decl CxParent))
        (is (v/ask? kb decl CxChild))
        (is (v/disjoint? kb dog_t cat_t CxChild))
        (is (not (v/believed? kb cat-h CxParent)))
        (is (not (v/believed? kb cat-h CxChild))))
      (let [eh (v/assert kb (list 'except (v/sentex-handle dh)) CxChild mono)]
        (testing "(b) the except of a roster handle is admitted"
          (is (v/believed? kb eh CxChild)))
        (testing "(c) hidden from the child, still read from the parent"
          (is (not (v/ask? kb decl CxChild)))
          (is (v/ask? kb decl CxParent))
          (is (not (v/disjoint? kb dog_t cat_t CxChild)))
          (is (v/disjoint? kb dog_t cat_t CxParent)))
        (testing "(d) the clash it convicted is withdrawn at the child only"
          (is (v/believed? kb cat-h CxChild) "no visible disjoint, so nothing defeats it")
          (is (not (v/believed? kb cat-h CxParent))))
        (v/retract! kb eh)
        (testing "(e) retracting the except restores the declaration and the clash"
          (is (v/ask? kb decl CxChild))
          (is (v/disjoint? kb dog_t cat_t CxChild))
          (is (not (v/believed? kb cat-h CxChild))))))))

;; ---- roster target 2: genl between predicates ------------------------------

(tu/deftest-kb an-except-hides-a-forced-monotonic-predicate-genl-from-its-subtree-only
  (tu/with-terms [Ann Bob CxParent CxChild]
    (parent-and-child kb CxParent CxChild)
    (let [likesX (relation "likes")
          knowsX (relation "knows")
          edge (list 'genl likesX knowsX)
          goal (list knowsX Ann Bob)
          _    (is (checks/forced-monotonic? kb edge) "a predicate genl is on the roster")
          gh   (v/assert kb edge CxParent mono)]
      (v/assert kb (list likesX Ann Bob) CxParent)
      (testing "(a) before the except: visible from both, and the general tuple proved"
        (is (v/ask? kb edge CxParent))
        (is (v/ask? kb edge CxChild))
        (is (v/ask? kb goal CxParent))
        (is (v/ask? kb goal CxChild)))
      (let [eh (v/assert kb (list 'except (v/sentex-handle gh)) CxChild mono)]
        (testing "(b) the except of a roster handle is admitted"
          (is (v/believed? kb eh CxChild)))
        (testing "(c) hidden from the child, still read from the parent"
          (is (not (v/ask? kb edge CxChild)))
          (is (v/ask? kb edge CxParent)))
        (testing "(d) the tuple proved through the edge is proved at the parent only"
          (is (v/ask? kb goal CxParent))
          (is (not (v/ask? kb goal CxChild))))
        (v/retract! kb eh)
        (testing "(e) retracting the except restores the edge and what it proves"
          (is (v/ask? kb edge CxChild))
          (is (v/ask? kb goal CxChild)))))))

;; ---- :default control: genl between types ----------------------------------

(tu/deftest-kb an-except-hides-a-default-type-genl-the-same-way
  (tu/with-terms [dog_t animal_t Rex CxParent CxChild]
    (parent-and-child kb CxParent CxChild)
    (let [edge (list 'genl dog_t animal_t)
          goal (list animal_t Rex)
          _    (is (not (checks/forced-monotonic? kb edge)) "a type genl is defeasible")
          gh   (v/assert kb edge CxParent)]
      (v/assert kb (list dog_t Rex) CxParent)
      (testing "(a) before the except: visible from both, and the membership proved"
        (is (v/ask? kb edge CxParent))
        (is (v/ask? kb edge CxChild))
        (is (v/ask? kb goal CxParent))
        (is (v/ask? kb goal CxChild)))
      (let [eh (v/assert kb (list 'except (v/sentex-handle gh)) CxChild mono)]
        (testing "(b) the except is admitted"
          (is (v/believed? kb eh CxChild)))
        (testing "(c) hidden from the child, still read from the parent"
          (is (not (v/ask? kb edge CxChild)))
          (is (v/ask? kb edge CxParent)))
        (testing "(d) the membership proved through the edge is proved at the parent only"
          (is (v/ask? kb goal CxParent))
          (is (not (v/ask? kb goal CxChild))))
        (v/retract! kb eh)
        (testing "(e) retracting the except restores the edge and what it proves"
          (is (v/ask? kb edge CxChild))
          (is (v/ask? kb goal CxChild)))))))

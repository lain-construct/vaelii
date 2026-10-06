;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.except-monotonic-test
  "A visibility `(except (sentexHandle H))` hides a sentex on the **forced-monotonic
  roster** exactly as it hides a `:default` one.

  A roster literal goes OUT only by retraction (docs/reference.md, decision 11): no
  defeat unmakes it.  An except is not a defeat.  It removes the visibility of `H` from
  the context it is asserted in and every context that sees that context
  (docs/contexts.md, \"except: removing visibility down a context subtree\"), and
  `checks/check-except-target` refuses only an unknown handle, so a roster target is
  admitted and hidden like any other.

  Each test places the target in a parent context `CxParent`, asserts the except in a child
  `CxChild` (`genlCx CxChild CxParent`), and pins five things:

    (a) the target is readable from `CxParent` and from `CxChild` before the except;
    (b) the except is admitted;
    (c) after it, a read from `CxChild` does not see the target and a read from `CxParent` does;
    (d) a consequence the engine computes from the target holds from `CxParent` and not
        from `CxChild`;
    (e) retracting the except restores the target and the consequence at `CxChild`.

  Two roster targets are covered — `disjoint` between types, whose consequence is the
  defeat of a `:default` membership that clashes with a `:monotonic` one, and `genl`
  between predicates, whose consequence is a tuple of the general predicate proved from
  a tuple of the specific one — and one `:default` control: `genl` between types, whose
  consequence is a membership proved through the edge."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.checks :as checks]
            [vaelii.impl.sentex :as sx]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(def ^:private mono {:strength :monotonic})

(defn- parent-and-child!
  "`CxParent` under `CxWell`, and `CxChild` seeing `CxParent`."
  [kb parent child]
  (v/assert kb (list 'genlCx parent 'CxWell) 'CxUniverse mono)
  (v/assert kb (list 'genlCx child parent) 'CxUniverse mono))

(defn- visible?
  "Is `sentence` answered from `context`, reading through the `genlCx` closure."
  [kb sentence context]
  (true? (v/ask? kb sentence context)))

(defn- relation
  "A gensym'd temporary predicate spelled camelCase, so a `genl` between two of them is a
  `genl` between predicates (docs/naming.md); `tu/with-terms` folds the capitals out."
  [base]
  (gensym (str base "Tmp")))

;; ---- roster target 1: disjoint ---------------------------------------------

(tu/deftest-kb an-except-hides-a-forced-monotonic-disjoint-from-its-subtree-only
  (tu/with-terms [dog_t cat_t Rex CxParent CxChild]
    (parent-and-child! kb CxParent CxChild)
    (let [decl  (list 'disjoint dog_t cat_t)
          _     (is (checks/forced-monotonic? kb decl) "the target is on the roster")
          dh    (v/assert kb decl CxParent mono)
          _dog  (v/assert kb (list dog_t Rex) CxParent mono)
          cat-h (v/assert kb (list cat_t Rex) CxParent)]
      (testing "(a) before the except: visible from both, and the :default membership loses"
        (is (visible? kb decl CxParent))
        (is (visible? kb decl CxChild))
        (is (v/disjoint? kb dog_t cat_t CxChild))
        (is (not (v/believed? kb cat-h CxParent)))
        (is (not (v/believed? kb cat-h CxChild))))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle dh)) CxChild mono)]
        (testing "(b) the except of a roster handle is admitted"
          (is (integer? eh)))
        (testing "(c) hidden from the child, still read from the parent"
          (is (not (visible? kb decl CxChild)))
          (is (visible? kb decl CxParent))
          (is (not (v/disjoint? kb dog_t cat_t CxChild)))
          (is (v/disjoint? kb dog_t cat_t CxParent)))
        (testing "(d) the clash it convicted is withdrawn at the child only"
          (is (v/believed? kb cat-h CxChild) "no visible disjoint, so nothing defeats it")
          (is (not (v/believed? kb cat-h CxParent))))
        (v/retract! kb eh)
        (testing "(e) retracting the except restores the declaration and the clash"
          (is (visible? kb decl CxChild))
          (is (v/disjoint? kb dog_t cat_t CxChild))
          (is (not (v/believed? kb cat-h CxChild))))))))

;; ---- roster target 2: genl between predicates ------------------------------

(tu/deftest-kb an-except-hides-a-forced-monotonic-predicate-genl-from-its-subtree-only
  (tu/with-terms [Ann Bob CxParent CxChild]
    (parent-and-child! kb CxParent CxChild)
    (let [likesX (relation "likes")
          knowsX (relation "knows")
          edge (list 'genl likesX knowsX)
          goal (list knowsX Ann Bob)
          _    (is (checks/forced-monotonic? kb edge) "a predicate genl is on the roster")
          gh   (v/assert kb edge CxParent mono)]
      (v/assert kb (list likesX Ann Bob) CxParent)
      (testing "(a) before the except: visible from both, and the general tuple proved"
        (is (visible? kb edge CxParent))
        (is (visible? kb edge CxChild))
        (is (v/ask? kb goal CxParent))
        (is (v/ask? kb goal CxChild)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle gh)) CxChild mono)]
        (testing "(b) the except of a roster handle is admitted"
          (is (integer? eh)))
        (testing "(c) hidden from the child, still read from the parent"
          (is (not (visible? kb edge CxChild)))
          (is (visible? kb edge CxParent)))
        (testing "(d) the tuple proved through the edge is proved at the parent only"
          (is (v/ask? kb goal CxParent))
          (is (not (v/ask? kb goal CxChild))))
        (v/retract! kb eh)
        (testing "(e) retracting the except restores the edge and what it proves"
          (is (visible? kb edge CxChild))
          (is (v/ask? kb goal CxChild)))))))

;; ---- :default control: genl between types ----------------------------------

(tu/deftest-kb an-except-hides-a-default-type-genl-the-same-way
  (tu/with-terms [dog_t animal_t Rex CxParent CxChild]
    (parent-and-child! kb CxParent CxChild)
    (let [edge (list 'genl dog_t animal_t)
          goal (list animal_t Rex)
          _    (is (not (checks/forced-monotonic? kb edge)) "a type genl is defeasible")
          gh   (v/assert kb edge CxParent)]
      (v/assert kb (list dog_t Rex) CxParent)
      (testing "(a) before the except: visible from both, and the membership proved"
        (is (visible? kb edge CxParent))
        (is (visible? kb edge CxChild))
        (is (v/ask? kb goal CxParent))
        (is (v/ask? kb goal CxChild)))
      (let [eh (v/assert kb (list 'except (sx/sentex-handle gh)) CxChild mono)]
        (testing "(b) the except is admitted"
          (is (integer? eh)))
        (testing "(c) hidden from the child, still read from the parent"
          (is (not (visible? kb edge CxChild)))
          (is (visible? kb edge CxParent)))
        (testing "(d) the membership proved through the edge is proved at the parent only"
          (is (v/ask? kb goal CxParent))
          (is (not (v/ask? kb goal CxChild))))
        (v/retract! kb eh)
        (testing "(e) retracting the except restores the edge and what it proves"
          (is (visible? kb edge CxChild))
          (is (v/ask? kb goal CxChild)))))))

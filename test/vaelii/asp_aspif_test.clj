(ns vaelii.asp-aspif-test
  "The ASP lower layer: the ASPIF emitter, the atom table, and the backend
  facade.  No KB, no store — these namespaces know nothing about sentexes.

  Two levels of assertion, deliberately.  The **wire format** is pinned literally,
  because ASPIF is an external contract with clingo and clasp: a silent encoding
  change is not a refactor, it is a different program, and a round-trip test alone
  would not localize the break.  The **semantics** are then checked by actually
  solving, because a well-formed program that means the wrong thing still emits
  valid text.

  Solving is skipped when no backend is reachable; the emitter tests always run."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [vaelii.impl.asp.aspif :as aspif]
            [vaelii.impl.asp.atoms :as atoms]
            [vaelii.impl.asp.solver :as solver]))

(def ^:private asp? (solver/available?))

(defn- lines [text] (remove str/blank? (str/split-lines text)))

(defn- body-lines
  "The statement lines of a rendered program — header and terminator dropped."
  [text] (-> (lines text) rest butlast))

;; ---- the wire format ----------------------------------------------------

(deftest render-frames-the-program
  (let [out (lines (aspif/render [(aspif/fact 1)]))]
    (testing "an ASPIF program opens with the version header"
      (is (= "asp 1 0 0" (first out))))
    (testing "and closes with the 0 terminator"
      (is (= "0" (last out))))))

(deftest statements-encode-as-documented
  ;; Format per statement type, from the grammar in the aspif ns docstring:
  ;;   rule  1 <head-type> <head-size> <head...> <body-type> <body-size> <lits...>
  ;;   min   2 <priority> <n> <lit weight>...
  ;;   show  4 <len> <text> <n> <atom>...
  (testing "a fact is a disjunctive head of one with an empty body"
    (is (= ["1 0 1 7 0 0"] (body-lines (aspif/render [(aspif/fact 7)])))))
  (testing "a choice atom is head-type 1"
    (is (= ["1 1 1 7 0 0"] (body-lines (aspif/render [(aspif/choice 7)])))))
  (testing "a normal rule lists its body literals"
    (is (= ["1 0 1 3 0 2 1 2"] (body-lines (aspif/render [(aspif/rule 3 [1 2])])))))
  (testing "default negation is a negative literal"
    (is (= ["1 0 1 3 0 2 1 -2"] (body-lines (aspif/render [(aspif/rule 3 [1 -2])])))))
  (testing "an integrity constraint is a rule with no head"
    (is (= ["1 0 0 0 2 1 2"] (body-lines (aspif/render [(aspif/constraint [1 2])])))))
  (testing "a minimize statement carries its priority then literal/weight pairs"
    (is (= ["2 5 2 1 1 2 3"]
           (body-lines (aspif/render [(aspif/minimize 5 [[1 1] [2 3]])])))))
  (testing "a show statement carries the byte length of its label"
    (is (= ["4 2 s1 1 9"] (body-lines (aspif/render [(aspif/show 9 "s1")]))))))

(deftest an-empty-program-is-still-well-formed
  (testing "header and terminator with nothing between them"
    (is (= ["asp 1 0 0" "0"] (lines (aspif/render []))))))

;; ---- the atom table ----------------------------------------------------

(deftest atom-ids-start-at-one
  ;; Atom 0 is the ASPIF terminator and must never be allocated.
  (let [t (atoms/new-table)]
    (is (= 1 (atoms/intern-sentex! t 100)))
    (is (pos? (atoms/intern-sentex! t 101)))))

(deftest interning-is-idempotent
  (let [t (atoms/new-table)
        a (atoms/intern-sentex! t 42)]
    (testing "the same sentex re-interns to the same atom"
      (is (= a (atoms/intern-sentex! t 42))))
    (testing "and does not consume a fresh id"
      (is (= 1 (atoms/count-atoms t))))))

(deftest the-three-namespaces-share-one-counter
  ;; Sentex, contradiction, and aux atoms all live in one ASPIF atom space, so ids
  ;; must not collide even though the lookup maps are separate.
  (let [t (atoms/new-table)
        s (atoms/intern-sentex! t 1)
        c (atoms/intern-contradiction! t '(contradiction X))
        a (atoms/intern-aux! t [:scratch 1])]
    (is (= 3 (count (distinct [s c a]))))
    (is (= 3 (atoms/count-atoms t)))))

(deftest labels-round-trip
  ;; Labels are the whole read-back channel: a solver echoes these strings, so
  ;; label -> atom -> source must survive the trip.
  (let [t (atoms/new-table)
        s (atoms/intern-sentex! t 42)
        c (atoms/intern-contradiction! t '(contradiction Y))]
    (testing "a sentex atom is labelled from its handle"
      (is (= "s42" (atoms/label-of-atom t s)))
      (is (= 42 (atoms/sentex-id-of-atom t s))))
    (testing "a contradiction atom carries its descriptor back"
      (is (= '(contradiction Y) (atoms/contradiction-of-atom t c))))
    (testing "and every label resolves to its atom"
      (is (= s (atoms/atom-of-label t (atoms/label-of-atom t s))))
      (is (= c (atoms/atom-of-label t (atoms/label-of-atom t c)))))))

(deftest an-uninterned-lookup-is-nil-not-an-error
  (let [t (atoms/new-table)]
    (is (nil? (atoms/atom-of-sentex t 999)))
    (is (nil? (atoms/label-of-atom t 999)))))

;; ---- solving -----------------------------------------------------------

(deftest a-fact-appears-in-the-answer-set
  (when asp?
    (let [r (solver/solve (aspif/render [(aspif/fact 1) (aspif/show 1 "a")]) :label)]
      (is (contains? #{:sat :optimum} (:status r)))
      (is (= ["a"] (:atoms r))))))

(deftest an-integrity-constraint-forces-the-other-branch
  ;; {a}. {b}. :- not a, not b.  :- a, b.   -- exactly one of a/b, and minimizing a
  ;; leaves b as the only optimum.
  (when asp?
    (let [prog (aspif/render [(aspif/choice 1) (aspif/choice 2)
                              (aspif/constraint [1 2])
                              (aspif/constraint [-1 -2])
                              (aspif/minimize 1 [[1 1]])
                              (aspif/show 1 "a") (aspif/show 2 "b")])
          r (solver/solve prog :label)]
      (testing "the constrained-against atom is dropped, its partner kept"
        (is (= ["b"] (:atoms r)))))))

(deftest an-unsatisfiable-program-reports-unsat-rather-than-throwing
  ;; clasp signals outcomes through exit codes 10/20/30; those are results, not
  ;; failures, and must not surface as exceptions.
  (when asp?
    (let [r (solver/solve (aspif/render [(aspif/fact 1) (aspif/constraint [1])]) :label)]
      (is (= :unsat (:status r))))))

(deftest higher-minimize-priority-dominates
  ;; The level ordering the edge solver's objective depends on: level 5 is satisfied
  ;; at the expense of level 1.
  (when asp?
    (let [prog (aspif/render [(aspif/choice 1) (aspif/choice 2)
                              (aspif/constraint [1 2])
                              (aspif/constraint [-1 -2])
                              (aspif/minimize 5 [[1 1]])
                              (aspif/minimize 1 [[2 1]])
                              (aspif/show 1 "a") (aspif/show 2 "b")])]
      (is (= ["b"] (:atoms (solver/solve prog :label)))))))

(deftest both-backends-agree
  ;; The facade routes by program size and availability; a program must mean the
  ;; same thing whichever backend sees it.
  (when (and asp? (some? (resolve 'vaelii.impl.asp.clasp/solve)))
    (require 'vaelii.impl.asp.clasp)
    (let [clasp-solve (resolve 'vaelii.impl.asp.clasp/solve)
          prog (aspif/render [(aspif/choice 1) (aspif/choice 2)
                              (aspif/constraint [1 2])
                              (aspif/minimize 1 [[1 1] [2 1]])
                              (aspif/show 1 "a") (aspif/show 2 "b")])]
      (is (= (set (:atoms (solver/solve prog :label)))
             (set (:atoms (clasp-solve prog :label))))))))

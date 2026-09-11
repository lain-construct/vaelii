;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.asp-incremental-test
  "The in-process clingo *session* API: a live control grown a batch at a time and
  toggled through externals, then solved repeatedly.  What the one-shot `solve` path
  cannot do and this exists to prove — `clingo_control_load_aspif` is one-shot, so a
  program loaded that way is frozen; the backend accessors are not, so a session adds
  ground rules between solves (clasp keeping its learned clauses) and flips an external
  atom's truth with no re-grounding.

  The assertions are semantic — actually solving and reading atoms/status back — because
  a session's whole claim is about behaviour across solves: that a second batch sees the
  first batch's atoms, that a new constraint takes effect on the live control, and that an
  external toggles.  Every test is a tiny program with a microsecond solve, and the whole
  suite is a no-op when libclingo is unreachable, exactly like the other solver suites."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.asp.aspif :as aspif]
            [vaelii.impl.asp.clingo :as clingo]))

(def ^:private asp? (clingo/available?))

(def ^:private optn
  "The `:all-optima` clingo flags: enumerate every model (`--models=0`), each trivially
  optimal absent a minimize statement, so `solve-session`'s `:witnesses` is the full model
  set — the count and membership these tests read.  Fixed at `open-session`, since a
  session's control takes its flags once."
  ["--opt-mode=optN" "--models=0"])

(defn- witness-sets
  "The models of an `:all-optima` result as a set of atom-label sets — order-free, so a
  count and a membership test do not depend on the search's arrival order."
  [r] (set (map set (:witnesses r))))

;; ---- growing the program on a live control -----------------------------

(deftest growing-a-program-reuses-the-earlier-batch's-atoms
  ;; The cross-batch identity the whole session rests on: a `vid` interned in batch one
  ;; re-interns to the SAME cid in batch two (clingo_backend_add_atom keys on the symbol),
  ;; so batch two's rule over atom 1 and its constraint on atom 1 bind the very atom batch
  ;; one chose — and the program has grown, not been reloaded.
  (when asp?
    (let [s (clingo/open-session optn)]
      (try
        ;; batch 1:  {a}.
        (clingo/add-program! s [(aspif/choice 1) (aspif/show 1 "a")])
        (let [cid-1 (get @(:cids s) 1)
              r1    (clingo/solve-session s :all-optima)]
          (testing "batch one alone admits a model in which a holds"
            (is (contains? #{:sat :optimum} (:status r1)))
            (is (some #(contains? (set %) "a") (:witnesses r1))))
          ;; batch 2:  b :- a.   :- not a.   (referencing atom 1)
          (clingo/add-program! s [(aspif/rule 2 [1]) (aspif/constraint [-1])
                                  (aspif/show 2 "b")])
          (let [cid-1' (get @(:cids s) 1)
                r2     (clingo/solve-session s :all-optima)]
            (testing "the re-seen atom keeps its cid across the two batches"
              (is (= cid-1 cid-1')))
            (testing "a is now forced and b derives from it — batch two saw batch one's atom"
              (is (contains? #{:sat :optimum} (:status r2)))
              (is (= #{"a" "b"} (set (:atoms r2)))))))
        (finally (clingo/close-session! s))))))

(deftest growing-a-program-narrows-its-models
  ;; The added constraint takes effect on the live control: a program that admitted four
  ;; models admits two once batch two forbids the all-in and all-out corners.  Solved
  ;; before and after on the ONE session, so it is the live grow — not a fresh load — that
  ;; the narrowing shows.
  (when asp?
    (let [s (clingo/open-session optn)]
      (try
        ;; {a}. {b}.  — four models
        (clingo/add-program! s [(aspif/choice 1) (aspif/choice 2)
                                (aspif/show 1 "a") (aspif/show 2 "b")])
        (let [before (clingo/solve-session s :all-optima)]
          (testing "two free choices admit all four subsets"
            (is (= 4 (count (:witnesses before))))
            (is (= #{#{} #{"a"} #{"b"} #{"a" "b"}} (witness-sets before))))
          ;; forbid both-true and both-false — exactly-one survives
          (clingo/add-program! s [(aspif/constraint [1 2]) (aspif/constraint [-1 -2])])
          (let [after (clingo/solve-session s :all-optima)]
            (testing "the two new constraints cut the model set to the two singletons"
              (is (= 2 (count (:witnesses after))))
              (is (= #{#{"a"} #{"b"}} (witness-sets after))))
            (testing "and it strictly narrowed"
              (is (< (count (:witnesses after)) (count (:witnesses before)))))))
        (finally (clingo/close-session! s))))))

;; ---- externals: toggle truth between solves, no re-grounding -----------

(deftest an-external-toggles-a-derived-atom
  ;; The multi-shot payoff: one control, one grounding, three solves.  `ext` is declared
  ;; false, `p :- ext`; flipping `ext`'s truth between solves flips `p` with it and the
  ;; program is never re-ground — the atoms come and go on the SAME live control.
  (when asp?
    (let [s (clingo/open-session optn)]
      (try
        (clingo/declare-external! s 3 :false "ext")
        (clingo/add-program! s [(aspif/rule 1 [3]) (aspif/show 1 "p")])
        (testing "ext false: neither ext nor its consequence p"
          (is (= #{} (set (:atoms (clingo/solve-session s :all-optima))))))
        (clingo/assign-external! s 3 :true)
        (testing "ext true: ext holds and p derives from it"
          (is (= #{"ext" "p"} (set (:atoms (clingo/solve-session s :all-optima))))))
        (clingo/assign-external! s 3 :false)
        (testing "ext false again: both gone — the toggle is reversible on the live control"
          (is (= #{} (set (:atoms (clingo/solve-session s :all-optima))))))
        (finally (clingo/close-session! s))))))

(deftest an-external-gates-satisfiability
  ;; The same toggle, but the external now decides SAT: `p :- ext` and `:- not p`, so the
  ;; program is unsatisfiable exactly when `ext` is false.  Status flips :unsat ↔ SAT
  ;; across solves on the one session, with nothing re-ground between them.
  (when asp?
    (let [s (clingo/open-session optn)]
      (try
        (clingo/declare-external! s 3 :false "ext")
        (clingo/add-program! s [(aspif/rule 1 [3]) (aspif/constraint [-1])
                                (aspif/show 1 "p")])
        (testing "ext false starves the only rule for p, so :- not p is unsatisfiable"
          (is (= :unsat (:status (clingo/solve-session s :all-optima)))))
        (clingo/assign-external! s 3 :true)
        (testing "ext true supplies p and the program is satisfiable"
          (is (contains? #{:sat :optimum} (:status (clingo/solve-session s :all-optima)))))
        (clingo/assign-external! s 3 :false)
        (testing "and back to unsat — the same control, three solves"
          (is (= :unsat (:status (clingo/solve-session s :all-optima)))))
        (finally (clingo/close-session! s))))))

;; ---- lifecycle ---------------------------------------------------------

(deftest an-empty-session-solves-and-closes-cleanly
  ;; A session opened and never grown is a valid empty program: trivially satisfiable with
  ;; no atoms.  And `close-session!` frees the control without throwing — the hygiene the
  ;; `finally` in every test above leans on.
  (when asp?
    (let [s (clingo/open-session optn)
          r (clingo/solve-session s :all-optima)]
      (testing "the empty program is satisfiable and yields no atoms"
        (is (contains? #{:sat :optimum} (:status r)))
        (is (= [] (:atoms r))))
      (testing "closing frees the control and returns without throwing"
        (is (nil? (clingo/close-session! s)))))))

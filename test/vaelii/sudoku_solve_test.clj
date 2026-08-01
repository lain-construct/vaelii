(ns vaelii.sudoku-solve-test
  "A 4×4 sudoku solved by **progressive solve contexts** — the do/label → do/classify
  → promote loop over a chain of round contexts.

  The whole puzzle is stated declaratively, in the KB's own vocabulary:

    * the board is typed individuals (`sudoku_cell` C11…C44, `sudoku_value` V1…V4)
      with the peer geometry as symmetric `peerOf` facts;
    * two forward rules derive `(ruledOut ?c ?v)` — a filled peer rules its value out,
      and a filled cell rules *every* value out (its own included, so a decided cell
      offers no further choice);
    * one excepted assumptionRule offers `(cellValue ?c ?v)` for any cell and value —
      `exceptWhen (ruledOut ?c ?v)`, so grounding itself does the candidate filtering
      (the guard-honoring half of `ground-heads`);
    * `(functional cellValue)` turns same-cell rivals into nogoods.

  Each round: `do/label` enumerates the optimal worlds over the surviving candidates,
  `do/classify` splits them into forced (kept in every world — a naked single) and
  supportable (a genuinely open cell), and the forced values are promoted as real
  `filled` facts into the *next* round's context, a `genlContext` child of the current
  one.  New clues fire the `ruledOut` rules, the next grounding offers fewer choices,
  and the loop terminates when nothing is left to choose.  The chain of round contexts
  then proves the unique solution; the base KB never believed a single choice.

  Enumeration needs an ASP backend, so the whole test is guarded on `asp?`."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.core :as v]
            [vaelii.impl.asp.solver :as solver]
            [vaelii.test-util :as tu]))

(def ^:private asp? (solver/available?))

;; the unique solution, and the five cells the puzzle leaves open
(def ^:private solution
  {[1 1] 1 [1 2] 2 [1 3] 3 [1 4] 4
   [2 1] 3 [2 2] 4 [2 3] 1 [2 4] 2
   [3 1] 2 [3 2] 1 [3 3] 4 [3 4] 3
   [4 1] 4 [4 2] 3 [4 3] 2 [4 4] 1})

(def ^:private open-cells #{[1 1] [1 2] [1 3] [2 1] [3 1]})

(def ^:private all-cells (sort (keys solution)))

(defn- cell-sym [[r c]] (symbol (str "C" r c)))
(defn- val-sym  [n]     (symbol (str "V" n)))

(defn- box-of [[r c]] [(quot (dec r) 2) (quot (dec c) 2)])

(defn- peers?
  "Same row, same column, or same 2×2 box."
  [a b]
  (and (not= a b)
       (or (= (a 0) (b 0)) (= (a 1) (b 1)) (= (box-of a) (box-of b)))))

(defn- load-sudoku
  "The timeless structure and rules into SudokuContext; the given clues into
  Round1Context, which sees it."
  [kb]
  (let [S 'SudokuContext]
    ;; metadata first — it governs the facts and choices below
    (v/assert kb '(symmetric peerOf) S {:strength :monotonic})
    (v/assert kb '(functional cellValue) S {:strength :monotonic})
    ;; the board: cells and values as typed individuals
    (doseq [rc all-cells]
      (v/assert kb (list 'sudoku_cell (cell-sym rc)) S {:strength :monotonic}))
    (doseq [n (range 1 5)]
      (v/assert kb (list 'sudoku_value (val-sym n)) S {:strength :monotonic}))
    ;; peer geometry, one direction per unordered pair — peerOf is symmetric
    (doseq [[i a] (map-indexed vector all-cells)
            b     (drop (inc i) all-cells)
            :when (peers? a b)]
      (v/assert kb (list 'peerOf (cell-sym a) (cell-sym b)) S {:strength :monotonic}))
    ;; a filled peer rules its value out; a filled cell rules every value out
    (v/assert kb '(implies (and (peerOf ?c ?c2) (filled ?c2 ?v)) (ruledOut ?c ?v))
              S {:strength :monotonic})
    (v/assert kb '(implies (and (filled ?c ?v2) (sudoku_value ?v)) (ruledOut ?c ?v))
              S {:strength :monotonic})
    ;; the choice: any cell may take any value — except one already ruled out
    (v/assert kb '(exceptWhen (ruledOut ?c ?v)
                              (set/assumptionRule
                               (implies (and (sudoku_cell ?c) (sudoku_value ?v))
                                        (cellValue ?c ?v))))
              S {:strength :monotonic})
    ;; round 1 sees the structure and adds the clues
    (v/assert kb '(genlContext Round1Context SudokuContext) S {:strength :monotonic})
    (doseq [rc all-cells :when (not (open-cells rc))]
      (v/assert kb (list 'filled (cell-sym rc) (val-sym (solution rc)))
                'Round1Context {:strength :monotonic}))))

(defn- promote
  "Record newly forced cell values as real clues in `ctx`, the next round's context —
  a genlContext child of `prev`, so the next grounding sees everything so far."
  [kb forced ctx prev]
  (v/assert kb (list 'genlContext ctx prev) prev {:strength :monotonic})
  (doseq [s forced
          :let [[_ c vv] (vec s)]]
    (v/assert kb (list 'filled c vv) ctx {:strength :monotonic})))

(deftest sudoku-solved-by-progressive-solve-contexts
  (when asp?
    (tu/with-cleared-kb [kb tu/fresh]
      (load-sudoku kb)

      (let [r1 (v/assert kb '(do/label Round1Context RoundOnePlanContext) 'Round1Context)
            c1 (v/assert kb '(do/classify RoundOnePlanContext) 'Round1Context)]
        (testing "round 1: C11 is open three ways, the other four open cells are naked singles"
          (is (= 3 (:count r1)))
          (is (= #{'(cellValue C12 V2) '(cellValue C13 V3)
                   '(cellValue C21 V3) '(cellValue C31 V2)}
                 (set (:forced c1))))
          (is (= #{'(cellValue C11 V1) '(cellValue C11 V2) '(cellValue C11 V3)}
                 (set (:supportable c1))))
          (is (empty? (:excluded c1))))
        (testing "each world keeps the four singles plus one of C11's candidates"
          (doseq [l (:labelings r1)]
            (is (= 5 (count (:true l))))
            (is (= 2 (count (:false l)))))
          (is (= #{'V1 'V2 'V3}
                 (set (map (fn [l]
                             (some (fn [s] (let [[_ c vv] (vec s)]
                                             (when (= c 'C11) vv)))
                                   (:true l)))
                           (:labelings r1))))))
        (testing "the labeling contexts hang under the round that produced them"
          (is (every? #(v/sees? kb % 'Round1Context)
                      (map :context (:labelings r1)))))

        (promote kb (:forced c1) 'Round2Context 'Round1Context)
        (let [r2 (v/assert kb '(do/label Round2Context RoundTwoPlanContext) 'Round2Context)
              c2 (v/assert kb '(do/classify RoundTwoPlanContext) 'Round2Context)]
          (testing "round 2: the promoted clues squeeze C11 to a single — one world, one forced value"
            (is (= 1 (:count r2)))
            (is (= ['(cellValue C11 V1)] (:forced c2)))
            (is (empty? (:supportable c2))))

          (promote kb (:forced c2) 'Round3Context 'Round2Context)
          (testing "round 3: every cell is decided, so grounding offers nothing"
            (let [r3 (v/assert kb '(do/label Round3Context RoundThreePlanContext) 'Round3Context)]
              (is (zero? (:count r3)))
              (is (= :no-choices (:reason r3)))))

          (testing "the chain of round contexts proves the unique solution"
            (doseq [rc all-cells]
              (let [vs (distinct (map #(get % '?v)
                                      (v/prove kb (list 'filled (cell-sym rc) '?v)
                                               'Round3Context)))]
                (is (= [(val-sym (solution rc))] vs)
                    (str "cell " rc)))))

          (testing "no choice ever leaked into belief, and nothing contradicts"
            (is (empty? (v/prove kb '(cellValue ?c ?v) 'Round3Context)))
            (is (zero? (count (v/contradictions kb)))))

          (testing "re-running a round replaces its labelings instead of accreting"
            ;; Round1Context's up-closure is unchanged by the later rounds (they sit
            ;; below it), so the same three worlds come back — into freshly rewritten
            ;; contexts, each holding exactly one grounding's truth values
            (let [r1b (v/assert kb '(do/label Round1Context RoundOnePlanContext) 'Round1Context)]
              (is (= 3 (:count r1b)))
              ;; five kept + two rejected truth values + the labelingOf marker
              (doseq [l (:labelings r1b)]
                (is (= 8 (count (v/sentexes-in-context kb (:context l)))))))))))))

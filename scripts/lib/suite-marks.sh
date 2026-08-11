#!/usr/bin/env bash
# scripts/lib/suite-marks.sh — the per-namespace progress marks, shared by the two
# scripts that run the whole suite more than once.
#
# `test-backends.sh` varies STORAGE and `test-sweeps.sh` varies the ENGINE
# implementation the suite runs against, but a run is a run: both boot a JVM,
# load every test namespace, and then take twenty minutes saying nothing unless
# somebody makes them.  This file is the making-them, and it lives here so the
# two scripts share one answer rather than two that drift.
#
# What is NOT here: each script's run loop, its interrupt handling and its
# summary.  Those touch variables only the caller has — a disk directory to
# clean, an env list to build — and generalizing them would buy indirection
# rather than reuse.  The rule for what belongs in this file is that it reads
# only its arguments.
#
# Sourced, never executed:
#   . scripts/lib/suite-marks.sh
#
# Every name below is read by the sourcing script and by nothing in here, which is
# what a library is and what SC2034 cannot see across a `.` boundary — hence the
# file-level disable rather than one per assignment.
# shellcheck disable=SC2034

# Colour only when someone is watching; a redirected run stays greppable.
if [[ -t 1 ]]; then
  GREEN=$'\033[32m'; RED=$'\033[31m'; DIM=$'\033[2m'; BOLD=$'\033[1m'; OFF=$'\033[0m'
else
  GREEN=""; RED=""; DIM=""; BOLD=""; OFF=""
fi
TICK="${GREEN}✔${OFF}"
CROSS="${RED}✘${OFF}"

hms() { printf '%dm%02ds' $(($1 / 60)) $(($1 % 60)); }

# The revision a run was taken at, and whether the tree was clean — the first line of
# every suite log.
#
# Without it a log records what was run and not *what it was run against*, and on a
# shared checkout those are different questions.  A matrix takes ~35 minutes and another
# agent landing a test halfway through moves the test and assertion counts under it; the
# artifact then shows counts that differ per backend, which reads exactly like a run that
# skipped something.  It cost one investigation to establish that it was not.
#
# `src/` and `test/` only: a dirty `docs/` or `CHANGELOG.md` cannot move a count, and
# reporting it would make every log say DIRTY on a repo where somebody is always writing.
revision_stamp() {
  local rev dirty
  rev=$(git rev-parse --short HEAD 2>/dev/null || echo "no-git")
  dirty=$(git status --porcelain -- src test 2>/dev/null | wc -l | tr -d ' ')
  if [ "${dirty:-0}" -gt 0 ]; then
    printf '# suite run at %s — tree DIRTY: %s uncommitted file(s) under src/ or test/ — %s\n' \
      "$rev" "$dirty" "$(date '+%Y-%m-%d %H:%M:%S')"
  else
    printf '# suite run at %s — src/ and test/ clean — %s\n' \
      "$rev" "$(date '+%Y-%m-%d %H:%M:%S')"
  fi
}

# what `lein test` compiles before it can run the first namespace — the number the
# wait is proportional to, and NOT the number of marks a run will print: the
# selector narrows what RUNS, never what is loaded, so every run pays this in full.
NS_COUNT=$(find test -name '*_test.clj' | wc -l | tr -d ' ')

# …and how many of them the selector will actually run, which is the denominator the
# marks count towards.  Leiningen prints one `lein test <ns>` header per namespace
# holding at least one SELECTED test, so a namespace whose every test is `^:slow`
# emits nothing under `:default` and would otherwise leave the count short.  Read off
# the source: the three forms that define a test all sit at column 0, and a `^:slow`
# on the `ns` form marks the whole file (which is what leiningen's metadata merge
# means).
TEST_FORM='^\((tu/deftest-kb|deftest|defspec) '
selected_ns_count() {
  local sel="$1" f slow plain count=0
  while IFS= read -r f; do
    if grep -qE '^\(ns +\^:slow' "$f"; then
      slow=1; plain=0
    else
      slow=$(grep -cE "$TEST_FORM\\^:slow" "$f")
      plain=$(grep -cE "${TEST_FORM}[^^]" "$f")
    fi
    case "$sel" in
      :slow)    (( slow  > 0 )) && count=$((count + 1)) ;;
      :default) (( plain > 0 )) && count=$((count + 1)) ;;
      *)        count=$((count + 1)) ;;
    esac
  done < <(find test -name '*_test.clj')
  echo "$count"
}

# How wide a row of marks is: as many groups of ten as the terminal has room
# for, keeping the right-hand column free for the running count.  Ten to a group
# because the point of grouping is to be countable at a glance.
COLS=$(tput cols 2>/dev/null)
[[ "$COLS" =~ ^[0-9]+$ ]] && (( COLS >= 40 )) || COLS=80   # a pty can report 0
ROW_GROUPS=$(( (COLS - 13 + 1) / 11 ))
(( ROW_GROUPS < 1 )) && ROW_GROUPS=1
MARKS_PER_ROW=$(( ROW_GROUPS * 10 ))

# One mark per test namespace, printed while the suite runs — the marks alone,
# in rows, which is a progress bar whose bricks each mean something.  A name per
# namespace is 165 lines a run and 1300 a matrix, and reading them is not how
# anybody uses this; where the ✘ falls in the row is.  Names come back after a
# failing run, which is when they answer a question.
#
# `lein test` prints `lein test <ns>` BEFORE running that namespace and
# `lein test :only <ns>/<test>` above every failure inside one, so a namespace's
# verdict is known when the next header (or the closing `Ran N tests`) arrives —
# one namespace of lag, and nothing waits for the run to end.  The failure lines
# name their own namespace, so a report that lands late is still attributed to
# the right one.  `fflush` because the mark is the progress: buffered, it would
# arrive with the summary it exists to precede.
#
# `$RUN_NS_COUNT` is the caller's, set from `selected_ns_count` above once the
# selector is parsed — the one value here that is read rather than computed.
ns_marks() {
  awk -v tick="$TICK" -v cross="$CROSS" -v total="$RUN_NS_COUNT" -v per="$MARKS_PER_ROW" '
    BEGIN { width = per + int((per - 1) / 10); digits = length(total) }
    function blanks(n,   s) { s = ""; while (n-- > 0) s = s " "; return s }
    function emit(   mark) {
      if (ns == "") return
      mark = (ns in bad) ? cross : tick
      if (col == 0) printf("  ")                  # the row indent
      else if (col % 10 == 0) printf(" ")         # the group gap
      printf("%s", mark)
      col++; count++
      if (col == per) endrow(); else fflush()
      ns = ""
    }
    # the count sits in a fixed column, so a partial row is padded to the width
    # a full one would have had rather than left where it happened to stop
    function endrow(   used) {
      if (col == 0) return
      used = col + int((col - 1) / 10)
      printf("%s  %*d/%d\n", blanks(width - used), digits, count, total)
      col = 0
      fflush()
    }
    /^lein test :only / { split($4, part, "/"); bad[part[1]] = 1; next }
    /^lein test [A-Za-z0-9._-]+$/ { emit(); ns = $3; next }
    /^Ran [0-9]+ tests/ { emit(); endrow() }
    END { emit(); endrow() }
  '
}

# The two lines clojure.test prints last, tightened into one column, plus the
# failing namespaces a red run should name under its summary.  Both read the log
# rather than the exit code, so a run that died before printing them says "did
# not finish" instead of claiming a count it never reached.
run_summary() {
  grep -aE '^Ran [0-9]+ tests' "$1" | tail -1 \
    | sed -E 's/^Ran ([0-9]+) tests containing ([0-9]+) assertions\.?$/\1 tests, \2 assertions/'
}
run_counts() {
  grep -aE '^[0-9]+ failures, [0-9]+ errors' "$1" | tail -1 | sed 's/\.$//'
}
failing_namespaces() {
  grep -aoE '^lein test :only [a-zA-Z0-9._-]+/' "$1" \
    | sed -E 's|^lein test :only ||; s|/$||' | sort -u
}

#!/usr/bin/env bash
# scripts/test-backends.sh — run the whole suite once per storage backend and
# report a ✔ / ✘ per test namespace as it goes, then one per run.
#
# Storage is two independent choices (docs/storage.md): the RECORD store, which
# must survive (`:memory` / `:disk`), and the INDEX, which is derived state
# `reindex` recomputes from the records (`:memory` / `:dense` / `:columnar` /
# `:disk`).  That is 2 × 4 = 8 pairings, of which SEVEN are legal — RAM records
# under the durable index is refused, an index outliving its records describing
# records that are gone — and each of the seven has a `:backend` name spelled
# `<records>-<index>`, which is what `VAELII_TEST_BACKEND` takes.  Every one of
# them loads the same shipped text KB (`resources/kb/*.txt`); what differs is
# only where the sentexes live and how they are indexed.
# An eighth run, `overlay`, is not an eighth pair but the fork decorator
# (docs/overlay.md) over an empty base.
#
# Each run prints the command it is about to run and the log it is writing —
# `env … lein test :default  # target/test-backends/<backend>.log` — so it is
# tailable while it goes and reproducible by copying the line.  The line carries only
# what THAT run needs: a scratch disk directory (`-Dvaelii.disk.dir`) is a
# durable run's concern, so a RAM-only one is given no `-D` at all and reads as
# the plain `lein test` it is.
#
# Then the run's own output becomes a ✔/✘ per test namespace, printed as each
# one finishes rather than at the end — so a suite eight minutes in has said
# eight minutes' worth about where it is.  The marks alone, in groups of ten
# across rows as wide as the terminal, each row closing with the count: a
# progress bar whose bricks each mean something, and three lines a backend
# rather than 165.  Everything else the suite prints (reflection warnings, the
# engine's own :warn logs, the failure reports) goes to the log, and a failing
# run names its failing namespaces under its summary line — which is where a
# name is worth reading, since by then it is the answer to a question.
#
# The FIRST mark of a run lands ~20s after its command line, and none of that
# gap is this script: `lein test` boots a JVM and then compiles and loads every
# test namespace before it runs any of them, so there is nothing to mark until
# it has.  The run says as much on the line under the command, because silence
# nobody accounted for reads as a hang.
#
# The suite is expected to be **failing-set-identical** across every run — a
# backend that answers differently is a bug in the backend, not a feature of
# it.  The assertion COUNT is identical too, across all eight: no test here
# compares a raw index map, so none is gated on the shape of one.  A run whose
# count differs has skipped something the others ran, which is worth reading
# even when both runs are green.
#
# Runs are SEQUENTIAL by design.  Two disk-backed suites over one directory
# would collide on the single-writer lock, and `VAELII_TEST_SPACE` only admits
# three non-overlapping four-db blocks — so parallelism buys three runs, not
# eight, at the cost of every run's timing being unreadable.
#
# A leading-colon argument is a TEST SELECTOR, passed straight to `lein test`
# (project.clj defines them).  `:default` — what a bare run takes — skips the
# eighteen `^:slow` tests, the exhaustive cross-products and randomized oracles
# that take one run from 317s to 219s between them; `:slow` is those alone;
# `:all` is both.  Eight backends multiply that gap by eight, which is why the
# fast pass is the default here for the same reason it is in `lein test` — and
# why the matrix is worth running at `:all` before a storage change lands.  A
# non-default selector writes `<backend>.<selector>.log`, so a `:slow` pass does
# not overwrite what a full one left.
#
# Usage:
#   ./scripts/test-backends.sh                       # all eight, :default
#   ./scripts/test-backends.sh :all                  # all eight, slow tests included
#   ./scripts/test-backends.sh :slow memory          # the slow tests, one backend
#   ./scripts/test-backends.sh memory disk-memory    # only these
#   ./scripts/test-backends.sh --tms dense           # the dense TMS instead
#   ./scripts/test-backends.sh --fail-fast
#   ./scripts/test-backends.sh --keep                # keep each run's disk dir
#
# Env:
#   TEST_BACKENDS_OUT   log directory (default target/test-backends)
#
# ^C stops the suite that is running and then the script — one interrupt gets
# you out of the whole matrix, not out of one run of it.
#
# Exit: 0 when every run passed, 1 when one failed, 130 when interrupted.

set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

# `<records>-<index>`, in the order they run: the three RAM-record pairs first
# (fast, no files), then the four durable-record ones — derived indexes before
# the durable one, so the runs that write least go first.
#
# `overlay` is an eighth run and not an eighth pair: it is the DECORATOR — a
# private writable fork over a shared read-only base (docs/overlay.md) — with
# the base left empty, which is the claim that a fork of nothing behaves exactly
# like the thing it forked.
ALL=(memory memory-dense memory-columnar
     disk-memory disk-dense disk-columnar disk
     overlay)

TMS=""
FAIL_FAST=0
KEEP=0
SELECTOR=":default"
WANTED=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    --tms) TMS="$2"; shift 2 ;;
    --tms=*) TMS="${1#*=}"; shift ;;
    --fail-fast) FAIL_FAST=1; shift ;;
    --keep) KEEP=1; shift ;;
    -h|--help) awk 'NR>1 && /^#/ {sub(/^# ?/, ""); print; next} NR>1 {exit}' "$0"; exit 0 ;;
    # checked here rather than left to lein, which answers an unknown selector with
    # "Please specify :test-selectors in project.clj" — true, and not the problem
    :all|:slow|:default) SELECTOR="$1"; shift ;;
    :*) echo "unknown selector $1 (:all, :slow, :default)" >&2; exit 2 ;;
    -*) echo "unknown flag $1 (try --help)" >&2; exit 2 ;;
    *) WANTED+=("$1"); shift ;;
  esac
done

if [[ ${#WANTED[@]} -gt 0 ]]; then
  BACKENDS=("${WANTED[@]}")
else
  BACKENDS=("${ALL[@]}")
fi

OUT_DIR="${TEST_BACKENDS_OUT:-target/test-backends}"
mkdir -p "$OUT_DIR"

# Colour only when someone is watching; a redirected run stays greppable.
if [[ -t 1 ]]; then
  GREEN=$'\033[32m'; RED=$'\033[31m'; DIM=$'\033[2m'; BOLD=$'\033[1m'; OFF=$'\033[0m'
else
  GREEN=""; RED=""; DIM=""; BOLD=""; OFF=""
fi
TICK="${GREEN}✔${OFF}"
CROSS="${RED}✘${OFF}"

hms() { printf '%dm%02ds' $(($1 / 60)) $(($1 % 60)); }

# what `lein test` compiles before it can run the first namespace — the number the
# wait below is proportional to, and NOT the number of marks a run will print: the
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
RUN_NS_COUNT=$(selected_ns_count "$SELECTOR")

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
# namespace is 165 lines a backend and 1300 a matrix, and reading them is not
# how anybody uses this; where the ✘ falls in the row is.  Names come back after
# a failing run, which is when they answer a question.
#
# `lein test` prints `lein test <ns>` BEFORE running that namespace and
# `lein test :only <ns>/<test>` above every failure inside one, so a namespace's
# verdict is known when the next header (or the closing `Ran N tests`) arrives —
# one namespace of lag, and nothing waits for the run to end.  The failure lines
# name their own namespace, so a report that lands late is still attributed to
# the right one.  `fflush` because the mark is the progress: buffered, it would
# arrive with the summary it exists to precede.
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

# ^C stops the run in progress AND the script.  Neither half is automatic.
#
# A `lein test` left in the foreground swallows the interrupt and the `for` loop
# marches on to the next backend, so getting out of an eight-run matrix takes
# eight interrupts.  So the suite runs in the background and the script `wait`s
# on it, which a trap CAN interrupt.
#
# Killing it then needs two things bash does not give by default.  `set -m` puts
# each background job in its own process group, so one signal reaches every
# process a run is (the `lein` wrapper, its JVM, the project JVM it forks, and
# the `tee`/`awk` reading them) — signalling a pid alone would kill one and
# orphan the rest.  The job is a pipeline, so its group is named by its FIRST
# process while `$!` is its last; `ps` is what reads the group off the pid bash
# hands back.  And `set -m` un-does the rule that a background job in a
# job-control-less shell has SIGINT set to IGNORED, which would make an
# interrupt unkillable by the very signal the user pressed.  SIGTERM first, so
# the durability shutdown hook runs and a disk-backed run closes its logs
# cleanly, then SIGKILL for anything that will not go.
set -m
child_pid=""
child_pgid=""
current_backend=""
current_log=""
diskdir=""
FAILED=()
DONE_RUNS=()

# Two codes for one fact: shellcheck 0.10 split "this function is never called"
# out of SC2317 into SC2329, so naming only the new one leaves the script red on
# every older shellcheck — including the one ubuntu-latest ships, which is how
# this surfaced. Both, so a contributor and CI reach the same verdict.
# shellcheck disable=SC2317,SC2329  # invoked from the INT/TERM trap below
stop_child() {
  [[ -z "$child_pgid" ]] && return 0
  kill -TERM -"$child_pgid" 2>/dev/null            # the negative pid: the whole group
  for _ in $(seq 1 20); do
    kill -0 -"$child_pgid" 2>/dev/null || return 0
    sleep 0.25
  done
  kill -KILL -"$child_pgid" 2>/dev/null
}

# shellcheck disable=SC2317,SC2329  # ditto — `trap on_interrupt INT TERM`
on_interrupt() {
  trap - INT TERM                                  # a second ^C is the OS's now
  echo
  echo "  ${RED}^C${OFF} ${DIM}stopping ${current_backend:-the run}${OFF}"
  # 2>/dev/null over both: reaping a signalled job is where bash prints its
  # `Terminated: 15` report, one line per process in the pipeline
  { stop_child; [[ -n "$child_pid" ]] && wait "$child_pid"; } 2>/dev/null
  [[ $KEEP -eq 1 || -z "$diskdir" ]] || rm -rf "$diskdir"
  [[ -n "$current_log" ]] && echo "  ${DIM}partial log: $current_log${OFF}"
  echo
  echo "${RED}interrupted${OFF} ${DIM}after ${#DONE_RUNS[@]} of ${#BACKENDS[@]}${OFF}"
  exit 130
}
trap on_interrupt INT TERM

echo "${BOLD}running the suite on ${#BACKENDS[@]} backend(s)${OFF}" \
     "${DIM}$SELECTOR — $RUN_NS_COUNT of $NS_COUNT namespaces${OFF}${TMS:+  (tms=$TMS)}"
echo "${DIM}logs in $OUT_DIR/${OFF}"
echo

for backend in "${BACKENDS[@]}"; do
  # `<backend>.log` belongs to the routine run; any other selector says which it
  # was, so a `:slow` pass and a `:default` pass sit beside each other
  if [[ "$SELECTOR" == ":default" ]]; then
    log="$OUT_DIR/$backend.log"
  else
    log="$OUT_DIR/$backend${SELECTOR/:/.}.log"
  fi
  current_backend="$backend"
  current_log="$log"

  # as an `env` argument list rather than an assignment prefix: a prefix is
  # recognized before expansion, so a conditionally-present one cannot be built
  envv=(VAELII_TEST_BACKEND="$backend")
  # a private disk directory, but only for a run with a durable half: those
  # derive their store's path from this property, so nothing a previous mode
  # wrote is still lying there.  A RAM-only run reads no directory, and being
  # handed one would only put a `-D` on its line that means nothing.
  diskdir=""
  case "$backend" in
    disk|disk-*)                                   # the RECORD half, i.e. the name's prefix
      diskdir="$OUT_DIR/$backend.disk"
      rm -rf "$diskdir"
      envv+=(JVM_OPTS="-Dvaelii.disk.dir=$diskdir") ;;
  esac
  [[ -n "$TMS" ]] && envv+=(VAELII_TEST_TMS="$TMS")

  # the command verbatim, so a run can be reproduced by copying the line, and
  # the log it is going to — printed BEFORE the run, so a suite still going is
  # already tailable
  echo "  ${DIM}env ${envv[*]} lein test $SELECTOR  # $log${OFF}"
  # ~20s of silence follows, and none of it is this script: `lein test` boots a
  # JVM (~6s to its first byte), then compiles and LOADS every test namespace
  # before running any of them, so there is no namespace to mark until it has.
  # Every one of them, whatever the selector — narrowing what runs does not narrow
  # what is compiled.  Said out loud, because a silence nobody accounted for reads
  # as a hang.
  echo "  ${DIM}loading a JVM and all $NS_COUNT test namespaces; the first mark waits on that${OFF}"
  start=$SECONDS
  # backgrounded and waited on, so ^C reaches the handler above rather than
  # being swallowed by a foreground child.  `tee` keeps the whole run in the
  # log; the terminal gets the marks alone.  With `pipefail` the pipeline's
  # status is `lein`'s, since neither reader fails.
  #
  # `< /dev/null` is what keeps it RUNNING.  `set -m` puts the job in its own
  # process group, which is therefore not the terminal's foreground group, and
  # leiningen pumps its own stdin into the project subprocess — so a run started
  # from a terminal reads the tty from the background, takes SIGTTIN, and the
  # whole group STOPS: 0% CPU, an empty log, no output ever, indistinguishable
  # from a hang until `ps` shows the state as `T`.  `lein test` has no use for
  # stdin, so give it none.
  env "${envv[@]}" lein test "$SELECTOR" < /dev/null 2>&1 | tee "$log" | ns_marks &
  child_pid=$!
  child_pgid=$(ps -o pgid= -p "$child_pid" 2>/dev/null | tr -d ' ')
  child_pgid="${child_pgid:-$child_pid}"
  wait "$child_pid" 2>/dev/null                    # 2>/dev/null: the job-done notice
  code=$?
  child_pid=""
  child_pgid=""
  DONE_RUNS+=("$backend")
  elapsed=$((SECONDS - start))

  # the two lines clojure.test prints last, tightened into one column; absent
  # when the run died before reaching them
  summary=$(grep -aE '^Ran [0-9]+ tests' "$log" | tail -1 \
              | sed -E 's/^Ran ([0-9]+) tests containing ([0-9]+) assertions\.?$/\1 tests, \2 assertions/')
  counts=$(grep -aE '^[0-9]+ failures, [0-9]+ errors' "$log" | tail -1 | sed 's/\.$//')

  if [[ $code -eq 0 ]]; then mark="$TICK"; else mark="$CROSS"; FAILED+=("$backend"); fi
  printf '  %s %-16s %-52s %s\n' \
    "$mark" "$backend" "${summary:-did not finish}${counts:+, $counts}" "$(hms $elapsed)"

  # what failed, again, under the run's own summary — the marks above have
  # scrolled by the time an eight-run matrix ends
  if [[ $code -ne 0 ]]; then
    while read -r ns; do
      [[ -z "$ns" ]] && continue
      printf '      %s %s\n' "$CROSS" "$ns"
    done < <(grep -aoE '^lein test :only [a-zA-Z0-9._-]+/' "$log" \
               | sed -E 's|^lein test :only ||; s|/$||' | sort -u)
  fi

  [[ $KEEP -eq 1 || -z "$diskdir" ]] || rm -rf "$diskdir"
  if [[ $code -ne 0 && $FAIL_FAST -eq 1 ]]; then
    echo; echo "${RED}stopping: --fail-fast${OFF}"; break
  fi
done

echo
if [[ ${#FAILED[@]} -eq 0 ]]; then
  echo "${GREEN}${BOLD}all ${#BACKENDS[@]} backends green${OFF}  ${DIM}($OUT_DIR/)${OFF}"
  exit 0
fi
echo "${RED}${BOLD}${#FAILED[@]} of ${#BACKENDS[@]} failed:${OFF} ${FAILED[*]}"
for b in "${FAILED[@]}"; do echo "  ${DIM}$OUT_DIR/$b.log${OFF}"; done
exit 1

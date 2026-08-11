#!/usr/bin/env bash
# scripts/test-sweeps.sh — run the whole suite once per ALTERNATIVE IMPLEMENTATION
# and report a ✔ / ✘ per test namespace as it goes, then one per run.
#
# The other axis the suite can be run on.  `test-backends.sh` varies where the
# sentexes live; this varies which implementation answers, holding storage at the
# default.  Five switches `test_util.clj` reads each re-run the whole suite through
# a component the engine otherwise picks for itself:
#
#   tms-dense      VAELII_TEST_TMS=dense        the dense JTMS instead of the map one
#   rete           VAELII_RETE=1                the RETE-ish sweep instead of the
#                                               re-derivation fixpoint
#   query-engine   VAELII_QUERY_ENGINE=…        the node engine instead of the goal-stack DFS
#   tactician      …plus VAELII_QUERY_STRATEGY  one of the node engine's orderings
#   hier-off       VAELII_HIER=0                the reference nested fan-out instead of
#                                               the set-algebra context retrieval
#
# Each is a COST decision rather than a semantic one — a tactician orders goals, it
# does not choose answers — so the suite must be **failing-set-identical** across all
# five and against a plain `lein test`.  A sweep that answers differently is a bug in
# the alternative, not a feature of it: running these by hand is what found a clash
# reported against a different sentex depending on which retrieval path answered.
#
# The ASSERTION COUNT is not identical here, and that is the one place this differs
# from `test-backends.sh`, where it is.  A handful of assertions pin an artifact of
# one implementation and stand aside under the switch that replaces it, through
# `tu/query-engine-override` — `prove` returns one solution per derivation and the
# node engine returns one per answer, so counting `prove`'s results is a DFS
# question (docs/inference.md).  Every such stand-aside says why at the call site.
# A count that moves for any other reason is a run that skipped something.
#
# WHY THIS IS A SCRIPT AND NOT A CI JOB.  It is both, and the local one is the
# gate.  `deep.yml` runs these five and the eight backends on a runner, which is
# 209 job-minutes against a 2,000-minute monthly allowance — nine runs a month,
# for a matrix a release wants once.  The same coverage here costs wall time and
# no money, so the CI job is the confirmation and this is what you run before a
# cut.  `lein gate` covers neither: it is one backend and every switch at its
# default, which is what keeps it a check you run before every landing.
#
# Runs are SEQUENTIAL, for the reason `test-backends.sh` gives: `VAELII_TEST_SPACE`
# admits six non-overlapping blocks and every run here takes the default one.
#
# A leading-colon argument is a TEST SELECTOR passed straight to `lein test`.
# `:default` — what a bare run takes — skips the `^:slow` tests; `:all` is the
# one to run before a release, and the one `deep.yml` uses.  A non-default
# selector writes `<sweep>.<selector>.log`, so passes at two selectors sit beside
# each other.
#
# Usage:
#   ./scripts/test-sweeps.sh                     # all five, :default
#   ./scripts/test-sweeps.sh :all                # all five, slow tests included
#   ./scripts/test-sweeps.sh query-engine        # only this one
#   ./scripts/test-sweeps.sh :all rete tms-dense
#   ./scripts/test-sweeps.sh --fail-fast
#
# Env:
#   TEST_SWEEPS_OUT   log directory (default target/test-sweeps)
#
# ^C stops the suite that is running and then the script.
#
# Exit: 0 when every sweep passed, 1 when one failed, 130 when interrupted.

set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

# shellcheck source=scripts/lib/suite-marks.sh
. scripts/lib/suite-marks.sh

# name -> the env assignments that select it, space-separated.  Kept as parallel
# arrays rather than an associative array: bash 3.2 is what macOS ships, and
# `declare -A` is bash 4.  The order is cheapest-first, so a matrix that is going
# to fail on the retrieval switch says so before spending twenty minutes on the
# node engine.
SWEEP_NAMES=(tms-dense rete hier-off query-engine tactician)
SWEEP_ENVS=(
  "VAELII_TEST_TMS=dense"
  "VAELII_RETE=1"
  "VAELII_HIER=0"
  "VAELII_QUERY_ENGINE=inference"
  "VAELII_QUERY_ENGINE=inference VAELII_QUERY_STRATEGY=breadth-first"
)

env_for() {                                        # name -> its assignments, or ""
  local want="$1" i
  for i in "${!SWEEP_NAMES[@]}"; do
    [[ "${SWEEP_NAMES[$i]}" == "$want" ]] && { printf '%s' "${SWEEP_ENVS[$i]}"; return 0; }
  done
  return 1
}

FAIL_FAST=0
SELECTOR=":default"
WANTED=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    --fail-fast) FAIL_FAST=1; shift ;;
    -h|--help) awk 'NR>1 && /^#/ {sub(/^# ?/, ""); print; next} NR>1 {exit}' "$0"; exit 0 ;;
    # checked here rather than left to lein, which answers an unknown selector with
    # "Please specify :test-selectors in project.clj" — true, and not the problem
    :all|:slow|:default) SELECTOR="$1"; shift ;;
    :*) echo "unknown selector $1 (:all, :slow, :default)" >&2; exit 2 ;;
    -*) echo "unknown flag $1 (try --help)" >&2; exit 2 ;;
    # named here rather than at run time: an unknown sweep would otherwise run the
    # suite with no switch set at all and report a clean pass for a configuration
    # nothing ran, which is the exact failure the switches' own domains refuse
    *) env_for "$1" >/dev/null \
         || { echo "unknown sweep $1 (${SWEEP_NAMES[*]})" >&2; exit 2; }
       WANTED+=("$1"); shift ;;
  esac
done

if [[ ${#WANTED[@]} -gt 0 ]]; then
  SWEEPS=("${WANTED[@]}")
else
  SWEEPS=("${SWEEP_NAMES[@]}")
fi

OUT_DIR="${TEST_SWEEPS_OUT:-target/test-sweeps}"
mkdir -p "$OUT_DIR"

RUN_NS_COUNT=$(selected_ns_count "$SELECTOR")

# ^C stops the run in progress AND the script; `test-backends.sh` carries the long
# form of why neither half is automatic.  In short: the suite runs in the
# background so a trap can interrupt the `wait`, and `set -m` gives it its own
# process group so one signal reaches the `lein` wrapper, its JVM, the project JVM
# it forks, and the readers on the pipe.
set -m
child_pid=""
child_pgid=""
current_sweep=""
current_log=""
FAILED=()
DONE_RUNS=()

# Two codes for one fact: shellcheck 0.10 split "this function is never called"
# out of SC2317 into SC2329, so naming only the new one leaves the script red on
# every older shellcheck — including the one ubuntu-latest ships.
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
  echo "  ${RED}^C${OFF} ${DIM}stopping ${current_sweep:-the run}${OFF}"
  { stop_child; [[ -n "$child_pid" ]] && wait "$child_pid"; } 2>/dev/null
  [[ -n "$current_log" ]] && echo "  ${DIM}partial log: $current_log${OFF}"
  echo
  echo "${RED}interrupted${OFF} ${DIM}after ${#DONE_RUNS[@]} of ${#SWEEPS[@]}${OFF}"
  exit 130
}
trap on_interrupt INT TERM

echo "${BOLD}running the suite on ${#SWEEPS[@]} sweep(s)${OFF}" \
     "${DIM}$SELECTOR — $RUN_NS_COUNT of $NS_COUNT namespaces${OFF}"
echo "${DIM}logs in $OUT_DIR/${OFF}"
echo

for sweep in "${SWEEPS[@]}"; do
  if [[ "$SELECTOR" == ":default" ]]; then
    log="$OUT_DIR/$sweep.log"
  else
    log="$OUT_DIR/$sweep${SELECTOR/:/.}.log"
  fi
  current_sweep="$sweep"
  current_log="$log"

  # as an `env` argument list rather than an assignment prefix: a prefix is
  # recognized before expansion, so one built from a variable cannot be used.
  # Word-splitting is exactly what is wanted here — the tactician row is two
  # assignments, and neither ever contains a space.
  # shellcheck disable=SC2207
  envv=( $(env_for "$sweep") )

  # the command verbatim, so a run can be reproduced by copying the line, and the
  # log it is going to — printed BEFORE the run, so a suite still going is already
  # tailable
  echo "  ${DIM}env ${envv[*]} lein test $SELECTOR  # $log${OFF}"
  echo "  ${DIM}loading a JVM and all $NS_COUNT test namespaces; the first mark waits on that${OFF}"
  start=$SECONDS
  # `< /dev/null` is what keeps it RUNNING: `set -m` puts the job outside the
  # terminal's foreground group and leiningen pumps its own stdin into the project
  # subprocess, so a run that reads the tty takes SIGTTIN and the whole group stops
  # — 0% CPU and an empty log, indistinguishable from a hang.
  # the stamp first, then append: a log has to say what it was run *against*, or a
  # count that moved because the tree moved is indistinguishable from one that moved
  # because a run skipped something
  revision_stamp > "$log"
  env "${envv[@]}" lein test "$SELECTOR" < /dev/null 2>&1 | tee -a "$log" | ns_marks &
  child_pid=$!
  child_pgid=$(ps -o pgid= -p "$child_pid" 2>/dev/null | tr -d ' ')
  child_pgid="${child_pgid:-$child_pid}"
  wait "$child_pid" 2>/dev/null                    # 2>/dev/null: the job-done notice
  code=$?
  child_pid=""
  child_pgid=""
  DONE_RUNS+=("$sweep")
  elapsed=$((SECONDS - start))

  summary=$(run_summary "$log")
  counts=$(run_counts "$log")

  if [[ $code -eq 0 ]]; then mark="$TICK"; else mark="$CROSS"; FAILED+=("$sweep"); fi
  printf '  %s %-16s %-52s %s\n' \
    "$mark" "$sweep" "${summary:-did not finish}${counts:+, $counts}" "$(hms $elapsed)"

  if [[ $code -ne 0 ]]; then
    while read -r ns; do
      [[ -z "$ns" ]] && continue
      printf '      %s %s\n' "$CROSS" "$ns"
    done < <(failing_namespaces "$log")
  fi

  if [[ $code -ne 0 && $FAIL_FAST -eq 1 ]]; then
    echo; echo "${RED}stopping: --fail-fast${OFF}"; break
  fi
done

echo
if [[ ${#FAILED[@]} -eq 0 ]]; then
  echo "${GREEN}${BOLD}all ${#SWEEPS[@]} sweeps green${OFF}  ${DIM}($OUT_DIR/)${OFF}"
  exit 0
fi
echo "${RED}${BOLD}${#FAILED[@]} of ${#SWEEPS[@]} failed:${OFF} ${FAILED[*]}"
for s in "${FAILED[@]}"; do
  if [[ "$SELECTOR" == ":default" ]]; then
    echo "  ${DIM}$OUT_DIR/$s.log${OFF}"
  else
    echo "  ${DIM}$OUT_DIR/$s${SELECTOR/:/.}.log${OFF}"
  fi
done
exit 1

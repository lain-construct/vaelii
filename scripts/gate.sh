#!/usr/bin/env bash
# scripts/gate.sh — everything that can say "no", behind `lein gate`.
#
#   lint   static analysis           (scripts/lint.sh — glossary, links, drift,
#                                     clj-kondo, cljfmt, shellcheck)
#   test   the suite                 (`lein test`, `:default` selector, memory stores)
#   perf   the scaling claims        (`lein perf` — growth ratios, not milliseconds)
#
# The `:default` selector, so the gate is a check you actually run before every
# landing rather than one you skip because it costs ten minutes.  Two things that
# buys back are **yours to run**, not the gate's:
#
#   - `lein test :all` — the `^:slow` tests, which carry more than half the
#     assertions (project.clj).  Worth a run when a change touches inference,
#     indexing or the TMS, and worth one occasionally regardless: a mark defers a
#     test and the deferral is only honest if somebody eventually runs it.
#   - `./scripts/test-backends.sh` — the eight record×index pairs plus the overlay
#     decorator.  **Anything touching storage, the index, records, or recovery must
#     run this**; the suite must be failing-set-identical across all eight, and the
#     memory-store run the gate does is one of the eight.
#
# `lein gate --all` runs the test stage at `:all` when you want the long version
# from here.
#
# Three checks that answer three different questions — is it well-formed, is it
# right, is it still fast — and a change can break any one of them without
# touching the others.  Running them together is the point: the one that has
# historically gone unnoticed is `perf`, because nothing fails when a cost
# quietly turns quadratic.
#
# NOT fail-fast by default, and that is the main decision here.  The suite takes
# minutes; stopping at the first failure means fixing lint, waiting out the
# tests, finding a test failure, waiting again, then finding the perf one —
# three full cycles to learn what one run already knew.  So every stage runs,
# each one's output is captured, and the report at the end names all of them.
# `--fail-fast` when you would rather stop.
#
#   lein gate                  # all three, full report
#   lein gate --fail-fast      # stop at the first failure
#   lein gate --quick          # perf: one attempt, widened bound (a pre-commit read)
#   lein gate --skip test      # drop a stage; repeatable
#   lein gate --only perf      # run one; repeatable
#   lein gate --all            # test stage at `:all` — the ^:slow tests too
#   lein gate --jobs 4         # test shards (default: cores - 2; 1 = one JVM)
#   lein gate --sequential     # the old shape: one test JVM, one stage at a time
#
# SHAPE.  `lint` and `test` run **concurrently**, then `perf` alone.  Two reasons it
# is that split and not all three at once:
#
#   - lint is static analysis and test is a JVM suite; neither can perturb the
#     other's answer, so lint is a free minute inside the suite's wall clock.
#   - **perf runs alone on purpose.**  It judges growth ratios rather than
#     milliseconds, which is what makes it machine-independent — but a reading taken
#     while eight test JVMs saturate the box is noise, and a perf gate that goes
#     amber under its own harness is one nobody trusts.  It is ~40s; that is a cheap
#     price for a number that means something.
#
# The test stage itself is sharded across JVMs (`scripts/test-parallel.sh`), which is
# safe because the in-memory registry isolates separate JVMs — see that script.
#
# Env:
#   GATE_OUT        log directory (default target/gate)
#   GATE_JOBS       default shard count for the test stage
#   PERF_TOLERANCE  passed to `lein perf --tolerance` — raise it on a loaded box
#
# Each stage streams to its own log, printed as it starts, so the run is
# tailable while it goes.  A failing stage prints the tail of its log inline;
# the whole log is always on disk.
#
# Exit: 0 when every stage passed, 1 when one failed, 130 when interrupted.
set -uo pipefail   # NOT -e: every stage must run even after one fails.

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1

OUT="${GATE_OUT:-target/gate}"
TAIL_LINES=40

fail_fast=0; quick=0; all=0; sequential=0; jobs="${GATE_JOBS:-}"; skip=(); only=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --fail-fast) fail_fast=1; shift ;;
    --quick)     quick=1; shift ;;
    --all)       all=1; shift ;;
    --sequential) sequential=1; shift ;;
    --jobs)      [[ $# -ge 2 ]] || { echo "gate: --jobs needs a value" >&2; exit 2; }
                 jobs="$2"; shift 2 ;;
    # A value is REQUIRED. `shift 2` on a one-element stack shifts nothing and
    # returns 1, so `while [[ $# -gt 0 ]]` never advances and `gate --skip` spins
    # forever instead of complaining.
    --skip)      [[ $# -ge 2 ]] || { echo "gate: --skip needs a value" >&2; exit 2; }
                 skip+=("$2"); shift 2 ;;
    --only)      [[ $# -ge 2 ]] || { echo "gate: --only needs a value" >&2; exit 2; }
                 only+=("$2"); shift 2 ;;
    -h|--help)   sed -n '2,52p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "gate: unknown argument $1" >&2; exit 2 ;;
  esac
done

# Colour: VAELII_COLOR=always|never forces; otherwise on for a capable terminal.
# `lein gate` pipes our stdout, so key off TERM as well as `-t 1` — TERM survives
# the pipe where the tty test does not.
color=0
case "$(printf '%s' "${VAELII_COLOR:-}" | tr '[:upper:]' '[:lower:]')" in
  always) color=1 ;;
  never)  color=0 ;;
  *) [[ -z "${NO_COLOR:-}" && -z "${CI:-}" \
        && ( -t 1 || ( -n "${TERM:-}" && "${TERM:-}" != dumb ) ) ]] && color=1 ;;
esac
if [[ $color -eq 1 ]]; then
  GREEN=$'\e[32m'; RED=$'\e[1;31m'; DIM=$'\e[2m'; BOLD=$'\e[1m'; RST=$'\e[0m'
else
  GREEN=''; RED=''; DIM=''; BOLD=''; RST=''
fi

trap 'echo; echo "${RED}gate interrupted${RST}"; exit 130' INT

# Both loops are guarded on the array's length rather than expanding it blind:
# this is bash 3.2 (what macOS ships), where `"${a[@]}"` on an *empty* array under
# `set -u` is an unbound-variable error rather than an empty list.
wanted () {                    # is stage $1 in this run?
  local s="$1" x
  if [[ ${#only[@]} -gt 0 ]]; then
    for x in "${only[@]}"; do [[ "$x" == "$s" ]] && return 0; done
    return 1
  fi
  if [[ ${#skip[@]} -gt 0 ]]; then
    for x in "${skip[@]}"; do [[ "$x" == "$s" ]] && return 1; done
  fi
  return 0
}

mkdir -p "$OUT" || exit 1
pass=0; fail=0; failed=(); skipped=()

announce () {                  # announce <name> <blurb>
  printf '%s==>%s %s%-5s%s %s%s  # %s%s\n' \
    "$BOLD" "$RST" "$BOLD" "$1" "$RST" "$DIM" "$2" "$OUT/$1.log" "$RST"
}

report_stage () {              # report_stage <name> <exit-code> <seconds>
  local name="$1" code="$2" t1="$3" log="$OUT/$1.log"
  if [[ $code -eq 0 ]]; then
    printf '    %s✓%s %-5s %s[%ds]%s\n' "$GREEN" "$RST" "$name" "$DIM" "$t1" "$RST"
    pass=$((pass + 1))
  else
    printf '    %s✗ %-5s FAILED (exit %d)%s %s[%ds]%s\n' \
      "$RED" "$name" "$code" "$RST" "$DIM" "$t1" "$RST"
    printf '%s' "$DIM"
    while IFS= read -r line; do printf '      %s\n' "$line"; done \
      < <(tail -n "$TAIL_LINES" "$log")
    printf '%s' "$RST"
    fail=$((fail + 1)); failed+=("$name")
  fi
}

run_stage () {                 # run_stage <name> <blurb> <cmd...>
  local name="$1" blurb="$2"; shift 2
  if ! wanted "$name"; then skipped+=("$name"); return 0; fi

  local t0 code
  announce "$name" "$blurb"
  t0=$SECONDS
  # Captured, never piped: a pipeline reports the *last* command's status, which
  # is how a green gate over a red suite happens.
  "$@" >"$OUT/$name.log" 2>&1
  code=$?
  report_stage "$name" "$code" "$((SECONDS - t0))"
  [[ $code -ne 0 && $fail_fast -eq 1 ]] && return 1
  return 0
}

# The reflection ratchet's other half.  `scripts/check-reflection.sh` compiles src and
# bench; the **test tree** is compiled by `lein test` itself under the same
# `*warn-on-reflection*`, so its warnings are already in this stage's log and reading
# them costs nothing.  Compiling the test tree in the lint pass instead would take it
# from 8 seconds to 74.  The split is stated in that script's header, and this is the
# half it names — the incident the whole ratchet exists for happened in `test/`.
check_test_reflection () {
  wanted test || return 0
  [[ -r "$OUT/test.log" ]] || return 0
  local t0=$SECONDS rc=0
  REFLECTION_LOG="$OUT/test.log" bash scripts/check-reflection.sh \
    >"$OUT/reflect.log" 2>&1 || rc=$?
  report_stage reflect "$rc" "$((SECONDS - t0))"
}

# One test JVM under `--sequential`, and under `--fail-fast` too: stopping at the
# first failure is a claim about *order*, and there is no order among stages that
# started together.
[[ $fail_fast -eq 1 ]] && sequential=1

if [[ $sequential -eq 1 ]]; then
  test_cmd=(lein test); [[ $all -eq 1 ]] && test_cmd+=(:all)
else
  test_cmd=(scripts/test-parallel.sh); [[ $all -eq 1 ]] && test_cmd+=(:all)
  [[ -n "$jobs" ]] && test_cmd+=(--jobs "$jobs")
fi
test_blurb="the suite$([[ $all -eq 1 ]] && echo " (:all)")$([[ $sequential -eq 0 ]] && echo ", sharded")"

perf_args=(perf)
[[ $quick -eq 1 ]] && perf_args+=(--quick)
[[ -n "${PERF_TOLERANCE:-}" ]] && perf_args+=(--tolerance "$PERF_TOLERANCE")

if [[ $sequential -eq 1 ]]; then
  # Cheapest first, so `--fail-fast` gets you the fast answer first.
  run_stage lint "static analysis" lein lint || true
  [[ $fail -gt 0 && $fail_fast -eq 1 ]] || run_stage test "$test_blurb" "${test_cmd[@]}" || true
  check_test_reflection
  [[ $fail -gt 0 && $fail_fast -eq 1 ]] || run_stage perf "the scaling claims" lein "${perf_args[@]}" || true
else
  # lint ‖ test, then perf alone — see SHAPE at the top.
  lint_pid=""; test_pid=""; lint_t0=0; test_t0=0
  if wanted lint; then
    announce lint "static analysis"
    lint_t0=$SECONDS
    ( lein lint >"$OUT/lint.log" 2>&1 ) & lint_pid=$!
  else skipped+=(lint); fi
  if wanted test; then
    announce test "$test_blurb"
    test_t0=$SECONDS
    ( "${test_cmd[@]}" >"$OUT/test.log" 2>&1 ) & test_pid=$!
  else skipped+=(test); fi

  # Joined in the order they were announced, so the report reads top to bottom.
  if [[ -n "$lint_pid" ]]; then
    wait "$lint_pid"; report_stage lint "$?" "$((SECONDS - lint_t0))"
  fi
  if [[ -n "$test_pid" ]]; then
    wait "$test_pid"; report_stage test "$?" "$((SECONDS - test_t0))"
  fi
  check_test_reflection

  run_stage perf "the scaling claims" lein "${perf_args[@]}" || true
fi

echo
if [[ ${#skipped[@]} -gt 0 ]]; then
  printf '%sskipped: %s%s\n' "$DIM" "${skipped[*]}" "$RST"
fi
if [[ $fail -eq 0 ]]; then
  printf '%s✓ gate passed%s — %d stage(s), logs in %s\n' "$GREEN" "$RST" "$pass" "$OUT"
  exit 0
fi
printf '%s✗ gate failed%s — %s (%d of %d) — full output in %s\n' \
  "$RED" "$RST" "${failed[*]}" "$fail" "$((pass + fail))" "$OUT"
exit 1

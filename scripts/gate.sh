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
#   lein gate --quick          # perf on its small size pair (a pre-commit read)
#   lein gate --skip test      # drop a stage; repeatable
#   lein gate --only perf      # run one; repeatable
#   lein gate --all            # test stage at `:all` — the ^:slow tests too
#
# Env:
#   GATE_OUT        log directory (default target/gate)
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

fail_fast=0; quick=0; all=0; skip=(); only=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --fail-fast) fail_fast=1; shift ;;
    --quick)     quick=1; shift ;;
    --all)       all=1; shift ;;
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

run_stage () {                 # run_stage <name> <blurb> <cmd...>
  local name="$1" blurb="$2"; shift 2
  if ! wanted "$name"; then skipped+=("$name"); return 0; fi

  local log="$OUT/$name.log" t0 t1 code
  printf '%s==>%s %s%-5s%s %s%s  # %s%s\n' \
    "$BOLD" "$RST" "$BOLD" "$name" "$RST" "$DIM" "$blurb" "$log" "$RST"
  t0=$SECONDS
  # Captured, never piped: a pipeline reports the *last* command's status, which
  # is how a green gate over a red suite happens.
  "$@" >"$log" 2>&1
  code=$?
  t1=$((SECONDS - t0))

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
    [[ $fail_fast -eq 1 ]] && return 1
  fi
  return 0
}

test_args=(test)
[[ $all -eq 1 ]] && test_args+=(:all)

perf_args=(perf)
[[ $quick -eq 1 ]] && perf_args+=(--quick)
[[ -n "${PERF_TOLERANCE:-}" ]] && perf_args+=(--tolerance "$PERF_TOLERANCE")

# Cheapest first, so `--fail-fast` gets you the fast answer first.
run_stage lint "static analysis"    lein lint || true
[[ $fail -gt 0 && $fail_fast -eq 1 ]] || run_stage test "the suite$([[ $all -eq 1 ]] && echo " (:all)")" lein "${test_args[@]}" || true
[[ $fail -gt 0 && $fail_fast -eq 1 ]] || run_stage perf "the scaling claims" lein "${perf_args[@]}" || true

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

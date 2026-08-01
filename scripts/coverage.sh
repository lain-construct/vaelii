#!/usr/bin/env bash
# scripts/coverage.sh — run cloverage over vaelii core and report the
# total form/line coverage %.
#
# Thin wrapper over `lein cloverage` (the task is added by injecting
# lein-cloverage into the root :plugins via `update-in` — see CLOVERAGE_VERSION
# below for why the :dev-profile declaration alone isn't enough). Cloverage
# instruments every namespace under
# src/main/clojure, runs the test suite against the instrumented code, writes
# an HTML report, and prints a console summary table. This script:
#   - runs it under +test (so the :test env + cleanup injections apply, exactly
#     like `lein test`; cloverage is NOT the `test` task, so :test is not
#     auto-merged — we add it explicitly),
#   - uses the project's `:default` test selector by default (drops :slow /
#     :perf, same as the routine `lein test` loop),
#   - parses the "ALL FILES" row and prints % Forms and % Lines.
#
# Because it instruments the whole core tree and runs the full suite, a run is
# much slower and heavier than `lein test` — expect minutes, not seconds.
#
# Usage:
#   ./scripts/coverage.sh                  # :default selector
#   ./scripts/coverage.sh :all             # any leading-colon arg overrides the selector
#   ./scripts/coverage.sh :fast
#   ./scripts/coverage.sh --fail-under 70  # exit non-zero if min(forms,lines) < 70%
#   ./scripts/coverage.sh -- -n 'vaelii\.lang.*'   # pass everything after -- straight to cloverage
#
# Env:
#   COVERAGE_PROFILE  Leiningen profile string (default "+test"; memory backend).
#                     For another backend, put +test LAST so its :test env (the
#                     ./kb/<backend>-test paths) wins the merge — a backend
#                     profile listed after +test overrides the path and the run
#                     would hit the REAL ./kb/<backend> dir:
#                       COVERAGE_PROFILE=+disk-local,+test ./scripts/coverage.sh
#   COVERAGE_EXCLUDE  Space-separated -e regexes for namespaces cloverage can't
#                     instrument (default: the two known "Method code too large!"
#                     namespaces). Set empty to disable exclusions.
#
# Output:
#   target/coverage/index.html    HTML report (gitignored under /target/)
#   testbench/coverage/run.log    raw cloverage output (gitignored under /testbench/)

set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

# lein-cloverage version, injected into the ROOT :plugins below. Keep in sync
# with project.clj's `:dev {:plugins [[lein-cloverage …]]}`. The plugin declared
# in :dev does NOT register the `cloverage` task when invoked through
# `with-profile +test` on lein 2.9.8 (profile-level plugins aren't resolved as
# tasks there), so we add it to the root via `update-in` instead of relying on
# :dev being active.
CLOVERAGE_VERSION="${CLOVERAGE_VERSION:-1.2.4}"

PROFILE="${COVERAGE_PROFILE:-+test}"
SELECTOR=":default"
FAIL_UNDER=""
PASSTHROUGH=()

# Args: a leading-colon token sets the selector, --fail-under N sets the
# threshold, and everything after a literal `--` is forwarded to cloverage.
while [[ $# -gt 0 ]]; do
  case "$1" in
    --) shift; PASSTHROUGH+=("$@"); break ;;
    --fail-under) FAIL_UNDER="$2"; shift 2 ;;
    --fail-under=*) FAIL_UNDER="${1#*=}"; shift ;;
    :*) SELECTOR="$1"; shift ;;
    *) PASSTHROUGH+=("$1"); shift ;;
  esac
done

OUT_DIR="${OUT_DIR:-./testbench/coverage}"
mkdir -p "$OUT_DIR"
LOG="$OUT_DIR/run.log"

CLOVERAGE_ARGS=(--no-colorize --selector "$SELECTOR")
[[ -n "$FAIL_UNDER" ]] && CLOVERAGE_ARGS+=(--fail-threshold "$FAIL_UNDER")

# Namespaces cloverage cannot handle, in two failure classes:
#
#   1. "Method code too large!" — a top-level form (a big defprotocol /
#      native-interop block / huge hiccup-rendering defn), once cloverage wraps
#      it for tracking, macroexpands into a single method that overflows the
#      JVM's 64 KB per-method bytecode limit:  kv, asp.clingo, browser.browser.
#   2. Broken protocol dispatch — a defrecord/deftype that inline-implements a
#      protocol defined in the SAME file loses its method table under cloverage's
#      per-form eval, so calls throw "No implementation of method ... found for
#      class ..." at test time:  index-trie, cache, writer-lease (every core ns
#      with both a defprotocol and a defrecord/deftype in one file).
#
# All load fine uninstrumented, so we load-but-don't-cover them rather than lose
# the run. Add more anchored regexes here if a new namespace trips either limit.
# Override the whole set with COVERAGE_EXCLUDE (space-separated regexes); set it
# empty to disable exclusions.
DEFAULT_EXCLUDE='^vaelii\.impl\.kv$ ^vaelii\.impl\.asp\.clingo$ ^vaelii\.browser\.browser$ ^vaelii\.impl\.index-trie$ ^vaelii\.impl\.cache$ ^vaelii\.impl\.writer-lease$'
for ns in ${COVERAGE_EXCLUDE-$DEFAULT_EXCLUDE}; do
  CLOVERAGE_ARGS+=(-e "$ns")
done

# bash 3.2 (macOS) errors on "${arr[@]}" when arr is empty under `set -u`,
# so only splice the pass-through args when there are any.
[[ ${#PASSTHROUGH[@]} -gt 0 ]] && CLOVERAGE_ARGS+=("${PASSTHROUGH[@]}")

PLUGIN_INJECT=(update-in :plugins conj "[lein-cloverage \"$CLOVERAGE_VERSION\"]" --)

echo "lein ${PLUGIN_INJECT[*]} with-profile $PROFILE cloverage ${CLOVERAGE_ARGS[*]}  #-> $LOG"
echo "(instruments all of src/main/clojure + runs the suite — this takes a while)"
echo

# tee so the user sees live progress; PIPESTATUS keeps lein's real exit code.
# `update-in :plugins conj … --` adds lein-cloverage to the ROOT :plugins so the
# `cloverage` task resolves (see CLOVERAGE_VERSION note above).
lein "${PLUGIN_INJECT[@]}" with-profile "$PROFILE" cloverage "${CLOVERAGE_ARGS[@]}" 2>&1 | tee "$LOG"
exit_code=${PIPESTATUS[0]}

# The summary table's total row is labelled "ALL FILES"; the two %.2f cells
# after it are % Forms and % Lines.
ALL_ROW=$(grep -aE "ALL FILES" "$LOG" | tail -1)
read -r FORMS LINES <<< "$(echo "$ALL_ROW" | grep -oE "[0-9]+\.[0-9]+" | head -2 | tr '\n' ' ')"

echo
echo "=== coverage ($SELECTOR) ==="
if [[ -n "${FORMS:-}" && -n "${LINES:-}" ]]; then
  printf "  %-9s %s%%\n" "forms:" "$FORMS"
  printf "  %-9s %s%%\n" "lines:" "$LINES"
  echo "  HTML report: target/coverage/index.html"
else
  echo "  could not parse coverage summary — see $LOG"
  [[ $exit_code -eq 0 ]] && exit_code=1
fi

exit "$exit_code"

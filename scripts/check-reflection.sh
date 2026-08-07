#!/usr/bin/env bash
# scripts/check-reflection.sh — a reflection warning fails the build instead of scrolling past.
#
# `:global-vars {*warn-on-reflection* true}` has been on for as long as the project
# has compiled, and the comment above it in `project.clj` says what that is worth:
# the flag WARNS and does not fail, nothing greps the output, and four warnings sat
# in the test tree printing on every run of every backend until somebody noticed.
# This is the grep.
#
# WHAT IT COVERS, AND WHAT COVERS THE REST.  `lein check` compiles the namespaces on
# the source path, so this pass is **`src` and `bench`** — `+bench` puts the harnesses
# on it, and they are the only reader of several density and columnar entry points.
# The **test tree is not compiled here**, deliberately: adding it takes the pass from
# 8 seconds to 74, which is longer than every other lint check combined. It is covered
# instead by `scripts/gate.sh`, which greps the test stage's own output — `lein test`
# already compiles every test namespace under the same flag, so those warnings are on
# stderr for free. Both halves are gated; neither is gated twice. Say so out loud when
# changing either, because an unstated split is how the next four warnings sit unread
# in whichever half nobody covered.
#
#   scripts/check-reflection.sh                  # compile src+bench, fail on any warning
#   REFLECTION_LOG=path/to.log scripts/…         # lint a captured log, compiling nothing
#
# The second form is what `gate.sh` uses on the test log, and what lets this script
# have a test: feed it a log with a known warning and it must exit 1.
set -uo pipefail

# The three the compiler emits under the flag.  Auto-boxing and the primitive-recur
# note are not literally reflection, but they are the same class of silent cost and
# the same fix — a hint at the call site.
readonly PATTERN='Reflection warning|Auto-boxing|recur arg for primitive'

# Third-party sources only.  A dependency whose current release still reflects is a
# fact about that dependency; ours is a defect, and every one of these is fixable at
# the call site with a type hint.  Adding one of our own files here is the thing this
# script exists to stop.  Entries are matched as fixed strings against the warning line.
readonly -a ALLOW=()

log=""
# Inline rather than a `cleanup` function: a function only a trap invokes reads as
# uncalled to shellcheck (SC2329), and silencing that would be a directive standing
# in for two lines of shell.  Single quotes, so `$log` is the value at exit.
trap '[[ -n "$log" && -z "${REFLECTION_LOG:-}" ]] && rm -f "$log"' EXIT

if [[ -n "${REFLECTION_LOG:-}" ]]; then
  log="$REFLECTION_LOG"
  if [[ ! -r "$log" ]]; then
    echo "check-reflection: cannot read REFLECTION_LOG=$log" >&2
    exit 2
  fi
else
  # The `.XXXXXX` is mandatory: BSD `mktemp -t` takes a PREFIX and appends its own
  # randomness, GNU coreutils takes a TEMPLATE and rejects fewer than three X's.  A
  # bare prefix works on macOS and dies on every Linux runner.  `set -e` is off here,
  # so a failed mktemp would leave `$log` empty and every line below would report on
  # a file that does not exist — check it rather than inherit that.  Same spelling as
  # scripts/lint.sh.
  log="$(mktemp -t vaelii-reflect.XXXXXX)" || log=""
  if [[ -z "$log" ]]; then
    echo "check-reflection: mktemp failed; no scratch file to compile into" >&2
    exit 2
  fi
  # `+bench` for the harness source path.  A profile whose dependencies clash badly
  # enough to break compilation fails here too, which is worth having.
  if ! lein with-profile +bench check >"$log" 2>&1; then
    echo "check-reflection: compilation failed — the warnings below are incidental" >&2
    tail -40 "$log" >&2
    exit 2
  fi
fi

hits="$(grep -E "$PATTERN" "$log" || true)"

if [[ -n "$hits" && ${#ALLOW[@]} -gt 0 ]]; then
  for pat in "${ALLOW[@]}"; do
    hits="$(printf '%s\n' "$hits" | grep -vF "$pat" || true)"
  done
fi

if [[ -z "$hits" ]]; then
  echo "no reflection warnings (src+bench)"
  exit 0
fi

printf '%s\n' "$hits"
printf '\n%s reflection/boxing warning(s) — hint the call site.\n' \
       "$(printf '%s\n' "$hits" | grep -c .)" >&2
exit 1

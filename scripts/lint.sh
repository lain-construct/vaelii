#!/usr/bin/env bash
# scripts/lint.sh — unified static-analysis runner behind `lein lint`.
#
# Runs every check (NOT fail-fast, so one pass surfaces every problem), captures
# each one's output + exit code, and prints a uniform report: one ✓/✗ line per
# check, a short summary on success, the full captured detail only under a FAILED
# check, and a dim [Ns] on the slow ones.  Exit non-zero iff any check failed.
#
#   - glossary    structural lint for docs/glossary.md (badges + order + links)
#   - links       relative markdown links across README + docs/ resolve
#   - drift       doc claims about the code still match the code
#   - kondo       clj-kondo over src + test + bench   (native binary)
#   - cljfmt      `lein cljfmt check` — formatting     (config in project.clj :cljfmt)
#   - shellcheck  the repo's shell scripts
#
#   lein lint               # the clean report
#   VERBOSE=1 lein lint     # also dump each check's full output, pass or fail
#   bash scripts/lint.sh -v # same, when run directly
#
# The granular `lein lint-glossary` / `lint-links` / `lint-drift` / `lint-kondo` /
# `lint-cljfmt` / `lint-shellcheck` aliases run a single check for a quick one-off.
set -uo pipefail   # NOT -e: every check must run even after one fails.

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 1

# Read the inherited VERBOSE env (or a -v arg) before normalizing it to 0/1 —
# don't reset to 0 first, that would clobber `VERBOSE=1 lein lint`.
if [[ "${1:-}" == "-v" || "${VERBOSE:-0}" == "1" ]]; then VERBOSE=1; else VERBOSE=0; fi

# Colour: VAELII_COLOR=always|never forces; otherwise on for a capable terminal
# (NO_COLOR / CI off).  `lein lint` pipes our stdout, so key off TERM as well as
# `-t 1`, since TERM survives that pipe.
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

pass=0; fail=0; failed_labels=()
# The `.XXXXXX` is mandatory, not decoration.  `-t` means two different things:
# BSD mktemp (macOS) takes a PREFIX and appends its own randomness, while GNU
# coreutils takes a TEMPLATE and rejects one with fewer than three X's.  So a
# bare `-t vaelii-lint` works here and dies on every Linux runner with "too few
# X's in template" — leaving `$out` empty, every check writing to nothing, and
# all six reported as FAILED.  A template with X's satisfies both.  Same
# spelling as vaelii-foreign's scripts/lint.sh.
out="$(mktemp -t vaelii-lint.XXXXXX)"
trap 'rm -f "$out"' EXIT

# summary <label> <outfile> — a short one-line success summary, drawn from the
# tool's own output where a figure carries info, else fixed text.
summary() {
  local label="$1" o="$2" s=""
  case "$label" in
    glossary)   s="$(grep -oE '\([0-9]+ entries\)' "$o" | head -1 | tr -d '()')" ;;
    links)      s="all resolve" ;;
    drift)      s="$(grep -oE '[0-9]+ errors, [0-9]+ warnings across [0-9]+ docs' "$o" | head -1)"
                s="${s/across /(}"; s="${s/ docs./ docs)}" ;;
    kondo)      s="$(grep -oE 'errors: [0-9]+, warnings: [0-9]+' "$o" | tail -1)" ;;
    cljfmt)     s="all files formatted" ;;
    shellcheck) s="scripts clean" ;;
  esac
  echo "${s:-ok}"
}

# print_status <label> <rc> <outfile> <seconds> — render one result row.
print_status() {
  local label="$1" rc="$2" o="$3" t="$4" tstr=""
  (( t >= 2 )) && tstr=" ${DIM}[${t}s]${RST}"
  if [[ $rc -eq 0 ]]; then
    printf '%s✓%s %s%s\n' "$GREEN" "$RST" "$(summary "$label" "$o")" "$tstr"
    pass=$((pass + 1))
    [[ $VERBOSE -eq 1 ]] && sed 's/^/        /' "$o"
  else
    printf '%s✗%s FAILED%s\n' "$RED" "$RST" "$tstr"
    sed 's/^/        /' "$o"
    [[ "$label" == cljfmt ]] && printf "        %s→ run \`lein fix\`%s\n" "$DIM" "$RST"
    fail=$((fail + 1)); failed_labels+=("$label")
  fi
}

# tool_hint <bin> — one-line install pointer for a lint dep beyond java/lein.
tool_hint() {
  case "$1" in
    clj-kondo)  echo "brew install borkdude/brew/clj-kondo (macOS), or https://github.com/clj-kondo/clj-kondo/blob/master/doc/install.md" ;;
    shellcheck) echo "brew install shellcheck (macOS), or your distro's shellcheck package" ;;
    python3)    echo "brew install python3 (macOS), or your distro's python3 package" ;;
    *)          echo "" ;;
  esac
}

# check <label> -- <cmd...> — run a check, streaming its row.  <cmd...> starts
# with the binary it needs, so a missing one is detected here once.
check() {
  local label="$1"; shift
  [[ "${1:-}" == "--" ]] && shift
  local bin="$1" hint
  printf '  %-11s ' "$label"
  SECONDS=0
  if ! command -v "$bin" >/dev/null 2>&1; then
    hint="$(tool_hint "$bin")"
    { printf '%s not found on PATH.\n' "$bin"
      [[ -n "$hint" ]] && printf 'Install: %s\n' "$hint"
    } >"$out"
    print_status "$label" 127 "$out" 0
    return
  fi
  "$@" >"$out" 2>&1
  local rc=$? t=$SECONDS
  print_status "$label" "$rc" "$out" "$t"
}

printf '%slint%s\n' "$BOLD" "$RST"

check glossary   -- bash scripts/lint-glossary.sh
check links      -- python3 scripts/check-doc-links.py --public-view
check drift      -- python3 scripts/check-doc-drift.py
check kondo      -- clj-kondo --lint src test bench
check cljfmt     -- lein cljfmt check
check shellcheck -- shellcheck scripts/lint.sh scripts/lint-glossary.sh scripts/coverage.sh \
                               scripts/gate.sh scripts/test-backends.sh scripts/update-badges.sh \
                               scripts/link-checkouts.sh

total=$((pass + fail))
if [[ $fail -eq 0 ]]; then
  printf '%slint: %d/%d clean%s\n' "$GREEN" "$pass" "$total" "$RST"
  exit 0
fi
printf '%slint: %d/%d — %s FAILED%s\n' "$RED" "$pass" "$total" "${failed_labels[*]}" "$RST"
exit 1

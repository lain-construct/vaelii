#!/usr/bin/env bash
# scripts/lint-conflict-markers.sh — fail if any tracked file carries a git
# conflict marker.
#
# A merge resolved by hand can leave a marker behind — most easily the diff3
# base line, seven pipes then a commit hash, which a three-marker eye skips.
# No other gate scans for these, so a leaked marker (and the dev hash a base
# line carries — a dev commit hash is provenance the project keeps out of
# tracked text) rides a green `lein gate` and `lein release-gate` into a squash.
#
# The three content-bearing markers are matched — the open, the base and the
# close — each seven of its character then a space or end of line.  The bare
# seven-equals separator is NOT matched: at a line start it is a Markdown
# heading underline and an ASCII rule, so matching it would false-fail on
# ordinary prose.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

pattern='^(<<<<<<<|\|\|\|\|\|\|\||>>>>>>>)( |$)'

hits="$(git grep -nE "$pattern" -- ':/' ':!scripts/lint-conflict-markers.sh' || true)"
if [[ -n "$hits" ]]; then
  echo "conflict markers in tracked files:" >&2
  echo "$hits" >&2
  exit 1
fi
echo "no conflict markers"

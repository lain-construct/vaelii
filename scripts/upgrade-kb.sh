#!/usr/bin/env bash
# scripts/upgrade-kb.sh [--verify|--trust] [--sync] [KB-DIR...] — bring each on-disk KB up to this checkout's engine,
# so the next open installs its belief instead of recovering it.
#
# Per directory this runs `lein cli upgrade --dir KB-DIR` (docs/operations.md): open the
# store under the backend its files were written by, install its reasoning image or, when
# the image was written under another image layout, other engine source or other
# policies, recover belief from the records and write a new image; then close, which
# writes the index image a rebuilt index leaves due. It prints what it found and did,
# and stops at the first directory that fails.
#
# KB-DIR defaults to checkouts/kb beside this checkout. A current KB installs its image
# and is left as it was. A stale one pays one full recover, which grows with the store.
# A KB another process holds open is refused by its single-writer lock. The heap is
# VAELII_HEAP, else half of physical memory up to 31g, and a KB over postgres records
# runs under `+with-postgres` (scripts/lib/start.sh).
#
# --verify goes to every `upgrade` run (docs/operations.md): it recovers anyway and
# reports whether belief changed. --trust keeps an image written under other engine
# source, as the browser's open does, and recovers only a KB whose records moved behind
# its images. --sync then brings the KB's shipped contexts to what this engine ships,
# which writes records.
#
# Without --sync the records are read, never rewritten: a change to the record format is
# a migration this script does not perform.
{ # one brace group, read whole before it runs: scripts/lint-shellcheck.sh says why
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=scripts/lib/start.sh
. "$ROOT/scripts/lib/start.sh"

FLAGS=()
DIRS=()
for arg in "$@"; do
  case "$arg" in
    --*) FLAGS+=("$arg") ;;
    *) DIRS+=("$arg") ;;
  esac
done
[ ${#DIRS[@]} -eq 0 ] && DIRS=("")
cd "$ROOT"
JVM_HEAP_OPTS="$(start_jvm_opts)" || exit 1
JVM_OPTS="${JVM_OPTS:-} $JVM_HEAP_OPTS"
export JVM_OPTS

for arg in "${DIRS[@]}"; do
  KB="$(start_kb_dir "$arg")" || exit 1
  PROFILES="$(start_profiles "$KB")"
  echo "upgrading $KB" >&2
  lein ${PROFILES:+with-profile "$PROFILES"} cli upgrade --dir "$KB" ${FLAGS[@]+"${FLAGS[@]}"}
done
exit
}

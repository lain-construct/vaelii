#!/usr/bin/env bash
# scripts/stage-mine.sh [--session <id>] [--records <dir>] <path>… — stage the
# hunks THIS session wrote, and none of the ones it did not.
#
# Several agents write this checkout, so a file's diff against HEAD is
# everybody's work at once. `git add <path>` takes the whole file and cannot
# tell the difference, `git add -p` is interactive and an agent has no terminal
# to answer it from, and what is left is reading hunks by hand and hoping. This
# is that reading, done mechanically.
#
# WHERE THE DELTA COMES FROM. An editor-side hook records, per session per file,
# the content at that session's FIRST touch (base) and as it LAST left it
# (after). base→after is your delta — the worktree is not, because somebody may
# have written to the file before you arrived or since you stopped. The records
# are three files per path in one directory:
#
#   <session>.<key>.base    <session>.<key>.after    <session>.<key>.path
#
# where <key> is the first 16 hex digits of the sha1 of the file's absolute
# path. The hook that writes them is machine-local and lives outside any repo,
# so nothing here hardcodes where: --records <dir>, or $EDIT_RECORDS.
#
# WHAT IT DOES, per path:
#
#   git merge-file  HEAD-blob  base  after     ->  HEAD with your delta replayed
#   git hash-object -w                         ->  that content, as a blob
#   git update-index --cacheinfo               ->  the index points at the blob
#
# THE WORKTREE IS NEVER WRITTEN. It holds both agents' work and keeps holding
# it; only the index moves. So `git status` afterwards shows your paths staged
# and the other writer's hunks still unstaged, which is exactly true, and their
# next commit takes them.
#
# A CONFLICT IS AN ANSWER, not a failure: two edits to the same lines cannot be
# separated by any means, and guessing which to keep is how one of them gets
# lost. The path is reported, the index is left alone, and the two of you sort
# out who lands first.
#
# The session id comes from --session <id>, or $CLAUDE_CODE_SESSION_ID. A hook
# that sweeps its records after a day means a delta you never staged is gone
# after that. The staging guard on the other side blocks the `git add` that
# would have swept, and prints the line to run instead — records directory and
# all — so the ordinary way to reach this script is to copy that line.
set -euo pipefail

usage() { sed -n '2,41p' "$0"; }

session="${CLAUDE_CODE_SESSION_ID:-}"
state="${EDIT_RECORDS:-}"
while [[ "${1:-}" == -* ]]; do
  case "$1" in
    --session)   session="${2:-}"; shift 2 ;;
    --session=*) session="${1#*=}"; shift ;;
    --records)   state="${2:-}"; shift 2 ;;
    --records=*) state="${1#*=}"; shift ;;
    -h|--help)   usage; exit 0 ;;
    --)          shift; break ;;
    *)           echo "unknown option: $1" >&2; exit 2 ;;
  esac
done

[[ $# -gt 0 ]] || { usage; exit 2; }
if [[ -z "$session" ]]; then
  echo "stage-mine: no session id (\$CLAUDE_CODE_SESSION_ID unset). Pass --session <id>." >&2
  exit 2
fi
if [[ -z "$state" ]]; then
  echo "stage-mine: no records directory. Pass --records <dir>, or set \$EDIT_RECORDS" >&2
  echo "  to wherever the editor's edit-tracking hook writes its base/after pairs." >&2
  exit 2
fi
if [[ ! -d "$state" ]]; then
  echo "stage-mine: $state is not a directory; no records to read." >&2
  exit 2
fi
tmp=$(mktemp -d "${TMPDIR:-/tmp}/stage-mine.XXXXXX")
trap 'rm -f "$tmp"/*; rmdir "$tmp"' EXIT

# The physical path, matching what the hook hashed: one spelling, or the record
# is filed under a name nothing looks up.
abspath() {
  local d b
  d=$(dirname -- "$1"); b=$(basename -- "$1")
  d=$(cd -- "$d" && pwd -P)
  printf '%s/%s\n' "$d" "$b"
}

key_of() {
  local k
  k=$(printf '%s' "$1" | shasum 2>/dev/null | cut -c1-16) || true
  [[ -n "$k" ]] || k=$(printf '%s' "$1" | sha1sum | cut -c1-16)
  printf '%s\n' "$k"
}

staged=0
skipped=0
last_root=""

for arg in "$@"; do
  if [[ ! -e "$arg" ]]; then
    echo "stage-mine: $arg — no such file." >&2
    skipped=$((skipped + 1)); continue
  fi
  abs=$(abspath "$arg")
  root=$(git -C "$(dirname -- "$abs")" rev-parse --show-toplevel)
  rel=${abs#"$root"/}
  last_root="$root"

  key=$(key_of "$abs")
  base="$state/$session.$key.base"
  after="$state/$session.$key.after"

  if [[ ! -f "$after" || ! -f "$base" ]]; then
    echo "stage-mine: $rel — this session has no recorded delta for it." >&2
    echo "  Nothing here knows which hunks are yours, so nothing is staged. A change" >&2
    echo "  written outside the editor leaves no record, and so does one whose record" >&2
    echo "  has aged out; read \`git diff -- $rel\` and stage it yourself." >&2
    skipped=$((skipped + 1)); continue
  fi

  if ! git -C "$root" cat-file -e "HEAD:$rel" 2>/dev/null; then
    # Not in HEAD: staging it publishes the whole file, so it has to be wholly
    # yours — which it is exactly when this session found nothing there.
    if [[ -s "$base" ]]; then
      echo "stage-mine: $rel — a new file somebody else started; your edits sit on top." >&2
      echo "  Staging it would publish their file. Leave it to them." >&2
      skipped=$((skipped + 1)); continue
    fi
    git -C "$root" add -- "$rel"
    echo "staged (new file, wholly yours): $rel"
    staged=$((staged + 1)); continue
  fi

  git -C "$root" show "HEAD:$rel" > "$tmp/ours"
  rc=0
  git merge-file -q -p "$tmp/ours" "$base" "$after" > "$tmp/merged" 2>/dev/null || rc=$?
  if [[ $rc -ge 1 && $rc -le 127 ]]; then
    echo "stage-mine: $rel — CONFLICT: your edits and another writer's touch the same lines." >&2
    echo "  $rc region(s) cannot be separated. Nothing staged for this path — wait for" >&2
    echo "  the other writer to land, or agree who goes first." >&2
    skipped=$((skipped + 1)); continue
  fi
  if [[ $rc -ne 0 ]]; then
    echo "stage-mine: $rel — git merge-file failed ($rc). Nothing staged." >&2
    skipped=$((skipped + 1)); continue
  fi

  if cmp -s "$tmp/merged" "$tmp/ours"; then
    echo "stage-mine: $rel — your delta is already in HEAD; nothing to stage."
    skipped=$((skipped + 1)); continue
  fi

  mode=$(git -C "$root" ls-files -s -- "$rel" | awk '{ print $1; exit }')
  [[ -n "$mode" ]] || mode=$(git -C "$root" ls-tree HEAD -- "$rel" | awk '{ print $1; exit }')
  blob=$(git -C "$root" hash-object -w --path "$rel" -- "$tmp/merged")
  git -C "$root" update-index --add --cacheinfo "$mode,$blob,$rel"
  echo "staged (your delta only): $rel"
  staged=$((staged + 1))
done

if [[ $staged -gt 0 && -n "$last_root" ]]; then
  echo
  echo "index now holds:"
  git -C "$last_root" diff --cached --stat | sed 's/^/  /'
  echo "The worktree is untouched — everybody else's hunks are still in the files."
fi
[[ $skipped -eq 0 ]]

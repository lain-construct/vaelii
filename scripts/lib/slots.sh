#!/usr/bin/env bash
# scripts/lib/slots.sh — how the suite runners share the box: how many JVMs one spins up by
# default, which checkout runs the heavy ones, and the one-matrix-at-a-time lock.
#
# The slot count first: how many JVMs a suite runner spins up in parallel by default,
# in one place so the two runners cannot drift: `test-parallel.sh` shards the namespaces,
# `test-matrix.sh` fans out the configurations, and both size their fan-out from here.
#
# The rule is two terms:
#
#   slots = P − 2 − (vaelii JVMs already running)        floored at 1
#
#   - **P − 2**, where P is the performance-core count read from `hw.perflevel0.logicalcpu`
#     on Apple Silicon — the performance tier alone, the efficiency cores NOT folded in.  Two
#     are held back for the concurrent `lint` stage and the OS.  On a 10-core (8P + 2E) box
#     that is 6 test JVMs, leaving two performance cores plus both efficiency cores free:
#     because P counts only performance cores, `P − 2` never reaches down into the E-cores the
#     way a naive `ncpu − 2` would.  A homogeneous box — an Intel Mac, or Linux CI — has no
#     `perflevel` key and falls back to `ncpu` / `nproc`, where `− 2` just leaves two cores
#     for everything else.
#   - **minus the vaelii JVMs already up.**  This is a shared checkout (several writers in one
#     tree) beside sibling checkouts, so a bench, a dev REPL or another gate is often already
#     eating cores.  Each such JVM is a slot this run should not also claim, so the count is
#     load-aware rather than a constant.
#
# That second term makes the answer depend on what else is running, so it is NOT the plain
# `P − 2` default — `default_slots` says so on stderr when the subtraction changes the number,
# and stays quiet on an idle box where the two agree.  The count on stdout is the only thing
# a caller captures (`jobs=$(default_slots)`); the note is stderr.
#
# Sourced, never executed:
#   . scripts/lib/slots.sh

# vaelii JVMs already running — the project / bench / dev JVMs doing work, NOT the leiningen
# launcher that spawns each (it pairs with a project JVM already counted, and is a near-idle
# bootstrap parent).  `pgrep -f` matches the full argv and excludes itself, so a bash script,
# a `tail -f` on a log or this call is never counted; the `java.*vaelii` shape keeps it to
# JVMs.  A rough estimate across this checkout AND its siblings — erring toward fewer slots.
running_vaelii_count() {
  local pids pid cmd n=0
  pids=$(pgrep -f 'java.*vaelii' 2>/dev/null) || pids=''
  for pid in $pids; do
    cmd=$(ps -o command= -p "$pid" 2>/dev/null) || continue
    case "$cmd" in
      *leiningen.core.main*) ;;   # the launcher parent; its project JVM is the one counted
      *) n=$((n + 1)) ;;
    esac
  done
  printf '%s\n' "$n"
}

default_slots() {
  local pcores=''
  # perflevel0 is the performance tier on Apple Silicon; the key is absent everywhere else.
  pcores=$(sysctl -n hw.perflevel0.logicalcpu 2>/dev/null) || pcores=''
  [[ -n "$pcores" ]] || pcores=$(sysctl -n hw.ncpu 2>/dev/null) || pcores=''
  [[ -n "$pcores" ]] || pcores=$(nproc 2>/dev/null) || pcores=''
  [[ -n "$pcores" ]] || pcores=4

  local base=$((pcores - 2)); (( base < 1 )) && base=1
  local running; running=$(running_vaelii_count)
  local slots=$((base - running)); (( slots < 1 )) && slots=1

  # Say when the load term moved the number off the plain P−2 default; quiet when it did not.
  if (( running > 0 )); then
    printf 'slots: %d vaelii JVM(s) already running — using %d, not the default P-2=%d\n' \
      "$running" "$slots" "$base" >&2
  fi
  printf '%s\n' "$slots"
}

# ---- the heavy runs belong to the primary checkout ---------------------------------------
#
# A matrix, an axis sweep or `lein perf` in a linked worktree is a second fleet of JVMs
# beside the primary's, and every runner above drops to one slot when it counts them.  So
# these run from the primary, which also owns the one matrix lock below.  A separate clone
# is not a linked worktree and is not refused.  `ALLOW_WORKTREE_RUN=1` runs one anyway,
# for a release gated in a scratch worktree at the carved sha.

# The repository's shared git directory, absolute: the primary's `.git`, from any worktree.
common_git_dir() {
  git rev-parse --path-format=absolute --git-common-dir 2>/dev/null
}

# require_primary <what> exits 3 in a linked worktree, naming the primary to run <what> from.
require_primary() {
  local own common
  own=$(git rev-parse --path-format=absolute --absolute-git-dir 2>/dev/null) || return 0
  common=$(common_git_dir) || return 0
  [[ "$own" == "$common" || -n "${ALLOW_WORKTREE_RUN:-}" ]] && return 0
  printf '%s runs from the primary checkout, %s, not from a linked worktree.\n' \
    "$1" "${common%/.git}" >&2
  printf '  Land the change, then run it there. ALLOW_WORKTREE_RUN=1 overrides.\n' >&2
  exit 3
}

# ---- one matrix at a time, and a queue for the rest --------------------------------------
#
# Two matrices at once each run at one slot, so a second request does not start a second
# matrix.  An `--owed` request that finds one running appends its baseline to the queue
# and returns; the running matrix, as it ends, starts one more over the union of the
# queued baselines, at the primary's HEAD.  The lock and the queue live in the shared git
# directory, so every worktree of the repository sees the same ones.
#
#   lock    `<pid> <revision> <epoch> <run dir>` of the matrix running now
#   queue   one `<commit> <selector> <requester>` line per request waiting for the next
#           matrix
#   red     `<epoch> <run dir>` of the last red matrix, until a green one; see below
#   jobs    the running matrix's slot count, set by `--set-jobs <n>` and re-read by its
#           scheduler every pass; taking and releasing the lock clear it, so a count
#           set for one matrix never carries into the next

matrix_state_dir() {
  local d
  d=$(common_git_dir) || return 1
  mkdir -p "$d/vaelii-matrix" 2>/dev/null || return 1
  printf '%s/vaelii-matrix\n' "$d"
}

# The lock's line when a live matrix holds it, else nothing.  A lock whose pid is gone,
# or is no longer a test-matrix, is stale and is removed.
matrix_lock_holder() {
  local dir line pid
  dir=$(matrix_state_dir) || return 0
  line=$(cat "$dir/lock" 2>/dev/null) || return 0
  pid=${line%% *}
  if [[ -n "$pid" ]] && ps -o command= -p "$pid" 2>/dev/null | grep -q 'test-matrix'; then
    printf '%s\n' "$line"
  elif [[ "$(cat "$dir/lock" 2>/dev/null)" == "$line" ]]; then
    rm -f "$dir/lock"       # only the stale line read above, not a lock taken since
  fi
}

# matrix_lock_take <revision> <run dir> takes the lock for this shell, or returns 1 while
# another matrix holds it.  noclobber makes the create atomic.
matrix_lock_take() {
  local dir
  dir=$(matrix_state_dir) || return 0
  matrix_lock_holder >/dev/null
  ( set -o noclobber; printf '%s %s %s %s\n' "$$" "$1" "$(date '+%s')" "$2" >"$dir/lock" ) \
    2>/dev/null || return 1
  rm -f "$dir/jobs"
}

matrix_lock_release() {
  local dir line
  dir=$(matrix_state_dir) || return 0
  line=$(cat "$dir/lock" 2>/dev/null) || return 0
  [[ "${line%% *}" == "$$" ]] && rm -f "$dir/lock" "$dir/jobs"
  return 0
}

# The file the running matrix re-reads its slot count from.  Its scheduler resolves the
# path once and reads it with the `read` builtin, so the one-second poll forks nothing.
matrix_jobs_file() {
  local dir
  dir=$(matrix_state_dir) || return 1
  printf '%s/jobs\n' "$dir"
}

# Who is asking for a matrix, as one word: the session id in EDIT_SESSION when the
# caller's environment sets one, else the login name.
matrix_requester() {
  if [[ -n "${EDIT_SESSION:-}" ]]; then
    printf 'session:%s\n' "$EDIT_SESSION"
  else
    printf 'user:%s\n' "${USER:-unknown}"
  fi
}

# matrix_queue_add <commit> <selector> <requester>
matrix_queue_add() {
  local dir
  dir=$(matrix_state_dir) || return 1
  printf '%s %s %s\n' "$1" "$2" "$3" >>"$dir/queue"
}

# Prints the queued requests (and empties the queue) as one `<commit> <selector>
# <requesters>`: the commit every queued baseline descends from, `:all` where the
# selectors differ, and the requesters comma-joined.  Prints nothing when the queue is
# empty.
matrix_queue_take() {
  local dir taken bases sels base sel who
  dir=$(matrix_state_dir) || return 0
  [[ -s "$dir/queue" ]] || return 0
  taken="$dir/queue.$$"
  mv "$dir/queue" "$taken" 2>/dev/null || return 0
  bases=$(cut -d' ' -f1 "$taken" | sort -u)
  sels=$(cut -d' ' -f2 "$taken" | sort -u)
  who=$(cut -d' ' -f3 "$taken" | grep -v '^$' | sort -u | paste -sd, -)
  rm -f "$taken"
  # word-split on purpose: one commit per word
  # shellcheck disable=SC2086
  if [[ $(printf '%s\n' "$bases" | wc -l) -gt 1 ]]; then
    base=$(git merge-base --octopus $bases 2>/dev/null) || base=$(printf '%s\n' "$bases" | head -1)
  else
    base=$bases
  fi
  if [[ $(printf '%s\n' "$sels" | wc -l) -gt 1 ]]; then sel=":all"; else sel=$sels; fi
  printf '%s %s %s\n' "$base" "$sel" "${who:-unknown}"
}

# ---- the cooldown after a red matrix ------------------------------------------------------
#
# A red matrix writes `red`: `<epoch> <run dir>`.  For MATRIX_RED_COOLDOWN seconds after
# it (1800 by default) a new matrix, started or queued, is refused, because a re-run that
# soon repeats the same failures.  A green matrix removes the file.

matrix_red_mark() {
  local dir
  dir=$(matrix_state_dir) || return 0
  printf '%s %s\n' "$(date '+%s')" "$1" >|"$dir/red"
}

matrix_red_clear() {
  local dir
  dir=$(matrix_state_dir) || return 0
  rm -f "$dir/red"
}

# The `red` line while the cooldown lasts, else nothing.
matrix_red_recent() {
  local dir line cool="${MATRIX_RED_COOLDOWN:-1800}"
  [[ "$cool" =~ ^[0-9]+$ ]] || cool=1800
  (( cool > 0 )) || return 0
  dir=$(matrix_state_dir) || return 0
  line=$(cat "$dir/red" 2>/dev/null) || return 0
  (( $(date '+%s') - ${line%% *} < cool )) && printf '%s\n' "$line"
  return 0
}

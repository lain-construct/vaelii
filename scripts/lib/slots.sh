#!/usr/bin/env bash
# scripts/lib/slots.sh — how many JVMs a suite runner spins up in parallel by default,
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
#   - **minus the vaelii JVMs already up.**  This is a shared checkout (several agents in one
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

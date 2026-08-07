#!/usr/bin/env bash
# scripts/run-bench-caches.sh — the corpus run of `vaelii.bench.caches`, detached.
#
# The load alone is ~11 minutes and the sweeps follow it, so this outlives the session
# that starts it: `nohup caffeinate -i scripts/run-bench-caches.sh <corpus-dir> &`.
# The log lives under target/ so it can be tailed without asking anyone, and the
# sentinel is echoed *here* rather than by the calling shell — a killed JVM must not
# report as a finished one.
set -uo pipefail

if [ $# -lt 1 ]; then
  echo "usage: $0 <corpus-dir> [profile] [chain|nochain]" >&2
  echo "  <corpus-dir> is a converted corpus — one vaelii-foreign's \`convert\` wrote." >&2
  exit 2
fi

CORPUS="$1"
PROFILE="${2:-ontology}"
CHAIN="${3:-nochain}"
# NOT under target/.  `lein clean` removes `:target-path`, and in a checkout several
# agents share, somebody else's clean unlinks a log this run is still writing to — the
# writer keeps its descriptor, so the run finishes normally and the output is simply
# gone.  testbench/ is gitignored and nothing sweeps it.
LOG="testbench/bench-caches/run.log"

mkdir -p testbench/bench-caches

{
  echo "=== bench-caches: $CORPUS at :$PROFILE ($CHAIN) ==="
  echo "=== started $(date -u '+%Y-%m-%dT%H:%M:%SZ') ==="
} >| "$LOG"

# The heap is the reason this is a script.  The :bench profile pins -Xmx6g, which a
# corpus of this size runs in only by collecting constantly — and a `JVM_OPTS` in the
# environment does NOT override it, the profile's `:jvm-opts` winning outright.  So the
# vector is edited on the way past: `update-in … conj` appends, and the JVM takes the
# last -Xmx it is given.  jol's two flags already ride in the profile.
# `with-profile` FIRST and `update-in` second, which is the order that works: the other
# way round the profile's vector is merged on top afterwards and its -Xmx6g is the last
# one the JVM sees.
lein with-profile +bench,+with-foreign update-in :jvm-opts conj '"-Xmx40g"' -- \
  run -m vaelii.bench.caches "$CORPUS" "$PROFILE" "$CHAIN" >> "$LOG" 2>&1
STATUS=$?

{
  echo
  echo "=== finished $(date -u '+%Y-%m-%dT%H:%M:%SZ') ==="
  if [ $STATUS -eq 0 ]; then
    echo "BENCH-CACHES-COMPLETE exit=0"
  else
    echo "BENCH-CACHES-FAILED exit=$STATUS"
  fi
} >> "$LOG"

exit $STATUS

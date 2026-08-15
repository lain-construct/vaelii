#!/usr/bin/env bash
# scripts/lib/suite-configs.sh — the thirteen configurations the whole suite can be run
# in, and the environment that selects each.  One table, three readers.
#
# Two axes, and they are independent (which is why they are two lists and not a
# cross-product):
#
#   BACKENDS — where the sentexes live.  Seven legal record×index pairs, spelled
#              `<records>-<index>`, plus `overlay`, which is not an eighth pair but the
#              fork decorator over an empty base (docs/overlay.md).
#   SWEEPS   — which implementation answers, storage held at the default.  Five
#              components the engine otherwise picks for itself.
#
# `test-backends.sh` runs the first list, `test-sweeps.sh` the second, and
# `test-matrix.sh` runs both at once — so the roster lives here rather than in the
# script that happened to need it first.  Adding a backend or a sweep is an edit to this
# file and to nothing else.
#
# Sourced, never executed:
#   . scripts/lib/suite-configs.sh
#
# Read by the sourcing script and by nothing here — SC2034 cannot see across a `.`.
# shellcheck disable=SC2034

# In the order they run: the three RAM-record pairs first (fast, no files), then the
# four durable-record ones — derived indexes before the durable one, so the runs that
# write least go first — then the decorator.
ALL_BACKENDS=(memory memory-dense memory-columnar
              disk-memory disk-dense disk-columnar disk
              overlay)

# Cheapest first, so a matrix that is going to fail on the retrieval switch says so
# before spending twenty minutes on the node engine.  Kept as parallel arrays rather
# than one associative array: bash 3.2 is what macOS ships, and `declare -A` is bash 4.
ALL_SWEEPS=(tms-dense rete hier-off query-engine tactician)
SWEEP_ENVS=(
  "VAELII_TEST_TMS=dense"
  "VAELII_RETE=1"
  "VAELII_HIER=0"
  "VAELII_QUERY_ENGINE=inference"
  "VAELII_QUERY_ENGINE=inference VAELII_QUERY_STRATEGY=breadth-first"
)

# backend | sweep, or nothing and a non-zero status for a name in neither list.  A
# caller checks this before running anything: an unknown name would otherwise run the
# suite with no switch set at all and report a clean pass for a configuration nothing
# ran, which is the exact failure the switches' own domains refuse.
config_kind() {
  local want="$1" b s
  for b in "${ALL_BACKENDS[@]}"; do [[ "$b" == "$want" ]] && { printf 'backend'; return 0; }; done
  for s in "${ALL_SWEEPS[@]}"; do [[ "$s" == "$want" ]] && { printf 'sweep'; return 0; }; done
  return 1
}

# The environment assignments that select a configuration, space-separated — a
# backend's one, or a sweep's one or two.  Never the disk directory: which directory a
# durable run writes to is the caller's to name, since the caller owns the run's output
# tree and two concurrent matrices must not share one.
config_env() {
  local want="$1" i
  for i in "${!ALL_BACKENDS[@]}"; do
    [[ "${ALL_BACKENDS[$i]}" == "$want" ]] && { printf 'VAELII_TEST_BACKEND=%s' "$want"; return 0; }
  done
  for i in "${!ALL_SWEEPS[@]}"; do
    [[ "${ALL_SWEEPS[$i]}" == "$want" ]] && { printf '%s' "${SWEEP_ENVS[$i]}"; return 0; }
  done
  return 1
}

# Does this configuration write a durable store?  The RECORD half is the name's prefix,
# and a RAM-only run reads no directory at all — handing it one would only put a `-D` on
# its command line that means nothing.
config_wants_disk() {
  case "$1" in
    disk|disk-*) return 0 ;;
    *) return 1 ;;
  esac
}

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
ALL_SWEEPS=(tms-reference rete hier-off query-engine tactician)
SWEEP_ENVS=(
  "VAELII_TEST_TMS=reference"
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

# ---- how many assertions a configuration is EXPECTED to run short ----------
#
# The suite is failing-set-identical across all thirteen, and the assertion COUNT moves
# only where a test says why.  `test-backends.sh` and `test-sweeps.sh` have both stated
# that for as long as they have existed; what follows is the same claim, checked.  Any
# other difference is a run that skipped something the others ran — a namespace that
# failed to load, a `deftest` that stood aside without saying so, a switch that turned a
# gate off — and every one of those reads as a green run.
#
# Two tests stand aside on purpose, and they are the whole table:
#
#   4   `profile_test/the-fan-tally-counts-what-the-walk-touched` — the `:fan` tally is
#       the one that is not index-independent, since the columnar trie walks natively and
#       counts no node probes.  It asserts that instead of standing aside (docs/profile.md).
#   8   the six `tu/query-engine-override` sites in `backward_test`, `query_test` and
#       `inference_test` — `prove` returns one solution per derivation on the DFS and one
#       per answer on the node engine, so counting its results is a DFS question.
#
# MEASURED, at both selectors, so the table does not depend on which one is running:
# `logs/test-matrix/run-92715` at `:all` puts the two columnar runs 4 below and the two
# node-engine runs 8 below, and the contributing namespaces alone reproduce both at
# `:default` (profile_test 86 -> 82, the three query namespaces 356 -> 348).  Neither
# stand-aside sits in a `^:slow` test, which is why the two selectors agree.
#
# A new stand-aside belongs here with its reason, in the commit that adds it.
config_expected_delta() {
  case "$1" in
    memory-columnar|disk-columnar) printf '4' ;;
    query-engine|tactician)        printf '8' ;;
    *)                             printf '0' ;;
  esac
}

# Check `name:assertions` pairs against that table.  Prints one line per configuration
# whose shortfall is not the expected one and returns 1; silent and 0 when they all hold.
#
# The baseline is the highest `count + expected`, not simply the highest count, and that
# is what makes a SUBSET checkable: `./scripts/test-sweeps.sh query-engine tactician`
# runs two configurations that are both expected to be 8 short, and against a bare
# maximum each would look like the full count and the other would look 0 short.
# Reconstructing the full count from every run and taking the highest gives the same
# baseline whichever configurations were asked for.
assertion_deltas_ok() {
  local pair name count baseline=0 full actual expected bad=0
  for pair in "$@"; do
    count="${pair##*:}"
    case "$count" in ''|*[!0-9]*) continue ;; esac
    full=$(( count + $(config_expected_delta "${pair%%:*}") ))
    (( full > baseline )) && baseline=$full
  done
  (( baseline == 0 )) && return 0            # nothing finished; nothing to compare
  for pair in "$@"; do
    name="${pair%%:*}"; count="${pair##*:}"
    case "$count" in ''|*[!0-9]*) continue ;; esac
    expected=$(config_expected_delta "$name")
    actual=$(( baseline - count ))
    if (( actual != expected )); then
      printf '  %-16s ran %s assertions — %s short of %s, where the table expects %s\n' \
        "$name" "$count" "$actual" "$baseline" "$expected"
      bad=1
    fi
  done
  return $bad
}

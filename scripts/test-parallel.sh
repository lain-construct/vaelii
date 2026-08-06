#!/usr/bin/env bash
# The suite across N JVMs instead of one.
#
# The test stage is the gate's long pole — 395s of a ~490s `:default` run — and it is
# one JVM walking 187 namespaces in sequence.  Splitting it is safe for one reason:
# **the in-memory registry is per-JVM**, so two runs over the same space numbers do not
# collide (docs/storage.md).  Each shard is its own `lein test`, its own KB registry,
# its own `:once` fixtures and its own net-neutrality baseline; nothing crosses.
#
# What this does NOT do, and must not:
#
#   - **Split a namespace.**  A shard is a whole number of namespaces, because a
#     `:once` fixture is what several tests in one file share.
#   - **Run the durable backends.**  Two disk suites over one directory collide on the
#     single-writer lock, and `VAELII_TEST_SPACE` admits only three non-overlapping
#     blocks — so this refuses a `VAELII_TEST_BACKEND` with a durable half rather than
#     sharding into corruption.  `scripts/test-backends.sh` is sequential on purpose
#     and stays that way.
#   - **Hide a failure.**  Every shard's exit status is read from a marker the shard
#     itself echoes, never from a pipeline (`lein test | tee` reports `tee`).  The
#     aggregate is red if any shard is.
#
# Balance comes from measured time, not guesswork: each run records how long every
# namespace took to `target/gate/test-timings.tsv`, and the next run bin-packs
# longest-first into the emptiest shard.  With no timings yet it falls back to
# round-robin, which is a worse split and still correct.
#
# Usage:
#   scripts/test-parallel.sh                 # :default, jobs = cores - 2
#   scripts/test-parallel.sh :all            # the ^:slow tests too
#   scripts/test-parallel.sh --jobs 4        # a fixed shard count
#   scripts/test-parallel.sh :all --jobs 6
set -uo pipefail

cd "$(dirname "$0")/.." || exit 1

OUT="${VAELII_GATE_OUT:-target/gate}"
TIMINGS="$OUT/test-timings.tsv"

selector=":default"
jobs=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    :*)       selector="$1"; shift ;;
    --jobs)   [[ $# -ge 2 ]] || { echo "test-parallel: --jobs needs a value" >&2; exit 2; }
              jobs="$2"; shift 2 ;;
    --jobs=*) jobs="${1#--jobs=}"; shift ;;
    *) echo "test-parallel: unknown argument $1" >&2; exit 2 ;;
  esac
done

# A durable half means one lock and three usable space blocks — not shardable.
case "${VAELII_TEST_BACKEND:-memory}" in
  *disk*)
    echo "test-parallel: VAELII_TEST_BACKEND=${VAELII_TEST_BACKEND} has a durable half." >&2
    echo "  Two disk suites over one directory collide on the single-writer lock." >&2
    echo "  Use scripts/test-backends.sh, which is sequential for this reason." >&2
    exit 2 ;;
esac

if [[ -z "$jobs" ]]; then
  cores=$( (sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 4) )
  jobs=$((cores - 2)); [[ $jobs -lt 1 ]] && jobs=1
fi

mkdir -p "$OUT" || exit 1

# ---- the namespaces ---------------------------------------------------------
# `_test.clj` only: `world.clj`, `test_util.clj` and friends are support code that
# declares no tests, and naming one would only cost a load.
namespaces=()
while IFS= read -r f; do
  ns="${f#test/}"; ns="${ns%.clj}"; ns="${ns//\//.}"; ns="${ns//_/-}"
  namespaces+=("$ns")
done < <(find test -name '*_test.clj' | sort)

n=${#namespaces[@]}
if [[ $n -eq 0 ]]; then echo "test-parallel: no test namespaces found" >&2; exit 2; fi
[[ $jobs -gt $n ]] && jobs=$n

# ---- bin-pack ---------------------------------------------------------------
# Longest-processing-time-first: sort by last run's duration descending, and hand each
# namespace to whichever shard is currently lightest.  This is the standard 4/3-optimal
# greedy, and on this suite it matters — the spread between the heaviest namespace and
# the median is large enough that round-robin leaves one shard running alone at the end.
assign_out="$OUT/.shard-assign"
awk -v jobs="$jobs" -v timings="$TIMINGS" '
  BEGIN {
    while ((getline line < timings) > 0) {
      split(line, f, "\t"); if (f[1] != "") secs[f[1]] = f[2] + 0
    }
    close(timings)
  }
  { ns[NR] = $0; w[NR] = (ns[NR] in secs) ? secs[ns[NR]] : -1 }
  END {
    # unknown namespaces get the mean, so a new test is not always packed last
    total = 0; known = 0
    for (i = 1; i <= NR; i++) if (w[i] >= 0) { total += w[i]; known++ }
    mean = (known > 0) ? total / known : 1
    for (i = 1; i <= NR; i++) if (w[i] < 0) w[i] = mean

    # selection sort by weight desc (NR is small; keeping this dependency-free)
    for (i = 1; i <= NR; i++) order[i] = i
    for (i = 1; i <= NR; i++)
      for (j = i + 1; j <= NR; j++)
        if (w[order[j]] > w[order[i]]) { t = order[i]; order[i] = order[j]; order[j] = t }

    for (b = 1; b <= jobs; b++) load[b] = 0
    for (k = 1; k <= NR; k++) {
      idx = order[k]; light = 1
      for (b = 2; b <= jobs; b++) if (load[b] < load[light]) light = b
      load[light] += w[idx]
      printf "%d\t%s\n", light, ns[idx]
    }
  }
' <(printf '%s\n' "${namespaces[@]}") > "$assign_out"

echo "running $n namespaces at $selector across $jobs shard(s) — logs in $OUT"

# ---- run --------------------------------------------------------------------
t0=$SECONDS
pids=(); shard_logs=()
for ((b = 1; b <= jobs; b++)); do
  shard_ns=()
  while IFS= read -r ns; do shard_ns+=("$ns"); done < <(awk -F'\t' -v b="$b" '$1==b {print $2}' "$assign_out")
  [[ ${#shard_ns[@]} -eq 0 ]] && continue

  log="$OUT/test.shard-$b.log"; timing="$OUT/.timing-$b.tsv"
  shard_logs+=("$log")
  # The status comes from the marker the shard echoes, never from the pipeline: `tee`
  # exits 0 over a red suite, which is exactly how a green gate hides one.
  # Namespaces first, THEN the selector: `split-selectors` splits leiningen's argv on
  # the first keyword and hands everything after a selector to that selector as its
  # own arguments — so `lein test :default <ns>` calls the `:default` predicate with
  # the namespace as a second argument and dies on arity, rather than filtering by it.
  (
    { lein test "${shard_ns[@]}" "$selector"; echo "SHARD-EXIT:$?"; } 2>&1 \
      | tee "$log" \
      | while IFS= read -r line; do
          case "$line" in
            "lein test "*) printf '%s\t%s\n' "$SECONDS" "${line#lein test }" ;;
          esac
        done > "$timing"
  ) &
  pids+=("$!")
done

for p in "${pids[@]}"; do wait "$p"; done
elapsed=$((SECONDS - t0))

# ---- timings for the next run ----------------------------------------------
# Each `lein test <ns>` line is a start stamp; a namespace's cost is the gap to the
# next one.  The last namespace in a shard has no successor, so it keeps its previous
# figure rather than a guess.
{
  [[ -f "$TIMINGS" ]] && cat "$TIMINGS"
  for ((b = 1; b <= jobs; b++)); do
    [[ -f "$OUT/.timing-$b.tsv" ]] || continue
    awk -F'\t' 'NR>1 { printf "%s\t%d\n", prev_ns, $1 - prev_t } { prev_t=$1; prev_ns=$2 }' "$OUT/.timing-$b.tsv"
  done
} | awk -F'\t' '$1 != "" { secs[$1] = $2 } END { for (k in secs) printf "%s\t%s\n", k, secs[k] }' \
  | sort > "$TIMINGS.new" && mv "$TIMINGS.new" "$TIMINGS"
rm -f "$OUT"/.timing-*.tsv "$assign_out"

# ---- aggregate --------------------------------------------------------------
# Summed, not eyeballed: the whole point of sharding is that no single log carries the
# suite's totals any more, and a missing shard has to read as a failure.
tests=0; assertions=0; failures=0; errors=0; bad=0; missing=()
for log in "${shard_logs[@]}"; do
  if ! grep -q '^SHARD-EXIT:' "$log"; then missing+=("$log"); bad=1; continue; fi
  grep -q '^SHARD-EXIT:0$' "$log" || bad=1
  while IFS= read -r line; do
    t=$(echo "$line" | sed -n 's/^Ran \([0-9]*\) tests containing \([0-9]*\) assertions.*/\1 \2/p')
    [[ -n "$t" ]] && { tests=$((tests + ${t% *})); assertions=$((assertions + ${t#* })); }
  done < <(grep '^Ran .* tests containing' "$log")
  while IFS= read -r line; do
    f=$(echo "$line" | sed -n 's/^\([0-9]*\) failures, \([0-9]*\) errors.*/\1 \2/p')
    [[ -n "$f" ]] && { failures=$((failures + ${f% *})); errors=$((errors + ${f#* })); }
  done < <(grep '^[0-9]* failures, [0-9]* errors' "$log")
done

echo
printf 'Ran %d tests containing %d assertions.\n' "$tests" "$assertions"
printf '%d failures, %d errors.\n' "$failures" "$errors"
printf 'across %d shard(s) in %ds\n' "${#shard_logs[@]}" "$elapsed"

if [[ ${#missing[@]} -gt 0 ]]; then
  printf 'shard(s) produced no exit marker (killed?): %s\n' "${missing[*]}" >&2
fi
if [[ $bad -ne 0 || $failures -ne 0 || $errors -ne 0 ]]; then
  echo
  echo "failing tests:"
  grep -h -A3 '^\(FAIL\|ERROR\) in' "${shard_logs[@]}" 2>/dev/null | head -n 120
  exit 1
fi
exit 0

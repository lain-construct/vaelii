#!/usr/bin/env bash
# scripts/test-matrix.sh — every configuration at once: the eight storage backends and
# the five sweeps, concurrently, with one JVM each.
#
# ~13 minutes where `test-backends.sh` and `test-sweeps.sh` in sequence take ~55.  Same
# thirteen runs, same verdicts; what changes is that the box runs more than one of them
# at a time.  **This is the one to run before landing a change that owes the matrix** —
# a change touching storage, the index, records, recovery or overlay (the backend half),
# or inference, the TMS or context retrieval (the sweep half).  The two single-axis
# scripts remain, and are what to reach for when you want one axis, one config, or a
# readable per-run wall time.
#
# WHY CONCURRENT IS SAFE, given both of those scripts are sequential on purpose:
#
#   - **The in-memory registry is per JVM.**  Two runs over the same space number do not
#     collide, which is the same fact `test-parallel.sh` shards on.
#   - **A durable run's store path is `<vaelii.disk.dir>/space-<n>`**
#     (`impl/disk/backend.clj`), and every config here gets its own `vaelii.disk.dir`
#     under this run's output directory.  Distinct directories, so the single-writer
#     lock is never contended and the six-block `VAELII_TEST_SPACE` limit — which is
#     about sharing one directory — never binds.
#   - **No test asserts an elapsed-time bound.**  Contention costs wall clock and cannot
#     cost a verdict, which is what makes thirteen suites on ten cores a scheduling
#     question rather than a correctness one.
#
# WHAT IT COSTS.  A run's wall time here is a function of what else was running, so it
# is not a measurement — read `lein perf` for those, and never while this is going.  The
# per-namespace progress the single-axis scripts print is dropped too: thirteen
# interleaved streams are not readable.  On a terminal you get instead a LIVE DASHBOARD
# — one row per configuration, each a bar that fills as its suite reaches namespaces,
# repainted in place; the bars are green until something fails and red after.  Off a
# terminal (a pipe, a redirect, CI, `SUITE_PROGRESS=lines`) that would be cursor-motion
# noise in a log, so those get the scrolling form: a line per configuration as it starts
# and finishes, and a heartbeat naming how far each running config has got.
#
# LONGEST FIRST.  Whoever starts last sets the finish, so the last thing to start has to
# be the shortest thing there is: the durable four take ~10-12 minutes under a full box
# against ~4-5 for the rest, and a 4-minute sweep starting at minute nine outlasts a
# 12-minute disk run that started at zero.  Order comes from the previous run's measured
# seconds (`target/test-matrix/config-timings.tsv`, per checkout), and from a
# durable-is-slower prior before anything has been measured.
#
# WHAT FAILED, AND WHETHER IT IS THE SUITE'S ANSWER.  A red run names the failing TESTS
# rather than their namespaces, and the report closes with those tests rolled up across
# configurations: a test that failed under every run is the suite's answer at this
# revision, and one that failed under only some is a difference between configurations —
# which is the finding, and the reason there is more than one run.  Every row is in
# `failures.tsv` whatever the console prints, and the console shrinks its shape as the
# count grows: blocks under nine, a line each under thirty, a count past that.
#
# THE TREE MOVING UNDER IT.  Several agents write this checkout, and thirteen minutes is
# long enough for two commits.  Every config records the revision it compiled, and the
# report at the end says whether they all compiled the same one — and if not, lists the
# commits that landed, marks the ones that touched `src/` or `test/`, and names which
# configs are on which side.  **A red run under a commit you did not write is that
# commit's to answer for.**  Report it, re-run that one config, and carry on; the matrix
# is owed by whoever landed the change, not by whoever happened to be running it.  A
# tree that was already dirty when the matrix started is the worse case and says so:
# uncommitted work compiled into all thirteen runs, and the result answers for no commit
# at all.
#
# **Do not edit the tree while this is running**, and the revision a config compiled is
# not the whole of why.  A namespace is compiled once at boot, so an edit after that
# cannot reach a run already going — but a test that reads a file at RUN time does see
# it: `config_surface_test` slurps `docs/operations.md` while its own roster is already
# compiled, so editing that doc mid-matrix moved one run's failure count and not
# another's.  The failing set stayed identical, which is the property that matters, and
# the count is what somebody reads first.  The dirty-by-the-end line says this happened;
# it cannot say what it cost.
#
# Usage:
#   ./scripts/test-matrix.sh                  # all thirteen, :default
#   ./scripts/test-matrix.sh :all             # ...with the ^:slow half — before a release
#   ./scripts/test-matrix.sh --jobs 4         # fewer at a time, on a box you are using
#   ./scripts/test-matrix.sh memory disk rete # only these
#   ./scripts/test-matrix.sh --keep           # keep each durable run's scratch directory
#   ./scripts/test-matrix.sh --fail-fast      # launch nothing new once one has failed
#
# Env:
#   TEST_MATRIX_OUT   log directory (default target/test-matrix/run-<pid>)
#   MATRIX_JOBS       how many at a time (default: scripts/lib/slots.sh)
#   MATRIX_JVM_OPTS   extra JVM_OPTS for every run.  Empty by default.  On a loaded box
#                     `-XX:ActiveProcessorCount=2` is the one worth trying — each JVM
#                     otherwise sizes its GC and JIT pools from all ten cores while
#                     doing one core of work — but measure it rather than believing it.
#                     It lands in each log's own `# env … lein test …` line either way,
#                     so a run stays reproducible by copying that line.
#   MATRIX_HEARTBEAT  seconds between scrolling progress lines when NOT on a terminal
#                     (default 60; 0 turns them off).  The live dashboard ignores it —
#                     it repaints every second — and `SUITE_PROGRESS=lines` is what
#                     turns the dashboard off in favour of the heartbeat on a terminal.
#
# ^C stops every running suite and then the script.
#
# Exit: 0 when all thirteen passed, 1 when one failed, 130 when interrupted.  A tree
# that moved does not change the exit status — it is a fact about the runs, not a
# verdict on them, and a green matrix across two revisions is still thirteen green runs.

set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

# leiningen's own terminal state, handed down first by the alias: lein-shell pipes
# this script's stdout, so `-t 1` (in suite-marks.sh, sourced below) would say "not a
# terminal" and the live dashboard would fall back to the scrolling heartbeat even
# with someone watching.  Absent when run directly, where `-t 1` stands.
case "${1:-}" in
  --tty)    SUITE_TTY=1; shift ;;
  --no-tty) SUITE_TTY=0; shift ;;
esac

# colours, `hms`, the log readers, and — through it — the revision helpers
# shellcheck source=scripts/lib/suite-marks.sh
. scripts/lib/suite-marks.sh
# shellcheck source=scripts/lib/suite-configs.sh
. scripts/lib/suite-configs.sh
# the default slot count, shared with test-parallel.sh so the rule cannot drift
# shellcheck source=scripts/lib/slots.sh
. scripts/lib/slots.sh

# The live dashboard — one repainted row per configuration, each a bar that fills as
# its suite reaches namespaces — runs on a terminal.  A pipe, a redirect or CI gets
# the scrolling heartbeat lines instead: a log wants those, and cursor motion painted
# into one is noise.  `SUITE_PROGRESS=lines` forces the heartbeat on a terminal too.
if (( IS_TTY )) && [[ "$PROGRESS" == marks ]]; then LIVE=1; else LIVE=0; fi
# the bar's cell count, from the terminal width suite-marks measured (80 when it could
# not), clamped so it neither crowds the counts beside it nor runs off a wide screen
BARW=$(( COLS - 46 )); (( BARW < 12 )) && BARW=12; (( BARW > 32 )) && BARW=32

SELECTOR=":default"
JOBS="${MATRIX_JOBS:-}"
KEEP=0
FAIL_FAST=0
HEARTBEAT="${MATRIX_HEARTBEAT:-60}"
WANTED=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    --jobs) [[ $# -ge 2 ]] || { echo "test-matrix: --jobs needs a value" >&2; exit 2; }
            JOBS="$2"; shift 2 ;;
    --jobs=*) JOBS="${1#*=}"; shift ;;
    --keep) KEEP=1; shift ;;
    --fail-fast) FAIL_FAST=1; shift ;;
    -h|--help) awk 'NR>1 && /^#/ {sub(/^# ?/, ""); print; next} NR>1 {exit}' "$0"; exit 0 ;;
    :all|:slow|:default) SELECTOR="$1"; shift ;;
    :*) echo "unknown selector $1 (:all, :slow, :default)" >&2; exit 2 ;;
    -*) echo "unknown flag $1 (try --help)" >&2; exit 2 ;;
    *) config_kind "$1" >/dev/null \
         || { echo "unknown configuration $1" >&2
              echo "  backends: ${ALL_BACKENDS[*]}" >&2
              echo "  sweeps:   ${ALL_SWEEPS[*]}" >&2; exit 2; }
       WANTED+=("$1"); shift ;;
  esac
done

if [[ ${#WANTED[@]} -gt 0 ]]; then
  CONFIGS=("${WANTED[@]}")
else
  CONFIGS=("${ALL_BACKENDS[@]}" "${ALL_SWEEPS[@]}")
fi

# LONGEST FIRST, which is what decides the finish.  A slot count under the configuration
# count means somebody starts in a second wave, and whoever starts last sets the wall
# clock — so the last thing to start must be the shortest thing there is.  Measured: the
# durable four take ~10-12 minutes under a full box against ~4-5 for the rest, and a
# 4-minute sweep starting at minute nine finishes after the 12-minute disk run that
# started at zero.  That is the whole difference between 13 minutes and 12.
#
# Weights come from the last run in this checkout (`config-timings.tsv`, kept beside the
# run directories and shared by every run, the way `gate.sh` keeps its shard timings) and
# fall back to a prior when there are none: a durable record store writes files and is
# slower, which is a fact about the configuration rather than about the machine, so it is
# safe to assume before anything has been measured.  `test-parallel.sh` bin-packs from
# measurement for the same reason and with the same fallback.
MATRIX_TIMINGS="target/test-matrix/config-timings.tsv"
order_longest_first() {
  local c w
  for c in "${CONFIGS[@]}"; do
    w=""
    [[ -r "$MATRIX_TIMINGS" ]] && w=$(awk -F'\t' -v c="$c" '$1 == c { print $2 }' "$MATRIX_TIMINGS" | tail -1)
    if [[ -z "$w" ]]; then
      if config_wants_disk "$c"; then w=600; else w=300; fi
    fi
    printf '%s\t%s\n' "$w" "$c"
  done | sort -k1,1nr -k2,2 | cut -f2        # ties on the name, so the order is content's
}
ORDERED=()
while IFS= read -r c; do ORDERED+=("$c"); done < <(order_longest_first)
CONFIGS=("${ORDERED[@]}")

# Slots default from `scripts/lib/slots.sh` — the same rule `test-parallel.sh` shards by:
# half the performance cores, less the vaelii JVMs already running on the box.  Each run is
# about one core of test work, so a slot count near the core count keeps every core busy
# while leaving the box usable; more slots than cores does not go faster and costs another
# JVM's memory each.  slots.sh says why it is P/2 (not `cores - 2`) and load-aware.
[[ -z "$JOBS" ]] && JOBS=$(default_slots)
[[ $JOBS -gt ${#CONFIGS[@]} ]] && JOBS=${#CONFIGS[@]}

# A run owns its directory — `gate.sh` and `test-backends.sh`, same reason: two matrices
# in one checkout must not interleave a log or delete each other's live disk scratch.
MATRIX_ROOT="target/test-matrix"
if [[ -n "${TEST_MATRIX_OUT:-}" ]]; then
  OUT_DIR="$TEST_MATRIX_OUT"; mkdir -p "$OUT_DIR"
else
  OUT_DIR="$MATRIX_ROOT/run-$$"; mkdir -p "$OUT_DIR"
  ln -sfn "$(basename "$OUT_DIR")" "$MATRIX_ROOT/latest" 2>/dev/null || true
fi
# absolute, so the reproducer header's `# <dir>` pastes from any directory rather than
# only from the checkout root.  The dir exists by now (mkdir above), so the `cd` holds.
ABS_OUT_DIR=$(cd "$OUT_DIR" 2>/dev/null && pwd) || ABS_OUT_DIR="$OUT_DIR"

RUN_NS_COUNT=$(selected_ns_count "$SELECTOR")

# ^C stops every running suite and then the script.  `set -m` puts each job in its own
# process group so one signal reaches everything a run is — the `lein` wrapper, its JVM
# and the project JVM it forks — rather than killing the wrapper and orphaning the JVM
# that holds the CPU.  `test-backends.sh` carries the long form.
set -m
FAILED=()
n=${#CONFIGS[@]}
state=(); pid=(); pgid=(); rev=(); logf=(); startt=(); secs=(); diskd=(); fin=()
for ((i = 0; i < n; i++)); do state[i]=queued; pid[i]=0; pgid[i]=0; secs[i]=0; diskd[i]=""; fin[i]=""; done

# shellcheck disable=SC2317,SC2329  # invoked from the INT/TERM trap below
stop_all() {
  local i
  for ((i = 0; i < n; i++)); do
    [[ "${state[i]}" == running ]] || continue
    [[ "${pgid[i]}" -gt 0 ]] && kill -TERM -"${pgid[i]}" 2>/dev/null
  done
  for _ in $(seq 1 20); do
    local alive=0
    for ((i = 0; i < n; i++)); do
      [[ "${state[i]}" == running && "${pgid[i]}" -gt 0 ]] || continue
      kill -0 -"${pgid[i]}" 2>/dev/null && alive=1
    done
    [[ $alive -eq 0 ]] && return 0
    sleep 0.25
  done
  for ((i = 0; i < n; i++)); do
    [[ "${state[i]}" == running && "${pgid[i]}" -gt 0 ]] && kill -KILL -"${pgid[i]}" 2>/dev/null
  done
}

# shellcheck disable=SC2317,SC2329  # ditto — `trap on_interrupt INT TERM`
on_interrupt() {
  trap - INT TERM
  echo; echo "  ${RED}^C${OFF} ${DIM}stopping every running suite${OFF}"
  { stop_all; } 2>/dev/null
  echo "  ${DIM}partial logs in $OUT_DIR/${OFF}"
  exit 130
}
trap on_interrupt INT TERM

# The log a config writes.  `<config>.log` belongs to the routine run; any other
# selector says which it was, so a `:slow` pass sits beside a `:default` one.
log_for() {
  if [[ "$SELECTOR" == ":default" ]]; then printf '%s/%s.log' "$OUT_DIR" "$1"
  else printf '%s/%s%s.log' "$OUT_DIR" "$1" "${SELECTOR/:/.}"; fi
}

# How many namespaces a running config has reached — `lein test` prints one header per
# namespace before running it, so counting them is the progress the heartbeat reports.
ns_reached() {
  local c                                          # `grep -c` prints 0 and exits 1, so
  c=$(grep -acE '^lein test [A-Za-z0-9._-]+$' "$1" 2>/dev/null)   # no `|| echo 0` — that
  printf '%s' "${c:-0}"                            # would print the zero twice
}

launch() {                                         # launch <index>
  # two `local`s, not one: a `local a=$1 b=${x[$a]}` expands every word before the
  # builtin runs, so `b` would index with the CALLER's `a`
  local i="$1"
  local cfg="${CONFIGS[$i]}" log envv=() opts
  log=$(log_for "$cfg"); logf[i]="$log"
  # as an `env` argument list rather than an assignment prefix: a prefix is recognized
  # before expansion, so one built from a variable cannot be used.  Word-splitting is
  # what is wanted — the tactician row is two assignments and neither holds a space.
  # shellcheck disable=SC2207
  envv=( $(config_env "$cfg") )
  opts="${MATRIX_JVM_OPTS:-}"
  if config_wants_disk "$cfg"; then
    diskd[i]="$OUT_DIR/$cfg.disk"
    rm -rf "${diskd[i]}"
    opts="$opts -Dvaelii.disk.dir=${diskd[i]}"
  fi
  [[ -n "${opts// /}" ]] && envv+=(JVM_OPTS="${opts# }")
  rev[i]=$(revision_hash)                          # what THIS run is about to compile
  startt[i]=$SECONDS
  # revision, then the command verbatim: two lines at the top of every log, so the one
  # config that went red is reproducible by copying its second line.  The console cannot
  # carry it — thirteen launches with a `-Dvaelii.disk.dir=…` each is not a readable
  # column — and the log is where somebody debugging that config is already looking.
  revision_stamp "$cfg" > "$log"
  printf '# env %s lein test %s\n' "${envv[*]}" "$SELECTOR" >> "$log"
  # `< /dev/null` is what keeps it running: `set -m` puts the job outside the terminal's
  # foreground group and leiningen pumps its own stdin into the project subprocess, so a
  # run that reads the tty takes SIGTTIN and the whole group stops — 0% CPU and an empty
  # log, indistinguishable from a hang.
  #
  # The status comes from the marker the run echoes into its own log, never from a
  # pipeline: `test-parallel.sh`'s rule, and here it is also how completion is noticed
  # without `wait -n`, which is bash 4.3 and this is the 3.2 macOS ships.
  ( env "${envv[@]}" lein test "$SELECTOR" < /dev/null >> "$log" 2>&1
    echo "MATRIX-EXIT:$?" >> "$log" ) &
  pid[i]=$!
  pgid[i]=$(ps -o pgid= -p "${pid[i]}" 2>/dev/null | tr -d ' ')
  pgid[i]="${pgid[i]:-${pid[i]}}"
  state[i]=running
  # the live dashboard carries a launching config as a bar that starts filling; only
  # the scrolling view announces it as a line
  (( LIVE )) || printf '  %s▸%s %-16s %s%s  # %s%s\n' \
    "$DIM" "$OFF" "$cfg" "$DIM" "${rev[i]}" "$log" "$OFF"
}

reap() {                                           # reap <index> -> prints its row
  local i="$1"                                     # separately, per `launch` above
  local cfg="${CONFIGS[$i]}" log="${logf[$i]}" code summary counts mark elapsed
  wait "${pid[i]}" 2>/dev/null
  code=$(grep -a '^MATRIX-EXIT:' "$log" | tail -1 | cut -d: -f2)
  code="${code:-1}"
  elapsed=$((SECONDS - startt[i])); secs[i]=$elapsed
  summary=$(run_summary "$log")
  counts=$(run_counts "$log")
  if [[ "$code" -eq 0 ]]; then mark="$TICK"; state[i]=passed
  else mark="$CROSS"; state[i]=failed; FAILED+=("$cfg"); fi
  fin[i]="${summary:-did not finish}${counts:+, $counts}"
  # On the dashboard the finished row and its ✔/✘ are already in the block, and the
  # failing tests are the end-of-run rollup's to name; only the scrolling view prints
  # the row and its failures inline as they land.
  if (( ! LIVE )); then
    printf '  %s %-16s %-52s %8s  %s\n' \
      "$mark" "$cfg" "${fin[i]}" "$(hms $elapsed)" "${rev[i]}"
    # the failing TESTS, not just their namespaces: "which namespace" cannot tell a
    # broken test from a configuration that disagrees, and the rollup needs the names
    if [[ "$code" -ne 0 ]]; then
      local shown=0 total
      total=$(failing_tests "$log" | wc -l | tr -d ' ')
      while read -r t; do
        [[ -z "$t" ]] && continue
        (( shown >= 8 )) && break
        printf '      %s %s\n' "$CROSS" "$t"
        shown=$((shown + 1))
      done < <(failing_tests "$log")
      (( total > shown )) && printf '      %s… and %d more in %s%s\n' \
        "$DIM" "$((total - shown))" "$log" "$OFF"
    fi
  fi
  [[ $KEEP -eq 1 || -z "${diskd[i]}" ]] || rm -rf "${diskd[i]}"
}

# ---- the live dashboard (a terminal only) -----------------------------------
# `redraw` repaints one row per configuration in place — queued, a filling bar while
# running, ✔/✘ when done — from the same `ns_reached` poll the heartbeat reads.  It is
# gated on `LIVE`, so a pipe or CI never sees a cursor-motion byte; the scrolling
# heartbeat is what those get.

# a proportional bar `━━━╾────────` `w` cells wide: heavy for the reached fraction, a
# half-heavy head at the frontier, light for the rest.  No padding follows it, so its
# multi-byte cells never have to line up with a byte-counted `printf` width — the colour
# escapes it emits are zero-width bytes, so they do not disturb that either.  The reached
# run and its head carry the verdict colour `col`; the unreached remainder is dim grey,
# so the bar reads as a filling gauge rather than a solid green (or red) block.
bar() {                                            # bar <reached> <total> <width> <col>
  local reached="$1" total="$2" w="$3" col="$4" fill i s=""
  (( total < 1 )) && total=1
  fill=$(( reached * w / total )); (( fill > w )) && fill=w
  # `${s}` braced, not `$s`: in a non-UTF-8 locale bash's bare-`$s` name scanner
  # swallows the high bytes of the glyph that follows, and under `set -u` the bogus
  # name reads as unbound and the bar comes back empty.  The braces end the name.
  s="${col}"
  for ((i = 0; i < w; i++)); do
    if   (( i <  fill )); then s="${s}━"
    elif (( i == fill )); then s="${s}╾${DIM}"     # head, then dim for the unreached rest
    else                       s="${s}─"
    fi
  done
  printf '%s%s' "$s" "$OFF"
}

BLOCK=0                                            # rows painted last time; 0 = not yet
redraw() {
  (( LIVE )) || return 0
  # up over the block painted last time, so this paint lands on top of it rather than
  # below it
  (( BLOCK > 0 )) && printf '\033[%dA' "$BLOCK"
  # green until something fails, then red — the bars carry the matrix's verdict-so-far,
  # not just each run's progress
  local barcol="$GREEN"; (( ${#FAILED[@]} > 0 )) && barcol="$RED"
  local i cfg run=0 donec=0 q=0 reached=0
  local -a rv=()
  # One poll per config, read by both the aggregate bar and its own row, so a running
  # config's log is grepped once a paint rather than twice.  A finished config counts as
  # its whole namespace budget reached; a queued one as none.
  for ((i = 0; i < n; i++)); do
    case "${state[i]}" in
      running)       rv[i]=$(ns_reached "${logf[i]}"); run=$((run + 1)) ;;
      passed|failed) rv[i]=$RUN_NS_COUNT;              donec=$((donec + 1)) ;;
      *)             rv[i]=0;                          q=$((q + 1)) ;;
    esac
    reached=$((reached + rv[i]))
  done
  # the whole matrix as one filling bar — the header's `lein test` line, animated: every
  # namespace of every configuration is a cell, so it advances even while a row is mid-run
  printf '\033[K  %s%-19s%s %s  %s# %s%s\n' \
    "$DIM" "lein test $SELECTOR" "$OFF" \
    "$(bar "$reached" "$((n * RUN_NS_COUNT))" "$BARW" "$barcol")" \
    "$DIM" "$ABS_OUT_DIR" "$OFF"
  for ((i = 0; i < n; i++)); do
    cfg="${CONFIGS[i]}"
    printf '\033[K'                                # clear the line's old content first
    case "${state[i]}" in
      running)
        printf '  %s⋯%s %-16s %s %s/%s  %s%s %s%s\n' \
          "$DIM" "$OFF" "$cfg" "$(bar "${rv[i]}" "$RUN_NS_COUNT" "$BARW" "$barcol")" \
          "${rv[i]}" "$RUN_NS_COUNT" "$DIM" "$(hms $((SECONDS - startt[i])))" "${rev[i]}" "$OFF" ;;
      passed)
        printf '  %s %-16s %-44.44s %s%s %s%s\n' \
          "$TICK" "$cfg" "${fin[i]}" "$DIM" "$(hms "${secs[i]}")" "${rev[i]}" "$OFF" ;;
      failed)
        printf '  %s %-16s %-44.44s %s%s %s%s\n' \
          "$CROSS" "$cfg" "${fin[i]}" "$DIM" "$(hms "${secs[i]}")" "${rev[i]}" "$OFF" ;;
      *)
        printf '  %s·%s %-16s %squeued%s\n' "$DIM" "$OFF" "$cfg" "$DIM" "$OFF" ;;
    esac
  done
  printf '\033[K  %s%d running · %d done · %d queued        %s elapsed%s\n' \
    "$DIM" "$run" "$donec" "$q" "$(hms $((SECONDS - T0)))" "$OFF"
  BLOCK=$(( n + 2 ))
}

START_REV=$(revision_hash)
START_DIRTY=$(revision_dirty)
T0=$SECONDS

echo "${BOLD}running ${n} configuration(s), $JOBS at a time${OFF}" \
     "${DIM}$SELECTOR — $RUN_NS_COUNT of $NS_COUNT namespaces${OFF}"
echo "${DIM}at $(revision_line)${OFF}"
# The two commands this stands in for, as pasteable reproducers: the `lint` you still owe
# by hand (the matrix does not run it), and the `test` run itself — its `#` carries the
# run's log directory, absolute so it pastes from anywhere.  Under a live terminal the
# test line is repainted as a filling bar by `redraw`; without one it is this static line.
printf '  %s%-19s # static analysis (run it by hand)%s\n' "$DIM" "lein lint" "$OFF"
(( LIVE )) || printf '  %s%-19s # %s%s\n' "$DIM" "lein test $SELECTOR" "$ABS_OUT_DIR" "$OFF"
if [[ "${START_DIRTY:-0}" -gt 0 ]]; then
  echo "  ${RED}⚠${OFF} ${DIM}src/ or test/ is dirty: every run below compiles that"
  echo "     uncommitted work, so this matrix answers for no commit${OFF}"
fi
# One suite is one core for minutes; thirteen beside somebody else's is a slower
# everything.  A warning and not a refusal — sharing the box is normal here.
if pgrep -f 'lein test|vaelii\.bench' >/dev/null 2>&1; then
  echo "  ${RED}⚠${OFF} ${DIM}a suite or bench JVM is already running in this checkout;" \
       "expect both to be slower${OFF}"
fi
echo

# hide the cursor while the block is being repainted, and put it back however the
# script ends — a clean finish, a failure, or the INT/TERM trap's `exit 130`
if (( LIVE )); then printf '\033[?25l'; trap 'printf "\033[?25h"' EXIT; fi

done_n=0; running=0; next=0; last_beat=$SECONDS
while (( done_n < n )); do
  while (( running < JOBS && next < n )); do
    if (( FAIL_FAST && ${#FAILED[@]} > 0 )); then break; fi
    launch "$next"; next=$((next + 1)); running=$((running + 1))
  done

  # nothing running and nothing launchable: --fail-fast stopped the queue
  if (( running == 0 && next < n )); then
    for ((i = next; i < n; i++)); do state[i]=skipped; done
    break
  fi

  for ((i = 0; i < next; i++)); do
    [[ "${state[i]}" == running ]] || continue
    grep -qa '^MATRIX-EXIT:' "${logf[i]}" 2>/dev/null || continue
    reap "$i"
    running=$((running - 1)); done_n=$((done_n + 1))
    last_beat=$SECONDS                             # a row just landed; no beat is due
  done

  if (( LIVE )); then
    redraw
  elif (( HEARTBEAT > 0 && running > 0 && SECONDS - last_beat >= HEARTBEAT )); then
    line=""; shown=0
    for ((i = 0; i < next; i++)); do
      [[ "${state[i]}" == running ]] || continue
      if (( shown < 5 )); then
        line="$line${line:+ · }${CONFIGS[i]} $(ns_reached "${logf[i]}")/$RUN_NS_COUNT"
        shown=$((shown + 1))
      fi
    done
    (( running > shown )) && line="$line · …"
    printf '  %s⋯ %s  %d done · %d running · %d queued   %s%s\n' \
      "$DIM" "$(hms $((SECONDS - T0)))" "$done_n" "$running" "$((n - next))" "$line" "$OFF"
    last_beat=$SECONDS
  fi

  # The poll delay, but interruptibly.  A bare `sleep 2` is an EXTERNAL foreground
  # command, and `set -m` gives it its own process group and hands it the terminal
  # — so a ^C goes to the sleep's group, not to this shell, and the INT/TERM trap
  # never runs.  Nearly all of this loop's wall time is that sleep, so nearly every
  # ^C lands in it and the whole interrupt is lost: the runs keep going, orphaned.
  # Background the sleep and `wait` on it instead — `wait` is a builtin, so this
  # shell stays in the foreground group and a trapped signal returns from it at
  # once, running `on_interrupt`.  Same reason `test-backends.sh` waits on its
  # backgrounded suite.  `2>/dev/null` swallows the job-done notice `set -m` prints.
  if (( done_n < n )); then
    if (( LIVE )); then sleep 1 & else sleep 2 & fi   # a beat a second under the
    wait "$!" 2>/dev/null                             # dashboard, so the bars visibly move
  fi
done

# the final frame, then the cursor below it and back on, so the failures rollup prints
# under a dashboard that already shows every configuration's verdict
if (( LIVE )); then redraw; printf '\033[?25h'; fi

END_REV=$(revision_hash)
END_DIRTY=$(revision_dirty)
ELAPSED=$((SECONDS - T0))

# ---- the machine-readable half ----------------------------------------------
# One row per configuration, so a later reader — or the agent that ran this — does not
# have to parse the console.  Written whatever the verdict.
{
  printf 'config\tkind\trevision\tstate\tseconds\tsummary\tcounts\n'
  for ((i = 0; i < n; i++)); do
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
      "${CONFIGS[i]}" "$(config_kind "${CONFIGS[i]}")" "${rev[i]:-}" "${state[i]}" \
      "${secs[i]}" \
      "$([[ -n "${logf[i]:-}" ]] && run_summary "${logf[i]}")" \
      "$([[ -n "${logf[i]:-}" ]] && run_counts "${logf[i]}")"
  done
} > "$OUT_DIR/summary.tsv"

# What the NEXT run orders itself by.  Per checkout rather than per run — it is feedback
# for the next matrix, not output of this one, so it sits above the run directories the
# way `gate.sh` keeps its shard timings.  A configuration that did not finish keeps
# whatever it last measured rather than a zero, which would promote it to shortest and
# put it last.
mkdir -p "$(dirname "$MATRIX_TIMINGS")" 2>/dev/null || true
{
  [[ -f "$MATRIX_TIMINGS" ]] && cat "$MATRIX_TIMINGS"
  for ((i = 0; i < n; i++)); do
    [[ "${state[i]}" == passed || "${state[i]}" == failed ]] || continue
    # Only a run that actually ran the suite teaches the next one anything.  A minute is
    # a sanity floor rather than a tuning constant: the shortest configuration measured
    # here is nearly four, and anything under a minute is a boot failure, a stand-in
    # `lein`, or a run killed early — each of which would otherwise be recorded as "the
    # fastest configuration" and launched last forever after.
    [[ -n "$(run_summary "${logf[i]}")" && "${secs[i]}" -ge 60 ]] || continue
    printf '%s\t%s\n' "${CONFIGS[i]}" "${secs[i]}"
  done
} | awk -F'\t' '$1 != "" && $2 != "" { s[$1] = $2 } END { for (k in s) printf "%s\t%s\n", k, s[k] }' \
  | sort > "$MATRIX_TIMINGS.$$.new" && mv "$MATRIX_TIMINGS.$$.new" "$MATRIX_TIMINGS"

echo
# ---- failures by test --------------------------------------------------------
# The question a red matrix asks second, after "whose commit is this": is it the SUITE's
# answer, or a difference between configurations?  Naming the failing namespace per run
# cannot answer it — the same namespace under thirteen runs is thirteen lines that all
# say the same word, and reading thirteen logs by hand is what this script exists to
# replace.  A test that failed under every run that finished is the suite's answer at
# this revision; one that failed under only some is a difference between them, and the
# runs it did NOT fail under are the finding.
if [[ ${#FAILED[@]} -gt 0 ]]; then
  fails_tsv="$OUT_DIR/failures.tsv"
  : > "$fails_tsv"
  ran=0; ran_list=""
  for ((i = 0; i < n; i++)); do
    [[ "${state[i]}" == passed || "${state[i]}" == failed ]] || continue
    ran=$((ran + 1)); ran_list="$ran_list ${CONFIGS[i]}"
    while read -r t; do
      [[ -n "$t" ]] && printf '%s\t%s\n' "$t" "${CONFIGS[i]}" >> "$fails_tsv"
    done < <(failing_tests "${logf[i]}")
  done

  # Three shapes, chosen by how much there is to say, because a report nobody reads to
  # the end reports nothing.  Under nine distinct failures each gets a block; up to
  # thirty, a line each; past that, the count and where the rows are.  The blocks are
  # the useful case and the common one — a matrix goes red on one or two tests far more
  # often than on thirty, and thirty is a signal in itself.
  #
  # Sorted inside awk rather than piped through `sort`, since these are multi-line
  # records and sorting the LINES interleaves them.  Ties break on the test name: the
  # order has to be a function of content, never of which run happened to finish first.
  awk -F'\t' -v ran="$ran" -v all="$ran_list" \
      -v dim="$DIM" -v bold="$BOLD" -v off="$OFF" -v rows="$fails_tsv" '
    { if (!(($1 SUBSEP $2) in pair)) { pair[$1 SUBSEP $2] = 1; cnt[$1]++; }
      seen[$1] = seen[$1] " " $2 " " }
    END {
      m = split(all, cfgs, " ")
      for (a = 2; a <= m; a++) {                     # by name, so "not in:" reads the same
        v = cfgs[a]; b = a - 1                       # however the launch order came out
        while (b > 0 && cfgs[b] > v) { cfgs[b + 1] = cfgs[b]; b-- }
        cfgs[b + 1] = v
      }
      n = 0
      for (t in cnt) { name[++n] = t; if (index(t, "/") > 0) { split(t, p, "/"); ns[p[1]] = 1 } }
      nns = 0; for (x in ns) nns++
      for (i = 1; i <= n; i++)                       # selection sort: count desc, name asc
        for (j = i + 1; j <= n; j++)
          if (cnt[name[j]] > cnt[name[i]] ||
              (cnt[name[j]] == cnt[name[i]] && name[j] < name[i])) {
            tmp = name[i]; name[i] = name[j]; name[j] = tmp
          }

      printf "%sfailures by test%s — %d distinct in %d namespace(s), over %d run(s) that finished\n",
             bold, off, n, nns, ran

      # who failed it, said from whichever end is shorter
      for (i = 1; i <= n; i++) {
        t = name[i]; miss = ""; k = 0; hit = ""
        for (j = 1; j <= m; j++) {
          if (cfgs[j] == "") continue
          if (index(seen[t], " " cfgs[j] " ") == 0) { k++; if (k <= 5) miss = miss " " cfgs[j] }
          else if (cnt[t] <= 5) hit = hit " " cfgs[j]
        }
        if (k > 5) miss = miss " …and " (k - 5) " more"
        which[i] = (k == 0) ? "every configuration" \
                 : (k <= 4) ? "all but" miss \
                 : (cnt[t] <= 5) ? hit : "see " rows
      }

      if (n <= 8) {
        for (i = 1; i <= n; i++) {
          printf "  %s────────────────────────────────────────%s\n", dim, off
          printf "  Failing test: %s\n", name[i]
          printf "  Configs:      %d of %d\n", cnt[name[i]], ran
          printf "  Which:        %s\n", which[i]
        }
      } else if (n <= 30) {
        for (i = 1; i <= n; i++)
          printf "  %2d/%d  %-56s %s%s%s\n", cnt[name[i]], ran, name[i], dim, which[i], off
      } else {
        printf "  %d distinct failures is too many to list — every row is in %s\n", n, rows
        for (i = 1; i <= 5; i++)
          printf "  %2d/%d  %s\n", cnt[name[i]], ran, name[i]
        printf "  %s…and %d more%s\n", dim, n - 5, off
      }

      # what the table means, which is the question somebody opened it with
      partial = 0
      for (i = 1; i <= n; i++) if (cnt[name[i]] < ran) partial = 1
      print ""
      if (partial)
        printf "  %sA test some runs passed is a difference BETWEEN configurations — the ones it\n  did not fail under are named beside it, and that is the finding.%s\n", dim, off
      else
        printf "  %sEvery run that finished failed the same tests, so this is the suite'"'"'s answer at\n  this revision rather than a difference between storage or implementation.%s\n", dim, off
    }
  ' "$fails_tsv"
  echo
fi

# ---- the verdict -------------------------------------------------------------
skipped=0
for ((i = 0; i < n; i++)); do [[ "${state[i]}" == skipped ]] && skipped=$((skipped + 1)); done
if [[ ${#FAILED[@]} -eq 0 && $skipped -eq 0 ]]; then
  echo "${GREEN}${BOLD}all $n configurations green${OFF} ${DIM}in $(hms $ELAPSED) ($OUT_DIR/)${OFF}"
else
  echo "${RED}${BOLD}${#FAILED[@]} of $n failed:${OFF} ${FAILED[*]}" \
       "${DIM}in $(hms $ELAPSED)${OFF}"
  (( skipped > 0 )) && echo "  ${DIM}$skipped never started (--fail-fast)${OFF}"
  # one path each while that is a short list, the directory once when it is not: a
  # thirteen-line column of near-identical paths is the part of a report people skip
  if [[ ${#FAILED[@]} -le 5 ]]; then
    for c in "${FAILED[@]}"; do echo "  ${DIM}$(log_for "$c")${OFF}"; done
  else
    echo "  ${DIM}logs: $OUT_DIR/<config>.log — one per failure, and failures.tsv${OFF}"
  fi
fi

# ---- was the tree holding still? ---------------------------------------------
# The question a red matrix on a shared checkout asks first, and the one nobody can
# answer afterwards from the logs alone.
echo
if [[ "$START_REV" == "$END_REV" && "${START_DIRTY:-0}" -eq 0 && "${END_DIRTY:-0}" -eq 0 ]]; then
  echo "${DIM}tree: stable — every run compiled $START_REV, src/ and test/ clean${OFF}"
else
  echo "${BOLD}tree: not stable across this matrix${OFF}"
  [[ "${START_DIRTY:-0}" -gt 0 ]] && \
    echo "  ${RED}⚠${OFF} dirty at the start: ${START_DIRTY} uncommitted file(s) under src/ or test/" \
         "— every run compiled them, so this answers for no commit"
  [[ "${END_DIRTY:-0}" -gt 0 && "${START_DIRTY:-0}" -eq 0 ]] && \
    echo "  ${RED}⚠${OFF} dirty by the end: ${END_DIRTY} uncommitted file(s) — a run that started" \
         "late compiled work no earlier run saw, and a test that reads a file at run time
     (a doc, a golden, a resource) saw the edit even in a run already going"
  if [[ "$START_REV" != "$END_REV" ]]; then
    echo "  ${RED}⚠${OFF} HEAD moved: $START_REV → $END_REV.  What landed:"
    while read -r sha subject; do
      [[ -z "$sha" ]] && continue
      # a commit that touched neither src/ nor test/ cannot move a count, and saying so
      # is most of the triage
      if [[ -n "$(git show --format= --name-only "$sha" -- src test 2>/dev/null)" ]]; then
        printf '      %s %s[src]%s  %s\n' "$sha" "$BOLD" "$OFF" "$subject"
      else
        printf '      %s %s[docs]%s %s\n' "$sha" "$DIM" "$OFF" "$subject"
      fi
    done < <(git log --reverse --format='%h %s' "$START_REV..$END_REV" 2>/dev/null)
    # which side each config compiled: the revision it read at launch
    older=""; newer=""
    for ((i = 0; i < n; i++)); do
      [[ -z "${rev[i]:-}" ]] && continue
      if [[ "${rev[i]}" == "$START_REV" ]]; then older="$older ${CONFIGS[i]}"
      else newer="$newer ${CONFIGS[i]}(${rev[i]})"; fi
    done
    [[ -n "$older" ]] && echo "      ${DIM}compiled $START_REV:${OFF}$older"
    [[ -n "$newer" ]] && echo "      ${DIM}compiled a later one:${OFF}$newer"
  fi
  echo "  ${DIM}A run that is red under a commit you did not write is that commit's to"
  echo "  answer for: say so, re-run the one config, and let whoever landed it run the"
  echo "  matrix. Your own change is cleared by a green run at a revision that holds it.${OFF}"
fi

[[ ${#FAILED[@]} -eq 0 && $skipped -eq 0 ]] && exit 0
exit 1

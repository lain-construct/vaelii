#!/usr/bin/env bash
# scripts/lib/start.sh — sourced by the three start-vaelii scripts, for the two things
# they share: the KB directory they open and the JVM options they add.
#
# The caller sets ROOT to the checkout before sourcing this file.

# start_kb_dir [DIR] prints the KB directory as a physical path: DIR, else `checkouts/kb`
# beside the checkout, which is gitignored and which you point at a KB yourself. It
# resolves a symlink, so the catalog names the KB after the directory the link points at.
# It prints a message and returns 1 when the path is not a directory, so a caller writes
# `KB="$(start_kb_dir "$arg")" || exit 1`.
start_kb_dir() {
  local dir="${1:-$ROOT/checkouts/kb}"
  if [ ! -d "$dir" ]; then
    echo "no KB directory at $dir — pass one, or point checkouts/kb at one" >&2
    return 1
  fi
  (cd "$dir" && pwd -P)
}

# start_profiles KB prints the Leiningen profiles KB's record store needs, comma-joined,
# or nothing. A KB whose records live on a postgres server holds `index/records.edn`
# naming that server (docs/storage.md), and opening it loads the vaelii-postgres
# adapter, which `+with-postgres` puts on the classpath with its driver. A caller
# writes `lein with-profile "+x,$(start_profiles "$KB")"` or `${p:+with-profile "$p"}`.
start_profiles() {
  if [ -f "$1/index/records.edn" ]; then echo "+with-postgres"; fi
}

# start_physical_mb prints the host's physical memory in MiB, read from /proc/meminfo
# (Linux, Android) or `sysctl hw.memsize` (macOS), or nothing when neither answers.
start_physical_mb() {
  if [ -r /proc/meminfo ]; then
    awk '/^MemTotal:/ { printf "%d\n", $2 / 1024; exit }' /proc/meminfo
  else
    local b
    b="$(sysctl -n hw.memsize 2>/dev/null)" || return 0
    case "$b" in '' | *[!0-9]*) ;; *) echo $((b / 1048576)) ;; esac
  fi
}

# start_heap_mb SIZE prints a JVM heap size (`40g`, `6144m`, `524288k`) in MiB, or
# nothing for a spelling it does not read.
start_heap_mb() {
  case "$1" in
    '' | *[!0-9gGmMkK]* | *[gGmMkK]?*) ;;
    *[gG]) echo $((${1%[gG]} * 1024)) ;;
    *[mM]) echo "${1%[mM]}" ;;
    *[kK]) echo $((${1%[kK]} / 1024)) ;;
    *) echo $(($1 / 1048576)) ;;
  esac
}

# start_jvm_opts prints the JVM options every start script adds to JVM_OPTS: the heap
# ceiling, and an exit on OutOfMemoryError, so a process that ran out of heap stops
# instead of serving a KB it did not finish building. A recover short of heap spends most
# of its time in full collections rather than failing, and the exit turns that into an
# error. The ceiling is VAELII_HEAP, else half the host's physical memory up to 31g, the
# largest heap the JVM addresses with compressed object pointers; with neither, the JVM
# picks its own. It prints a message and returns 1 when VAELII_HEAP exceeds physical
# memory, since the OS kills a JVM it cannot back before the heap mark (docs/caches.md)
# fires, so a caller writes `opts="$(start_jvm_opts)" || exit 1`.
start_jvm_opts() {
  local phys mb heap=""
  phys="$(start_physical_mb)"
  if [ -n "${VAELII_HEAP:-}" ]; then
    mb="$(start_heap_mb "$VAELII_HEAP")"
    if [ -n "$phys" ] && [ -n "$mb" ] && [ "$mb" -gt "$phys" ]; then
      echo "VAELII_HEAP=$VAELII_HEAP exceeds this host's ${phys}m of physical memory" >&2
      return 1
    fi
    heap="-Xmx$VAELII_HEAP "
  elif [ -n "$phys" ]; then
    mb=$((phys / 2))
    if [ "$mb" -gt 31744 ]; then mb=31744; fi
    heap="-Xmx${mb}m "
  fi
  echo "${heap}-XX:+ExitOnOutOfMemoryError"
}

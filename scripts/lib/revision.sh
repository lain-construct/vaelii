#!/usr/bin/env bash
# scripts/lib/revision.sh — what a run was taken against, in the two shapes that
# want it: a `#` line at the top of a log, and a short line beside the output.
#
# A verdict that does not name its revision is half a verdict.  On a shared
# checkout those are two different questions: a matrix takes ~35 minutes and
# another agent landing a test halfway through moves the test and assertion
# counts under it — the artifact then shows counts that differ per run, which
# reads exactly like a run that skipped something.  It cost one investigation to
# establish that it was not.  The same applies to a gate whose log is read an
# hour later, and to a number quoted into a report.
#
# `src/` and `test/` only: a dirty `docs/` or `CHANGELOG.md` cannot move a count,
# and reporting it would say DIRTY on every run of a repo where somebody is
# always writing.
#
# Sourced, never executed:
#   . scripts/lib/revision.sh
#
# The rule for what belongs in here is `suite-marks.sh`'s: it reads only its
# arguments and the repository, so both the suite scripts and `gate.sh` can take
# it without taking anything else.

# The revision, short.  `no-git` rather than empty, so a log line is indistinguishable from a fact
# about a tarball rather than as a field somebody forgot to fill in.
revision_hash() {
  git rev-parse --short HEAD 2>/dev/null || echo "no-git"
}

# How many files under src/ or test/ the run was taken over rather than at.
revision_dirty() {
  git status --porcelain -- src test 2>/dev/null | wc -l | tr -d ' '
}

# `<hash> — <state>`, and nothing else: no colour, no newline, no label.  The
# caller owns all three, which is what lets one line serve a console header, a
# summary row and the log stamp below.
revision_line() {
  local rev dirty
  rev=$(revision_hash)
  dirty=$(revision_dirty)
  if [ "${dirty:-0}" -gt 0 ]; then
    printf '%s — tree DIRTY: %s uncommitted file(s) under src/ or test/' "$rev" "$dirty"
  else
    printf '%s — src/ and test/ clean' "$rev"
  fi
}

# The first line of a log: the same fact, dated, and commented so the greps that
# read these logs back (`^Ran `, `^lein test :only `) cannot match it.  `$1`
# names what was run — every caller passes it (the backend, the sweep, the gate
# stage); the `suite run` default is a fallback for a bare call, not the common case.
revision_stamp() {
  printf '# %s at %s — %s\n' "${1:-suite run}" "$(revision_line)" "$(date '+%Y-%m-%d %H:%M:%S')"
}

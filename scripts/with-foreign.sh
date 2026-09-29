#!/usr/bin/env bash
# scripts/with-foreign.sh — run a lein task with vaelii-foreign's readers on the
# classpath, resolved as an ad-hoc dependency rather than a profile.
#
# This replaces the removed `:with-foreign` profile.  The engine names no plugin
# coordinate anywhere (docs/foreign.md), so nothing couples a plugin release to an
# engine cut; this script supplies the coordinate for the single invocation instead.
# `:exclusions [com.vaelii/vaelii]` drops the plugin's own dependency on a *released*
# vaelii, so that jar does not land beside the `src/` this checkout is editing.
#
# The default task is `browser` (browser + REPL + reload channel).  Pass another to
# run it instead, and `FOREIGN_VERSION` to pin a version — a snapshot you `lein
# install`ed from the plugin, say, rather than Clojars' latest.
#
#   scripts/with-foreign.sh                          # foreign-capable browser
#   scripts/with-foreign.sh repl                     # a foreign dump through import-dump
#   scripts/with-foreign.sh run -m vaelii.web        # the web server
#   FOREIGN_VERSION=0.18.1 scripts/with-foreign.sh   # pin the reader version
#
# For live plugin source instead of a published jar, scripts/link-checkouts.sh puts
# the readers on every command's classpath (docs/foreign.md has the trade in full).
{ # one brace group, read whole before it runs: scripts/lint-shellcheck.sh says why
set -euo pipefail

VERSION="${FOREIGN_VERSION:-RELEASE}"

# No task named means the dev browser, which is what the removed profile was reached
# for most.
if [ $# -eq 0 ]; then
  set -- browser
fi

exec lein update-in :dependencies conj \
  "[com.vaelii/vaelii-foreign \"$VERSION\" :exclusions [com.vaelii/vaelii]]" -- "$@"
exit
}

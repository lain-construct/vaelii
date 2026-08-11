#!/usr/bin/env bash
# scripts/lint-versions.sh — the version strings this tree states more than once
# must agree.
#
# `defproject`'s version is written in four places and lein-cloverage's in two,
# each with a "keep in sync" comment and nothing enforcing it.  A comment is not
# a check: these drift, and each drift reads as something other than what it is.
#
#   1. The sibling pin.  `defproject com.vaelii/vaelii "V"` and the
#      `:with-foreign` profile's `com.vaelii/vaelii-foreign "V"` are cut
#      together — the release carve strips the snapshot suffix tree-wide, so a
#      released tree names a released sibling and a dev tree names the snapshot
#      being cut beside it.  When the pin lags, `lein with-profile +with-foreign`
#      fails to resolve, and the documented recovery (`lein install` in the
#      sibling) installs the sibling's *own* current version — so it does not
#      recover, and the user reads a working install as a broken one.
#
#   2. The README's install coordinate.  It is the same version string a third
#      time, so it is held to the same equality rather than to a weaker rule.
#      It is tempting to treat it as lagging — "it should name the last
#      *release*" — and that is the wrong model: `build-release-tree.sh` strips
#      `-SNAPSHOT` **tree-wide** and guards that none survives, so a dev README
#      saying `0.5.0` carves into a release README saying `0.5.0`,
#      which is exactly right and needs nobody to remember it.  A README pinned
#      to a bare previous release is the one that carves wrong: it survives the
#      strip untouched and ships a 0.5.0 tree advertising 0.4.0, which is the
#      single line a reader copies.  So the dev tree says snapshot everywhere
#      and the cut says the release everywhere.
#
#   3. lein-cloverage.  `scripts/coverage.sh` injects the plugin at the root
#      level because a :dev-profile plugin does not register the `cloverage`
#      task through `with-profile +test`; project.clj declares the same plugin
#      for editor tooling.  Two versions means the report and the declaration
#      describe different runs.
#
#   4. The release badge.  `.github/badges/release.svg` is *generated* from
#      `defproject` by `scripts/update-badges.sh`, and being generated is what
#      makes it drift: bumping the version does not run that script, and the
#      badge is a picture at the top of the README — a reader has no way to
#      tell `v0.5.0` painted there apart from the version the tree
#      actually builds.  Held to `agrees` rather than to equality, for the
#      reason the pin is: on `develop` the badge names the release that
#      shipped, and the drift being looked for leaves a *snapshot* behind.
#
# Exit 0 when every pair agrees; prints each disagreement and the fix, and
# exits 1.
set -euo pipefail
export LC_ALL=C

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

PROJECT=${PROJECT_FILE:-project.clj}
COVERAGE=${COVERAGE_FILE:-scripts/coverage.sh}

FAILS=0

# agrees <own> <other> — is `other` a legal spelling beside this tree's `own`?
#
# Two shapes are legal, because three trees carry this file and they are not the
# same tree.  The dev tree and the cut tree are internally uniform: everything is
# `X.Y.Z-SNAPSHOT`, or the carve has stripped every suffix and everything is
# `X.Y.Z`.  **`develop` is deliberately not uniform.** `bump-develop.sh` rewrites
# line 1 only, leaving each sibling coordinate at the version that shipped, and
# the reason is load-bearing: a contributor cloning develop has to be able to
# build it, and `X.Y.(Z+1)-SNAPSHOT` is on nobody's Clojars.  A check that demanded
# equality there would turn the branch every pull request targets red, which is a
# worse failure than the drift it is looking for.
#
# So: equal, or this tree is a snapshot and the other names a plain release.  That
# second arm is what a released coordinate looks like and nothing else — the drift
# this check exists for left a *snapshot* behind (`0.4.0` beside a pin
# reading `0.3.0`), so it is still caught, and so is a pin left at an
# older snapshot in any tree.
agrees() {
  local own="$1" other="$2"
  [[ "$own" == "$other" ]] && return 0
  [[ "$own" == *-SNAPSHOT && "$other" =~ ^[0-9]+(\.[0-9]+)*$ ]] && return 0
  return 1
}

err() { echo "  FAIL: $*" >&2; FAILS=$((FAILS + 1)); }

# read_version <regex-with-one-capture> <file> — first match, or empty.  An
# unreadable coordinate is reported as such rather than passed over: a check
# that goes quiet when its own parse breaks is one that stops holding.
read_version() {
  sed -n "s/$1/\1/p" "$2" 2>/dev/null | head -1
}

# ---- 1: the sibling pin tracks defproject ----
engine=$(read_version '^(defproject com\.vaelii\/vaelii "\([^"]*\)".*' "$PROJECT")
sibling=$(read_version '.*com\.vaelii\/vaelii-foreign "\([^"]*\)".*' "$PROJECT")

if [[ -z "$engine" ]]; then
  err "cannot read defproject's version from $PROJECT"
elif [[ -z "$sibling" ]]; then
  err "cannot read the :with-foreign vaelii-foreign pin from $PROJECT"
elif ! agrees "$engine" "$sibling"; then
  err "sibling pin drift: defproject is $engine, :with-foreign names vaelii-foreign $sibling"
  echo "        → set the :with-foreign pin to \"$engine\" (they are cut together)," >&2
  echo "          or to the release this snapshot follows (that is develop's shape)" >&2
fi

# ---- 2: every README install coordinate is the same version ----
# Both spellings, not the first: the Leiningen vector and the deps.edn map are two
# lines a reader copies, and fixing one is how the other goes stale.  `mapfile` is
# bash 4; macOS ships 3.2 as /bin/bash, so read the matches in a loop.
README=${README_FILE:-README.md}
found=0
while IFS= read -r r; do
  found=1
  agrees "$engine" "$r" && continue
  err "$README advertises $r, defproject is $engine"
  echo "        → make it \"$engine\"; the carve strips -SNAPSHOT tree-wide" >&2
done < <(sed -n 's/.*com\.vaelii\/vaelii "\([^"]*\)".*/\1/p;
                 s/.*com\.vaelii\/vaelii {:mvn\/version "\([^"]*\)"}.*/\1/p' \
           "$README" 2>/dev/null)

(( found == 1 )) || err "cannot read an install coordinate from $README"

# ---- 3: lein-cloverage agrees between the script and the project ----
declared=$(read_version '.*\[lein-cloverage "\([^"]*\)"\].*' "$PROJECT")
# The `${…}` here is the text being matched, not an expansion to perform: the
# line in coverage.sh literally reads `CLOVERAGE_VERSION="${CLOVERAGE_VERSION:-1.2.4}"`.
# shellcheck disable=SC2016
injected=$(read_version '^CLOVERAGE_VERSION="\${CLOVERAGE_VERSION:-\([^}]*\)}"' "$COVERAGE")

if [[ -z "$declared" ]]; then
  err "cannot read lein-cloverage's version from $PROJECT"
elif [[ -z "$injected" ]]; then
  err "cannot read CLOVERAGE_VERSION's default from $COVERAGE"
elif [[ "$declared" != "$injected" ]]; then
  err "cloverage drift: $PROJECT declares $declared, $COVERAGE injects $injected"
  echo "        → make both $declared, or both whatever the newer one should be" >&2
fi

# ---- 4: the release badge reads defproject's version ----
# Off the `<title>`, which carries the version once; the `<text>` runs beside it
# repeat it for the badge's shadow and blur layers, so the first match there would
# be one of three spellings of the same thing and a partial rewrite would still
# parse.  The badge is generated, so the fix is to re-run the generator: editing
# the SVG by hand leaves the next `update-badges.sh` run to undo it.
BADGE=${BADGE_FILE:-.github/badges/release.svg}

# The existence test is its own arm rather than left to the read: `read_version`
# pipes, `pipefail` is on, and a missing file would abort the whole script from
# inside a command substitution — exiting non-zero with nothing said, which is the
# one way a check can fail and teach nobody anything.
if [[ ! -f "$BADGE" ]]; then
  err "no release badge at $BADGE"
  echo "        → generate it with scripts/update-badges.sh" >&2
else
  badge=$(read_version '.*<title>release: v\([^<]*\)<\/title>.*' "$BADGE")
  if [[ -z "$badge" ]]; then
    err "cannot read the release version from $BADGE"
    echo "        → regenerate it with scripts/update-badges.sh" >&2
  elif ! agrees "$engine" "$badge"; then
    err "badge drift: $BADGE reads v$badge, defproject is $engine"
    echo "        → run scripts/update-badges.sh; the badge is generated from" >&2
    echo "          defproject and is not edited by hand" >&2
  fi
fi

if (( FAILS > 0 )); then
  echo "lint-versions: $FAILS disagreement(s)" >&2
  exit 1
fi
echo "lint-versions: OK (vaelii/vaelii-foreign $engine in project.clj, $README and $BADGE, lein-cloverage $declared)"

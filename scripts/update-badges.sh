#!/usr/bin/env bash
# scripts/update-badges.sh — single source of truth for the README badge row.
#
# Measures real(ish) heuristics, then regenerates the ENTIRE badge block
# between the `<!-- badges:start ... -->` / `<!-- badges:end -->` markers in
# README.md. Each badge SVG is rendered locally (no network) and committed
# under .github/badges/; the README references the local files. Colors are a
# perceptually-even OKLCH rainbow: N hues spaced evenly around the OKLCH circle
# at a fixed, bright lightness, so adjacent badges are equally distinguishable
# and black text reads cleanly on every one.
#
# Badges (left to right, lowercase keys):
#   license | release | tests | coverage | loc | docstrings | deps | sponsors
#   (+ a Stage-2 hosted set behind INCLUDE_HOSTED: ci | stars | last commit | clojars)
#
#   - License / Release: static, read from project.clj (:license name +
#               defproject version).
#   - Dev metrics: tests (deftest count) and loc, measured from the tree.
#   - Hosted (Stage 2): ci / stars / last commit / clojars — live shields
#               badges that need the public repo; off by default.
#   - Docstrings: % of top-level defns carrying a docstring, measured from the
#               tree. The one code-quality figure surfaced as a badge.
#   - Coverage: cloverage line-coverage % from scripts/coverage.sh. That run
#               takes minutes, so it is NOT run by default — the previous
#               value already in coverage.svg is preserved. Pass --coverage to
#               actually re-run coverage.sh and refresh it.
#   - Deps:     count of outdated project.clj dependencies from `lein antq`.
#               Like coverage, the antq run needs network + minutes, so it is
#               NOT run by default. Pass --deps to refresh it; that also
#               (re)writes docs/dependencies.md, the report the deps badge
#               LINKS to, so clicking "N outdated" shows exactly which deps are
#               behind, each with a changelog link.
#
# Coverage and deps read `n/a` until their opt-in flag has been run once.
#
# A full scorecard prints to stderr; the README rewrite is the main act.
#
# The script also owns the docs/glossary.md category badges: six label-only
# SVGs (cat-kb | cat-inference | cat-tms | cat-asp | cat-backend | cat-qr) that
# tag each glossary entry's subsystem. Same OKLCH rainbow, 6 evenly-spaced hues,
# at shields' native ~20px so they sit inline in body text.
#
# Usage:
#   scripts/update-badges.sh            # measure + rewrite badges (coverage + deps preserved)
#   scripts/update-badges.sh --coverage # also re-run coverage.sh and refresh that badge
#   scripts/update-badges.sh --deps     # also re-run lein antq, refresh the deps badge + docs/dependencies.md report
#   scripts/update-badges.sh --dry-run  # measure + print, leave README alone
#   scripts/update-badges.sh --glossary-only # only regenerate the glossary category badges
set -euo pipefail

# One level up: this lives in scripts/, beside every other script here. Moving it
# without changing this is silent — the cd succeeds against the parent directory
# and every measurement then reads an empty tree, so the badges regenerate with
# zeroes rather than failing.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

DRY=0; RUN_COV=0; RUN_DEPS=0; GLOSSARY_ONLY=0
for a in "$@"; do
  case "$a" in
    --dry-run|-n)  DRY=1 ;;
    --coverage|-c) RUN_COV=1 ;;
    --deps|-d)     RUN_DEPS=1 ;;
    --glossary-only|-g) GLOSSARY_ONLY=1 ;;
  esac
done

# ---- CONFIG ----
# The docstrings badge is the raw docstring-coverage % (top-level defns with a
# docstring). The scorecard also prints test:src / doc:src ratios and naming /
# commented-code counts as plain diagnostics — no weighting, no composite.

# Seeds for the two badges whose measurement is opt-in. Precedence is
# --flag live run > the value in the existing SVG > this seed, so a
# non-numeric seed renders literally and keeps the badge honest until the
# expensive run has happened once.
COVERAGE_FALLBACK=n/a
DEPS_FALLBACK=n/a

# Perceptually-even OKLCH rainbow. The N badge colors are N hues spaced
# evenly around the OKLCH hue circle at fixed lightness + chroma. Even hue
# steps make adjacent badges equally distinguishable. Lightness is kept
# high/bright so dark text reads on every badge (>= ~0.78 keeps them all dark).
OKLCH_L=0.82            # lightness 0..1 (higher = brighter; >= 0.78 => dark text)
OKLCH_C=0.12            # chroma (higher = more vivid; auto-clamped to sRGB gamut)

# Print N hexes (no #), evenly spaced around the OKLCH hue circle at OKLCH_L /
# OKLCH_C: OKLCH -> OKLab -> linear sRGB -> gamma sRGB, clamped to gamut.
rainbow_palette() {
  perl -e '
    my ($N,$L,$C)=@ARGV;
    sub g { my $x=shift; $x=$x<=0.0031308?12.92*$x:1.055*($x**(1/2.4))-0.055; $x<0?0:($x>1?1:$x) }
    for my $i (0..$N-1) {
      my $H=6.28318530718*$i/$N; my $a=$C*cos($H); my $b=$C*sin($H);
      my $l=($L+0.3963377774*$a+0.2158037573*$b)**3;
      my $m=($L-0.1055613458*$a-0.0638541728*$b)**3;
      my $s=($L-0.0894841775*$a-1.2914855480*$b)**3;
      my $R= 4.0767416621*$l-3.3077115913*$m+0.2309699292*$s;
      my $G=-1.2684380046*$l+2.6097574011*$m-0.3413193965*$s;
      my $B=-0.0041960863*$l-0.7034186147*$m+1.7076147010*$s;
      printf "%02x%02x%02x ", int(g($R)*255+0.5), int(g($G)*255+0.5), int(g($B)*255+0.5);
    }
  ' "$1" "$OKLCH_L" "$OKLCH_C"
}

# File links are RELATIVE repo paths (org-agnostic; render on GitHub wherever the
# repo lives). GH is only used for the one link that can't be a file: the
# releases page.
GH=vaelii/vaelii
# coverage -> a large, well-covered file (placeholder until coverage.sh can emit
# the actual per-file champion); docstrings -> the docstring-rich public read
# API; deps -> a generated report (docs/dependencies.md) that lists exactly which
# project.clj deps are outdated + changelog links, so clicking the "N outdated"
# badge shows the actionable list instead of the raw project.clj. The report is
# (re)written only on a --deps refresh (write_deps_report); a normal run leaves
# it, matching how the badge value itself is preserved. Plain config; repoint
# freely. (Relative repo paths.)
COVERAGE_FILE="src/vaelii/impl/taxonomy.clj"
DOCSTRINGS_FILE="src/vaelii/core.clj"
DEPS_FILE="docs/dependencies.md"

# Static badge values: license + version, read from project.clj.
VERSION=$(grep -m1 -E '^\(defproject' project.clj | grep -oE '"[^"]+"' | head -1 | tr -d '"' || true)
LICENSE_NAME=$(grep -m1 -A1 -E ':license' project.clj | grep -oE ':name[[:space:]]*"[^"]+"' | grep -oE '"[^"]+"' | tr -d '"' || true)
[[ -z "$VERSION" ]] && VERSION="dev"
[[ -z "$LICENSE_NAME" ]] && LICENSE_NAME="see LICENSE"

# Self-hosted badge SVGs, rendered by make_badge below.
BADGES_DIR=".github/badges"
MSG_TEXT=000            # message text color (true black on the bright OKLCH color)
LABEL_BG=2b2b2b         # darkened key (label) background; white label text on it
                        # lands at a contrast close to black-on-bright (matched)
BADGE_SCALE=1.2         # enlarge factor (1 = the native ~20px tall; 1.2 ~= 24px);
                        # the viewBox stays at the layout size and the root
                        # width/height scale, so the SVG renders bigger

MAIN='src'; TEST='test'; DOCS='docs'
clj=(--include='*.clj')

# count lines matching a pattern, tolerating zero matches (grep exits 1).
count() { local n; n=$("$@" | wc -l | tr -d ' '); echo "${n:-0}"; }
g() { grep "$@" || true; }

# Render a badge SVG to $1. Args: outfile label message color
#
# Layout is the classic two-part badge: a dark key (label) box and a bright
# message box, each sized to its text plus 5px of padding either side. An empty
# label renders the message alone (the glossary category badges). Text advance
# widths come from the baked-in Verdana 11px table, so this needs neither the
# network nor a local copy of the font; every <text> also carries textLength, so
# the glyph run is painted at exactly the width the box was sized from and the
# two can never disagree.
make_badge() {
  perl - "$1" "$2" "$3" "$4" "$BADGE_SCALE" "$MSG_TEXT" "$LABEL_BG" <<'PERL'
use strict; use warnings;
my ($out,$label,$msg,$color,$scale,$msgtext,$labelbg) = @ARGV;

# Verdana 11px advance widths in hundredths of a px, printable ASCII 32..126.
my @W = split ' ', <<'TBL';
387 433 505 900 699 1184 799 295 500 500 699 900 400 500 400 500 699
699 699 699 699 699 699 699 699 699 500 500 900 900 900 600 1100 752
754 768 848 696 632 853 827 463 500 762 612 927 823 866 663 866 765
752 678 805 752 1088 754 677 754 500 500 500 900 699 699 661 685 573
685 655 387 685 696 302 379 651 302 1070 696 668 685 685 469 573 433
696 651 900 651 651 578 698 500 698 900
TBL
sub tw {                        # text width in whole px (0 for empty)
  my $s = shift; return 0 unless length $s;
  my $t = 0;
  for my $c (split //, $s) {
    my $o = ord $c;
    $t += ($o >= 32 && $o <= 126) ? $W[$o - 32] : $W[ord('m') - 32];
  }
  return int($t / 100 + 0.5);
}
sub esc { my $s = shift; $s =~ s/&/&amp;/g; $s =~ s/</&lt;/g; $s =~ s/>/&gt;/g; $s =~ s/"/&quot;/g; $s }

my $PAD = 5;
my $ltw = tw($label);   my $mtw = tw($msg);
my $lw  = $ltw ? $ltw + 2*$PAD : 0;
my $mw  = $mtw + 2*$PAD;
my $w   = $lw + $mw;
# Text centres. A two-part badge nudges the label +1px and the message -1px off
# the geometric centre of its box, which is what keeps the pair optically
# balanced across the divider; a label-less badge takes no nudge.
my $lx  = ($lw/2 + 1) * 10;
my $mx  = ($lw + $mw/2 + ($lw ? -1 : 0)) * 10;
my $aria = $ltw ? esc($label).": ".esc($msg) : esc($msg);
my ($el,$em) = (esc($label), esc($msg));

# One text run: a blurred shadow, a flat shadow, then the glyphs themselves.
sub run {
  my ($x,$tl,$txt,$shadow,$fill) = @_;
  sprintf('<g transform="scale(.1)"><g aria-hidden="true" fill="%s">'
        . '<text x="%d" y="150" fill-opacity=".8" filter="url(#blur)" textLength="%d">%s</text>'
        . '<text x="%d" y="150" fill-opacity=".3" textLength="%d">%s</text></g>'
        . '<text x="%d" y="140" textLength="%d"%s>%s</text></g>',
        $shadow, $x, $tl, $txt, $x, $tl, $txt, $x, $tl, $fill, $txt);
}
my $body = "";
$body .= run($lx, $ltw*10, $el, '#010101', '')                  if $ltw;
$body .= run($mx, $mtw*10, $em, '#ccc',    qq{ fill="#$msgtext"});

my $svg = sprintf(
  '<svg xmlns="http://www.w3.org/2000/svg" width="%.0f" height="%.0f" viewBox="0 0 %d 20" role="img" aria-label="%s">'
. '<title>%s</title><filter id="blur"><feGaussianBlur stdDeviation="16"/></filter>'
. '<linearGradient id="s" x2="0" y2="100%%"><stop offset="0" stop-color="#bbb" stop-opacity=".1"/><stop offset="1" stop-opacity=".1"/></linearGradient>'
. '<clipPath id="r"><rect width="%d" height="20" rx="3"/></clipPath>'
. '<g clip-path="url(#r)"><rect width="%d" height="20" fill="#%s"/><rect x="%d" width="%d" height="20" fill="#%s"/>'
. '<rect width="%d" height="20" fill="url(#s)"/></g>'
. '<g fill="#fff" text-anchor="middle" font-family="Verdana,Geneva,DejaVu Sans,sans-serif" text-rendering="geometricPrecision" font-size="110">%s</g></svg>',
  $w*$scale, 20*$scale, $w, $aria, $aria, $w,
  $lw, ($ltw ? $labelbg : $color), $lw, $mw, $color, $w, $body);

open my $fh, '>', $out or die "$out: $!"; print $fh $svg; close $fh;
PERL
}

# Write the deps report the deps badge links to (DEPS_FILE). Turns antq's edn
# output into a markdown table of outdated project.clj deps (name / current /
# latest / changelog), or an "up to date" note when the count is 0. Only called
# on a --deps refresh, so the file stays in sync with the badge value. Each antq
# map carries :name/:version(current)/:latest-version/:changes-url; :changes-url
# may be `nil` (no link). Args: antq-edn count.
write_deps_report() {
  local edn="$1" n="$2" today rows
  today=$(date +%Y-%m-%d)
  rows=$(printf '%s' "$edn" | perl -0777 -ne '
    # Split the flat edn vector into one record per dependency at each :name
    # key, then pull fields by name. Do NOT brace-scan: antq maps carry a
    # nested `:repositories {}` pair, so a `\{[^{}]*\}` scan matches that empty
    # inner map first and drops every real record (silent header-only table).
    my %seen;
    for my $r (split /(?=:name ")/) {
      my ($name) = $r =~ /:name "([^"]+)"/ or next;
      # One row per dependency. antq emits a record per place a dep is declared,
      # so anything named in both the root :dependencies and a profile (the
      # :bench RoaringBitmap / fastutil pair) arrives twice. The badge counts
      # distinct names, so leaving the repeats in makes the table contradict the
      # "N outdated" heading directly above it.
      next if $seen{$name}++;
      my ($cur)  = $r =~ /:version "([^"]+)"/;
      my ($lat)  = $r =~ /:latest-version "([^"]+)"/;
      my ($url)  = $r =~ /:changes-url "([^"]+)"/;
      my $chg = $url ? "[changelog]($url)" : "—";
      print "| `$name` | ", ($cur//"?"), " | ", ($lat//"?"), " | $chg |\n";
    }')
  {
    echo "<!-- generated by scripts/update-badges.sh --deps (do not hand-edit) -->"
    echo "# Dependency status"
    echo
    echo "Outdated \`project.clj\` dependencies as reported by \`lein antq\`. Last"
    echo "checked **${today}**; regenerate with \`scripts/update-badges.sh --deps\`."
    echo
    if [[ "${n:-0}" -eq 0 ]]; then
      echo "All dependencies are up to date. ✅"
    else
      echo "**${n} outdated:**"
      echo
      echo "| dependency | current | latest | changelog |"
      echo "|---|---|---|---|"
      printf '%s\n' "$rows"
    fi
  } > "$DEPS_FILE"
  echo "  deps report written: $DEPS_FILE (${n} outdated)" >&2
}

# ---- glossary category badges (docs/glossary.md) ----
# Five label-only badges tagging each glossary entry's subsystem. Same OKLCH
# method, 5 evenly-spaced hues, but at the native ~20px (scale 1.0) so they
# render inline in glossary body text. The glossary references them as
# ../.github/badges/cat-<name>.svg; the entries themselves are hand-tagged —
# only these SVGs are script-owned. Regenerated on every non-dry run;
# --glossary-only regenerates just these and exits.
# Must match CATS in scripts/lint-glossary.sh, which fails the build on a category
# whose SVG is missing: `qr` was in that list and not in this one, so cat-qr.svg was
# committed once and could never be regenerated — its hue belongs to no palette this
# script produces.
GLOSSARY_CATS=(kb inference tms asp backend qr)
glossary_badges() {
  local cat_colors i saved_scale
  read -r -a cat_colors <<< "$(rainbow_palette "${#GLOSSARY_CATS[@]}")"
  saved_scale=$BADGE_SCALE; BADGE_SCALE=1.0
  mkdir -p "$BADGES_DIR"
  for i in "${!GLOSSARY_CATS[@]}"; do
    make_badge "$BADGES_DIR/cat-${GLOSSARY_CATS[$i]}.svg" "" "${GLOSSARY_CATS[$i]}" "${cat_colors[$i]}"
  done
  BADGE_SCALE=$saved_scale
  echo "  glossary category badges: ${GLOSSARY_CATS[*]} -> $BADGES_DIR/cat-*.svg" >&2
}
if [[ "$GLOSSARY_ONLY" == 1 ]]; then glossary_badges; exit 0; fi
[[ "$DRY" == 0 ]] && glossary_badges

# ---- gather raw counts ----
loc_src=$(find "$MAIN" -name '*.clj' -exec cat {} + | wc -l | tr -d ' ')
loc_test=$(find "$TEST" -name '*.clj' -exec cat {} + | wc -l | tr -d ' ')
loc_doc=$(find "$DOCS" -name '*.md' -exec cat {} + | wc -l | tr -d ' ')

defns=$(count g -rhE '^\(defn ' "$MAIN" "${clj[@]}")
docd=$(grep -rhEA1 '^\(defn ' "$MAIN" "${clj[@]}" | { grep -cE '^\s+"' || true; } | tr -d ' ')
snake=$(count g -rhE '^\(defn?-? [a-z]*_' "$MAIN" "${clj[@]}")

commented=$(count g -rhE '^\s*;;+\s*\(' "$MAIN" "${clj[@]}")

# dev-metric badge values (measured from the tree each run)
# `(tu/deftest-kb` as well as `(deftest`: the KB-fixture macro defines the majority of
# the suite, and counting only the bare form reported 868 of 2464 tests — undercounting
# our own coverage by two thirds, on the badge that advertises it.
tests=$(count g -rhoE '\((tu/)?deftest(-kb)?[[:space:]]' "$TEST" "${clj[@]}")
loc_fmt=$(awk "BEGIN{ printf \"%.0fk\", $loc_src/1000 }")

# ---- docstring coverage + scorecard (one awk pass); stdout = docstring % ----
docstrings=$(awk -v loc_src="$loc_src" -v loc_test="$loc_test" -v loc_doc="$loc_doc" \
  -v defns="$defns" -v docd="$docd" -v snake="$snake" -v commented="$commented" '
  BEGIN{
    doc_cov    = defns>0    ? 100.0*docd/defns        : 0
    test_ratio = loc_src>0  ? loc_test/loc_src         : 0
    doc_ratio  = loc_src>0  ? loc_doc/loc_src          : 0
    cm_per1k   = loc_src>0  ? 1000.0*commented/loc_src : 0

    bar="------------------------------------------------------------"
    printf "\n  VAELII BADGE SCORECARD\n  %s\n", bar > "/dev/stderr"
    printf "  source %d loc | tests %d loc | docs %d loc\n\n", loc_src, loc_test, loc_doc > "/dev/stderr"

    printf "  CODE QUALITY  (docstring coverage is the badge; rest are diagnostics)\n" > "/dev/stderr"
    printf "    docstring coverage          %7.1f%%   (badge)\n", doc_cov > "/dev/stderr"
    printf "    test:source ratio           %7.2fx\n", test_ratio > "/dev/stderr"
    printf "    doc:source ratio            %7.2fx\n", doc_ratio > "/dev/stderr"
    printf "    naming               %5d snake_case defns\n", snake > "/dev/stderr"
    printf "    commented-out code          %5.2f/1k src lines\n", cm_per1k > "/dev/stderr"
    printf "  %s\n\n", bar > "/dev/stderr"

    printf "%.0f\n", doc_cov   # stdout: docstring coverage %
  }')

# ---- coverage: NOT run by default (it takes minutes). Precedence:
#      --coverage live run  >  value in the existing coverage.svg  >  COVERAGE_FALLBACK.
cov=""
if [[ "$RUN_COV" == 1 ]]; then
  echo "  running scripts/coverage.sh (instruments core + runs the suite; minutes)..." >&2
  covlog=$(mktemp)
  { ./scripts/coverage.sh 2>&1 || true; } | tee "$covlog" >&2
  cov=$({ grep -aE '^[[:space:]]*lines:' "$covlog" | grep -oE '[0-9]+(\.[0-9]+)?' | head -1; } || true)
  rm -f "$covlog"
  [[ -z "$cov" ]] && echo "  WARN: could not parse coverage output; falling back to the existing/seed value" >&2
fi
[[ -z "$cov" ]] && cov=$({ grep -oE 'coverage: [0-9.]+' "$BADGES_DIR/coverage.svg" | grep -oE '[0-9.]+' | head -1; } 2>/dev/null || true)
[[ -z "$cov" ]] && cov="$COVERAGE_FALLBACK"
# Coverage message: percent suffix when numeric (a sentinel like "n/a" stays clean).
if [[ "$cov" =~ ^[0-9.]+$ ]]; then cov_msg="${cov}%"; else cov_msg="$cov"; fi

# ---- deps: NOT run by default (antq needs network + minutes). Precedence:
#      --deps live run  >  count in the existing deps.svg  >  DEPS_FALLBACK.
# The edn reporter emits one map per outdated dep; distinct :name = the count.
deps=""
if [[ "$RUN_DEPS" == 1 ]]; then
  echo "  running lein antq (outdated project deps; network, ~minutes)..." >&2
  antqout=$(lein antq --skip=github-action --reporter=edn 2>/dev/null || true)
  # antq's edn reporter emits `(...maps...)` when deps are outdated and `()`
  # when everything is current; anything without a paren is an error/no-run.
  if [[ "$antqout" == *"("* ]]; then
    # grep exits 1 on zero matches (the all-up-to-date `()` case); guard it so
    # pipefail + set -e don't abort the whole run before the README rewrite.
    deps=$(printf '%s' "$antqout" | { grep -oE ':name "[^"]+"' || true; } | sort -u | wc -l | tr -d ' ')
    # Refresh the report the deps badge links to (skipped on a dry run).
    [[ "$DRY" == 0 ]] && write_deps_report "$antqout" "$deps"
  else
    echo "  WARN: antq produced no parseable output; preserving the existing deps value" >&2
  fi
fi
if [[ -z "$deps" && -f "$BADGES_DIR/deps.svg" ]]; then
  if grep -q 'up to date' "$BADGES_DIR/deps.svg" 2>/dev/null; then deps=0
  else deps=$({ grep -oE 'deps: [0-9]+' "$BADGES_DIR/deps.svg" | grep -oE '[0-9]+' | head -1; } 2>/dev/null || true); fi
fi
[[ -z "$deps" ]] && deps="$DEPS_FALLBACK"
# Deps message: "up to date" at zero, "<n> outdated" otherwise (sentinel stays clean).
if [[ "$deps" =~ ^[0-9]+$ ]]; then
  if [[ "$deps" -eq 0 ]]; then deps_msg="up to date"; else deps_msg="${deps} outdated"; fi
else
  deps_msg="$deps"
fi

# ---- the badge row (script is source of truth) ----
# `sponsors` reads **welcome**, not a count, and that is the whole difference between
# this badge and the one that was removed. A hardcoded `0` was a number nobody
# measured, went stale the moment anyone sponsored, and advertised an absence; an
# invitation is true on both sides of the org's Sponsors application and needs no
# maintenance when it lands.
#
# The link is the canonical page (`github.com/sponsors/<org>`), which 404s until that
# application is approved. Deliberate: it is the URL `FUNDING.yml` in the org's
# `.github` repo already names (`github: vaelii`), so the badge and the repo Sponsor
# button point at one place and both start working together, with nothing to edit here.
SPONSORS_MSG=welcome
SPON="https://github.com/sponsors/vaelii"
keys=(license release tests coverage loc docstrings deps sponsors)
msgs=("$LICENSE_NAME" "v$VERSION" "$tests" "$cov_msg" "$loc_fmt" "${docstrings}%" "$deps_msg" "$SPONSORS_MSG")
links=(
  "LICENSE"                           # license    -> the license file
  "https://github.com/${GH}/releases" # release    -> releases page (only absolute repo link)
  "test"                              # tests      -> the test tree
  "$COVERAGE_FILE"                    # coverage   -> large well-covered file
  "src"                               # loc        -> the source tree
  "$DOCSTRINGS_FILE"                  # docstrings -> docstring-rich public API
  "$DEPS_FILE"                        # deps       -> the generated report
  "$SPON"                             # sponsors   -> the org patron page
)

# Sized from `keys` rather than a constant beside it, which is what the glossary
# palette below already does. A hand-maintained count is a second place to edit when a
# badge is added or dropped, and the failure is not a wrong colour: the palette comes
# up short and `set -u` aborts mid-run, after some SVGs are rewritten and before the
# README block is. One array decides both how many badges there are and how many hues
# to space around the circle.
read -r -a RAINBOW <<< "$(rainbow_palette "${#keys[@]}")"

# ---- Stage-2 hosted badges (live; defer until the repo is PUBLIC) ----
# Live shields/GitHub badges (not self-hosted SVGs): they update on their own but
# render in shields' default style (white text, ~20px), which is why the README
# uses the self-hosted set instead. Off by design, not pending — the repo is
# public now and these would resolve; `hosted_md` below is kept as the recipe for
# anyone who prefers live badges. Note the workflow filenames are lint/test/deep.
INCLUDE_HOSTED=0
PUB="$GH"
hosted_md=(
  "[![ci](https://img.shields.io/github/actions/workflow/status/${PUB}/test.yml?label=ci)](https://github.com/${PUB}/actions)"
  "[![stars](https://img.shields.io/github/stars/${PUB})](https://github.com/${PUB}/stargazers)"
  "[![last commit](https://img.shields.io/github/last-commit/${PUB})](https://github.com/${PUB}/commits/main)"
  "[![clojars](https://img.shields.io/clojars/v/vaelii)](https://clojars.org/vaelii)"
)

[[ "$DRY" == 0 ]] && mkdir -p "$BADGES_DIR"
BLOCK=""
for i in "${!keys[@]}"; do
  slug=${keys[$i]// /-}
  file="$BADGES_DIR/$slug.svg"
  [[ "$DRY" == 0 ]] && make_badge "$file" "${keys[$i]}" "${msgs[$i]}" "${RAINBOW[$i]}"
  BLOCK+="[![${keys[$i]}](${file})](${links[$i]})"$'\n'
done
if [[ "$INCLUDE_HOSTED" == 1 ]]; then
  for line in "${hosted_md[@]}"; do BLOCK+="$line"$'\n'; done
fi

cov_src="preserved from coverage.svg/seed; pass --coverage to refresh"
[[ "$RUN_COV" == 1 && "$cov" =~ ^[0-9.]+$ ]] && cov_src="fresh from coverage.sh"
echo "  coverage: ${cov_msg} (${cov_src})" >&2
deps_src="preserved from deps.svg/seed; pass --deps to refresh"
[[ "$RUN_DEPS" == 1 && -n "${antqout:-}" && "$antqout" == *"("* ]] && deps_src="fresh from lein antq"
echo "  deps: ${deps_msg} (${deps_src})" >&2
{ echo "  link targets:"
  echo "    coverage   -> $COVERAGE_FILE"
  echo "    docstrings -> $DOCSTRINGS_FILE"
  echo "    deps       -> $DEPS_FILE"; } >&2

if [[ "$DRY" == 1 ]]; then
  printf '%s' "$BLOCK" >&2
  echo "  (dry run: README not modified)" >&2
else
  BLOCK="$BLOCK" perl -i -0pe '
    my $b = $ENV{BLOCK};
    s/(<!-- badges:start.*?-->\n).*?(<!-- badges:end -->)/$1$b$2/s
      or die "badge markers not found in README.md (expected <!-- badges:start --> ... <!-- badges:end -->)\n";
  ' README.md
  echo "  README badges regenerated: coverage ${cov_msg} | docstrings ${docstrings}% | deps ${deps_msg}" >&2
fi

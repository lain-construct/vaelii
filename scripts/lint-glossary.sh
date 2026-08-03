#!/usr/bin/env bash
# scripts/lint-glossary.sh — structural lint for docs/glossary.md.
#
# Checks:
#   1. Every entry line (starts with `**`) carries exactly ONE category badge
#      `![<cat>](../.github/badges/cat-<cat>.svg)` on the term line, alt text
#      matching the SVG slug, <cat> one of: kb inference tms asp backend.
#   2. Entries are strictly alphabetical within each `## <letter>` section
#      (case-insensitive, backticks stripped, byte order), and the section
#      letters ascend.
#   3. Every relative link target exists (anchors stripped; http/anchor-only
#      links skipped). Paths resolve relative to docs/.
#   4. The legend (everything before the first section) references every badge
#      in CATS.
#   5. Each of those cat-*.svg files exists.
#
# Exit 0 when clean; prints each violation and exits 1 otherwise.
set -euo pipefail
export LC_ALL=C

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
# Overridable for self-testing (link targets still resolve against docs/).
GLOSS=${GLOSSARY_FILE:-docs/glossary.md}
CATS=(kb inference tms asp backend qr)

FAILS=0
err() { echo "  FAIL: $*" >&2; FAILS=$((FAILS + 1)); }

# ---- 1 + 2: per-entry badge shape and alphabetical order (one awk pass) ----
while IFS= read -r msg; do
  err "$msg"
done < <(awk -v catlist="${CATS[*]}" '
  BEGIN { split(catlist, arr, " ")
          for (i in arr) cats[arr[i]] = 1 }
  /^## / { section = substr($0, 4); prev = ""
           if (lastsec != "" && !(section > lastsec))
             print "section " section " out of order (after " lastsec ")"
           lastsec = section; next }
  /^\*\*/ {
    line = $0
    term = line; sub(/^\*\*/, "", term)
    idx = index(term, "**"); term = substr(term, 1, idx - 1)
    n = 0; rest = line
    while (match(rest, /!\[[a-z]+\]\(\.\.\/\.github\/badges\/cat-[a-z]+\.svg\)/)) {
      m = substr(rest, RSTART, RLENGTH); n++
      alt = m;  sub(/^!\[/, "", alt);       sub(/\].*$/, "", alt)
      slug = m; sub(/^.*cat-/, "", slug);   sub(/\.svg.*$/, "", slug)
      if (!(alt in cats))
        print "unknown category \"" alt "\" on entry \"" term "\""
      if (alt != slug)
        print "alt/slug mismatch on entry \"" term "\" (" alt " vs " slug ")"
      rest = substr(rest, RSTART + RLENGTH)
    }
    if (n != 1)
      print "entry \"" term "\" has " n " category badges on its term line (want exactly 1)"
    key = tolower(term); gsub(/`/, "", key)
    if (prev != "" && !(key > prev))
      print "entry \"" term "\" out of alphabetical order in section " section
    prev = key
  }
' "$GLOSS")

# ---- 3: relative link targets exist (resolved from docs/) ----
while IFS= read -r target; do
  [[ -e "docs/$target" ]] || err "broken relative link: $target"
done < <(grep -oE '\]\([^)]*\)' "$GLOSS" \
           | sed -E 's/^\]\(//; s/\)$//' \
           | grep -vE '^(https?:|#)' \
           | sed 's/#.*//' | grep -v '^$' | sort -u)

# ---- 4: legend references every badge in CATS ----
legend=$(awk '/^## /{exit} {print}' "$GLOSS")
for c in "${CATS[@]}"; do
  grep -q "cat-$c\.svg" <<<"$legend" || err "legend missing cat-$c badge"
done

# ---- 5: badge SVGs exist ----
for c in "${CATS[@]}"; do
  [[ -f ".github/badges/cat-$c.svg" ]] \
    || err "missing .github/badges/cat-$c.svg"
done

if (( FAILS > 0 )); then
  echo "lint-glossary: $FAILS violation(s)" >&2
  exit 1
fi
entries=$(grep -c '^\*\*' "$GLOSS")
echo "lint-glossary: OK ($entries entries)"

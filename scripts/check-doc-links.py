#!/usr/bin/env python3
"""Check relative markdown links across the repo's docs resolve to real files.

Scans docs/**.md plus the contributor scaffolding (README, CONTRIBUTING, CONTRIBUTORS,
the CLAs, SECURITY, the PR template). Reports any [text](path) link whose target
(relative to the linking file) is missing. Skips http(s)/mailto links. Drops ?query
before resolving. Code-fence contents are skipped so example links don't count.

The **#fragment is checked too**, against the headings the target file actually
offers (`anchors_of`), and a bare `#anchor` against the linking file's own. A renamed
heading is the one link failure that leaves no trace: the file still resolves, so the
reader lands at the top of a long page and concludes they misread the pointer. Cheap
to check and invisible otherwise, which is the combination worth a ratchet.

Also scans source files (src/**/*.clj{,c,s}) for the `See docs/foo.md`
docstring idiom and `[..](docs/..)` links: a ROOT-relative `docs/<path>.md`
reference written inside a docstring or comment is neither a markdown link nor
in a markdown file, so the markdown scan above never sees it — yet these rot the
same way a markdown link does (a doc is renamed/removed and the pointer
dangles). Test sources (test/**) are skipped: they may carry deliberate
dead-link fixtures.

vaelii is a self-contained repo, so every relative link must resolve inside
it. --public-view is a release gate: it additionally flags any link whose target
escapes the repo root — a leak out of the standalone release into a sibling
checkout that a public reader would not have.
"""
import os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def is_public_doc(path):
    """User-facing doc set the --public-view gate applies to."""
    rel = os.path.relpath(path, ROOT)
    return rel in SCAFFOLDING or rel.startswith("docs" + os.sep)


LINK = re.compile(r'\[[^\]]*\]\(([^)]+)\)')
FENCE = re.compile(r'^\s*(```|~~~)')
# A ROOT-relative `docs/<path>.md` reference in a source docstring/comment. The
# lookbehind keeps it from matching the tail of a longer path.
SRC_DOC_REF = re.compile(r'(?<![\w/])docs/[\w./-]+\.md')

HEADING = re.compile(r'^(#{1,6})\s+(.*?)\s*$')
# An explicit anchor somebody wrote by hand, which GitHub honours alongside the
# slugs it derives.
EXPLICIT_ANCHOR = re.compile(r'<a\s+(?:id|name)="([^"]+)"')


def slugify(heading):
    """GitHub's heading -> fragment rule.

    Lowercase, drop everything that is not a word character, a space or a hyphen,
    then replace EACH space with a hyphen. That last word is required: a run of
    spaces becomes a run of hyphens, so `## Phase 3 — the dense TMS` (whose em-dash
    is dropped between two spaces) is `phase-3--the-dense-tms` with a DOUBLE hyphen.
    Collapsing runs instead reports every such heading as a dead anchor, which is
    the whole population of headings this repo punctuates with em-dashes.
    """
    return re.sub(r'[^\w\s-]', '', heading.strip()).lower().replace(' ', '-')


_anchor_cache = {}


def anchors_of(path):
    """Every fragment `path` offers: one slug per heading, plus explicit <a id>.

    A repeated heading gets GitHub's `-1`, `-2` … suffixes, since that is what a
    link to the second one has to say. Headings inside a code fence are text, not
    headings, and are skipped — the same fence rule the link scan uses.
    """
    if path in _anchor_cache:
        return _anchor_cache[path]
    found, seen, in_fence = set(), {}, False
    try:
        with open(path) as fh:
            for line in fh:
                if FENCE.match(line):
                    in_fence = not in_fence
                    continue
                if in_fence:
                    continue
                found.update(EXPLICIT_ANCHOR.findall(line))
                m = HEADING.match(line)
                if not m:
                    continue
                slug = slugify(m.group(2))
                n = seen.get(slug, 0)
                seen[slug] = n + 1
                found.add(slug if n == 0 else f"{slug}-{n}")
    except (OSError, UnicodeDecodeError):
        return frozenset()
    _anchor_cache[path] = frozenset(found)
    return _anchor_cache[path]


# The contributor scaffolding: markdown that ships and links inward, but lives
# outside docs/. A dangling link here is read by someone deciding whether to send a
# patch, or by someone about to sign an agreement, so it is checked like the rest.
SCAFFOLDING = ("README.md", "CONTRIBUTING.md", "CONTRIBUTORS.md",
               os.path.join("legal", "ICLA.md"), os.path.join("legal", "CCLA.md"),
               os.path.join("licenses", "THIRD-PARTY.md"),
               os.path.join("licenses", "DEPENDENCIES.md"),
               os.path.join(".github", "SECURITY.md"),
               os.path.join(".github", "pull_request_template.md"))


def md_files():
    for rel in SCAFFOLDING:
        p = os.path.join(ROOT, rel)
        if os.path.exists(p):
            yield p
    for dirpath, _, names in os.walk(os.path.join(ROOT, "docs")):
        for n in names:
            if n.endswith(".md"):
                yield os.path.join(dirpath, n)


def source_files():
    """Clojure sources under src (doc-bearing). test/ is skipped."""
    for dirpath, _, names in os.walk(os.path.join(ROOT, "src")):
        for n in names:
            if n.endswith((".clj", ".cljc", ".cljs")):
                yield os.path.join(dirpath, n)


public_view = "--public-view" in sys.argv[1:]

missing, escaping, dead_anchors = [], [], []
for path in md_files():
    with open(path) as fh:
        lines = fh.readlines()
    rel = os.path.relpath(path, ROOT)
    public = public_view and is_public_doc(path)
    in_fence = False
    for i, line in enumerate(lines, 1):
        if FENCE.match(line):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        for m in LINK.finditer(line):
            target = m.group(1).strip()
            if target.startswith(("http://", "https://", "mailto:")):
                continue
            # The fragment is CHECKED, not dropped. A heading rename leaves the file
            # resolving and the link landing at the top of it — a link that half
            # works, which is the kind a reader blames themselves for.
            frag = target.split('#', 1)[1] if '#' in target else ""
            target = target.split('#', 1)[0].split('?', 1)[0].strip()
            if not target:
                # `#anchor` alone — a link into the linking file's own headings.
                if frag and frag not in anchors_of(path):
                    dead_anchors.append(f"{rel}:{i} -> #{frag}  (in this file)")
                continue
            resolved = os.path.normpath(os.path.join(os.path.dirname(path), target))
            escapes = not (resolved == ROOT or resolved.startswith(ROOT + os.sep))
            if public and escapes:
                escaping.append(f"{rel}:{i} -> {target}  (link escapes the repo)")
                continue
            if not os.path.exists(resolved):
                missing.append(f"{rel}:{i} -> {target}")
            elif frag and resolved.endswith(".md") and frag not in anchors_of(resolved):
                dead_anchors.append(
                    f"{rel}:{i} -> {target}#{frag}  (no such heading in {target})")

# Source-file docstring/comment references to docs — ROOT-relative, must exist.
src_missing = []
for path in source_files():
    rel = os.path.relpath(path, ROOT)
    with open(path) as fh:
        for i, line in enumerate(fh, 1):
            for m in SRC_DOC_REF.finditer(line):
                ref = m.group(0)
                if not os.path.exists(os.path.join(ROOT, ref)):
                    src_missing.append(f"{rel}:{i} -> {ref}")

fail = False
if missing:
    print(f"BROKEN LOCAL MARKDOWN LINKS ({len(missing)}):")
    for x in missing:
        print("  " + x)
    fail = True

if dead_anchors:
    print(f"DEAD ANCHORS ({len(dead_anchors)}):")
    for x in dead_anchors:
        print("  " + x)
    fail = True

if src_missing:
    print(f"BROKEN DOC REFERENCES IN SOURCE ({len(src_missing)}):")
    for x in src_missing:
        print("  " + x)
    fail = True

if public_view:
    if escaping:
        print(f"PUBLIC-VIEW VIOLATIONS ({len(escaping)} link(s) escape the repo):")
        for x in escaping:
            print("  " + x)
        fail = True
    else:
        print("public-view: no doc links escape the repo.")

if fail:
    sys.exit(1)
print("All local markdown links and source doc references resolve.")

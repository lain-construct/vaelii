#!/usr/bin/env python3
"""Check relative markdown links across the repo's docs resolve to real files.

Scans docs/**.md plus the contributor scaffolding (README, CONTRIBUTING, CONTRIBUTORS,
the CLAs, SECURITY, the PR template). Reports any [text](path) link whose target
(relative to the linking file) is missing. Skips http(s)/mailto links and pure
#anchors. Drops #fragments and ?query before resolving. Code-fence contents are
skipped so example links don't count.

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

missing, escaping = [], []
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
            if target.startswith(("http://", "https://", "mailto:", "#")):
                continue
            target = target.split('#', 1)[0].split('?', 1)[0].strip()
            if not target:
                continue
            resolved = os.path.normpath(os.path.join(os.path.dirname(path), target))
            escapes = not (resolved == ROOT or resolved.startswith(ROOT + os.sep))
            if public and escapes:
                escaping.append(f"{rel}:{i} -> {target}  (link escapes the repo)")
                continue
            if not os.path.exists(resolved):
                missing.append(f"{rel}:{i} -> {target}")

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

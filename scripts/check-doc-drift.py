#!/usr/bin/env python3
"""Check that doc claims about the code still match the code.

Scans README.md and docs/**.md for the drift classes that actually bite:

  E1  defrecord/defprotocol snippets whose name or field list no longer
      matches the definition under src/ (the Atomic/Rule/Deduction class).
  E2  Backticked var refs — `vaelii.x.y/fn` or `alias/fn` for a known
      alias — whose definition is missing from the resolved namespace.
  E3  VAELII_* env vars that appear nowhere in src/, scripts/, resources/,
      or project.clj.
  E4  Backticked repo paths (docs/x.md, scripts/x, src/.../y.clj,
      resources/...) that do not exist.
  E5  A reference from inside the repo to an agent instruction file
      (`CLAUDE.md`, `.claude/...`).  Those are stow-linked from a separate
      dotfiles repo and gitignored here, so a reader who clones this repo
      does not have them: a pointer at one is a dead end, and the knowledge
      belongs in docs/ instead.  Scans source and scripts as well as docs.
  E6  A doc under docs/ that nothing links to — index.md is the map, so a
      doc it does not reach is one nobody finds.
  E7  Archaeology: prose narrating the project's own past ("there used to be",
      "was previously", "the old behaviour", "before the fix").  A doc and a
      comment describe what the code does now; a diff already records how it
      got here.  Only the unambiguous phrasings are errors — plain "X used to
      Y" collides with "used to" meaning *employed to* ("the key used to diff
      against what is stored"), so it is W7 and the hook catches it at the
      keystroke instead.  Scans source and scripts as well as docs.
  E8  `(requiring-resolve 'ns/var)` on a literal symbol anywhere under src/
      except vaelii.impl.wiring — a layering cut left at its call site, where
      nothing counts it and nothing stops the next one.  A computed symbol (a
      keyword->var registry) and the two optional backends are exempt.
  E9  Futurology: prose naming work as forthcoming ("on the roadmap", "is the
      next step", "left for a future pass", a `## TODO` section).  E7's mirror
      image and the same argument — the present is the only tense a doc has.
      Stating an ABSENCE is not futurology and is wanted ("there is no beta
      network", "## What is not built"): an absence is a fact about the engine.
      What this bans is the promise attached to one.
  E10 A `declare` with no comment above it saying which cycle forces it, or one
      whose every use is below its own definition (so it does nothing).  The
      preferred fix is a reordering; the comment is where "an ordering cannot
      fix this" gets written down.
  W1  Line-number citations into .clj files (`foo.clj:123`) — warned, not
      failed: cite the var name instead, line numbers always rot.
  W2  Backticked `alias/name` for an UNKNOWN alias whose name is defined
      nowhere under src/ or test/ — a likely renamed alias.
  W6  Backticked KB symbols (`set/forwardRule`, `do/label` — namespaced KB
      performatives/markers, NOT Clojure vars) absent from the KB corpus.
  W7  The ambiguous half of E7 — see above.

Not flagged: MIME types (`application/json`), Maven coordinates / java
packages (dotted group ids not starting with `vaelii`).

vaelii is self-contained (no sibling checkouts), so every reference must
resolve within the repo — missing env vars and paths are hard errors, not
"unverifiable" warnings.

Errors exit 1; warnings exit 0. False positives go in
scripts/check-doc-drift-allowlist.txt (one literal token per line, matched
against the flagged token; # comments allowed).
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "src")
TEST_SRC = os.path.join(ROOT, "test")
RESOURCES = os.path.join(ROOT, "resources")
FENCE = re.compile(r"^\s*(```|~~~)")

# Conventional alias -> namespace map (harvested from the `:as` requires across
# src/ and test/). Aliases not listed fall back to a global any-namespace
# name-existence check (W2).
ALIASES = {
    "v": "vaelii.core", "core": "vaelii.core",
    "aspif": "vaelii.impl.asp.aspif", "atoms": "vaelii.impl.asp.atoms",
    "clasp": "vaelii.impl.asp.clasp", "clingo": "vaelii.impl.asp.clingo",
    "edge": "vaelii.impl.asp.edge", "label": "vaelii.impl.asp.label",
    "solver": "vaelii.impl.asp.solver",
    "budget": "vaelii.impl.budget", "chain": "vaelii.impl.chain",
    "checks": "vaelii.impl.checks", "core-context": "vaelii.impl.core-context",
    "backend": "vaelii.impl.disk.backend", "disk": "vaelii.impl.disk.backend",
    "dur": "vaelii.impl.disk.durability", "f": "vaelii.impl.disk.files",
    "dkv": "vaelii.impl.disk.kv", "lock": "vaelii.impl.disk.lock",
    "drs": "vaelii.impl.disk.record-store",
    "infer": "vaelii.impl.infer",
    "integrate": "vaelii.impl.integrate", "jtms": "vaelii.impl.jtms",
    "kb": "vaelii.impl.kb", "kv": "vaelii.impl.kv",
    "levels": "vaelii.impl.levels", "lvl": "vaelii.impl.levels",
    "mem": "vaelii.impl.memory", "nm": "vaelii.impl.naming",
    "nat": "vaelii.impl.nat", "observe": "vaelii.impl.observe",
    "plan": "vaelii.impl.plan", "p": "vaelii.impl.protocols",
    "provers": "vaelii.impl.provers", "reindex": "vaelii.impl.reindex",
    "rete": "vaelii.impl.rete", "rewrite": "vaelii.impl.rewrite",
    "rw": "vaelii.impl.rewrite", "rules": "vaelii.impl.rules",
    "vr": "vaelii.impl.rules", "seed": "vaelii.impl.seed",
    "sentex": "vaelii.impl.sentex", "sx": "vaelii.impl.sentex",
    "settle": "vaelii.impl.settle", "solve": "vaelii.impl.solve",
    "special": "vaelii.impl.special", "starter": "vaelii.impl.starter",
    "strength": "vaelii.impl.strength", "tax": "vaelii.impl.taxonomy",
    "taxonomy": "vaelii.impl.taxonomy", "web": "vaelii.impl.web",
    "wff": "vaelii.impl.wff",
}

# `deftest` (clojure.test) and `defroutes` (reitit/ring) define vars too, and
# docs cite them by their test-ns / browser-ns alias; include so those refs
# resolve instead of warning.
DEF_RE = r"\(def(?:n|n-|macro|multi|method|protocol|record|type|once|test|routes)?\s+(?:\^\S+\s+|\^\{[^}]*\}\s+)*"

# Namespaced KB SYMBOLS (performatives, work-state markers, aggregate operators) —
# not Clojure vars. Checked for existence against the source + resources corpus
# (W6), never against the def index. `set/*Rule`, `do/label`, `agg/count`, ...
KB_SYMBOL_PREFIXES = {"set", "do", "agg"}

# MIME types in API docs (`application/json`, `application/nippy`).
MIME_PREFIXES = {"application", "text", "multipart", "image", "audio", "video"}


def load_allowlist():
    allow = set()
    p = os.path.join(ROOT, "scripts", "check-doc-drift-allowlist.txt")
    if os.path.exists(p):
        for line in open(p):
            line = line.strip()
            if line and not line.startswith("#"):
                allow.add(line)
    return allow


def md_files():
    p = os.path.join(ROOT, "README.md")
    if os.path.exists(p):
        yield p
    for dirpath, _, names in os.walk(os.path.join(ROOT, "docs")):
        for n in sorted(names):
            if n.endswith(".md"):
                yield os.path.join(dirpath, n)


def clj_files():
    for dirpath, _, names in os.walk(SRC):
        for n in names:
            if n.endswith(".clj"):
                yield os.path.join(dirpath, n)


def ns_to_path(ns):
    return os.path.join(SRC, ns.replace(".", "/").replace("-", "_") + ".clj")


def parse_field_vector(text, start):
    """Symbols inside the [...] starting at text[start]; ;; comments dropped."""
    depth, i, buf = 0, start, []
    while i < len(text):
        c = text[i]
        if c == "[":
            depth += 1
        elif c == "]":
            depth -= 1
            if depth == 0:
                break
        buf.append(c)
        i += 1
    body = re.sub(r";[^\n]*", " ", "".join(buf))
    return re.findall(r"[A-Za-z_*+!?<>=-][\w*+!?<>=.'-]*", body)


def record_fields_in(text, name):
    m = re.search(r"\(def(?:record|protocol)\s+" + re.escape(name) + r"\b", text)
    if m is None:
        return None
    bracket = text.find("[", m.end())
    if bracket == -1:
        return []  # defprotocol: no field vector
    return parse_field_vector(text, bracket)


# Build the code-side indexes once.
src_text = {}
all_def_names = set()
for path in clj_files():
    text = open(path).read()
    src_text[path] = text
    for m in re.finditer(DEF_RE + r"([\w*+!?<>=.'-]+)", text):
        all_def_names.add(m.group(1))
    if "defprotocol" in text:  # protocol method signatures are definitions too
        for m in re.finditer(r"^\s+\(([a-z][\w*+!?<>=.'-]*)\s+\[", text, re.M):
            all_def_names.add(m.group(1))

# Test definitions count as "defined under the repo" for the W2 existence check:
# docs cite test vars by their test-ns alias. clj_files() only walks src/, so
# harvest the test tree's def names separately.
if os.path.isdir(TEST_SRC):
    for dirpath, _, names in os.walk(TEST_SRC):
        for n in names:
            if n.endswith(".clj"):
                try:
                    t = open(os.path.join(dirpath, n)).read()
                except (UnicodeDecodeError, OSError):
                    continue
                for m in re.finditer(DEF_RE + r"([\w*+!?<>=.'-]+)", t):
                    all_def_names.add(m.group(1))

# KB corpus for W6: every .clj/.txt/.edn under src + resources. Built lazily —
# only docs that mention KB symbols pay.
_kb_corpus = None


def kb_corpus():
    global _kb_corpus
    if _kb_corpus is None:
        chunks = list(src_text.values())
        for root in (RESOURCES,):
            for dirpath, _, names in os.walk(root):
                for n in names:
                    if n.endswith((".clj", ".txt", ".edn")):
                        try:
                            chunks.append(open(os.path.join(dirpath, n)).read())
                        except (UnicodeDecodeError, OSError):
                            pass
        _kb_corpus = "\n".join(chunks)
    return _kb_corpus


allow = load_allowlist()
allow_used = set()  # allowlist tokens that actually suppressed a finding
errors, warnings = [], []


def flag(kind, doc, token, msg):
    if token in allow:
        allow_used.add(token)
        return
    (errors if kind.startswith("E") else warnings).append(
        f"{kind} {os.path.relpath(doc, ROOT)}: {msg}")


# nsish words that are directory/language names, not aliases.
NS_STOP = {"docs", "scripts", "src", "resources", "test", "target",
           "checkouts", "bench", "vaelii"}

for doc in md_files():
    lines = open(doc).read().split("\n")

    # Split into fenced/unfenced views.
    in_fence, fence_lines, prose_lines = False, [], []
    for line in lines:
        if FENCE.match(line):
            in_fence = not in_fence
            continue
        (fence_lines if in_fence else prose_lines).append(line)
    fenced, prose = "\n".join(fence_lines), "\n".join(prose_lines)
    whole = "\n".join(lines)

    # E1: defrecord/defprotocol snippets in fenced blocks.
    for m in re.finditer(r"\(def(record|protocol)\s+([A-Za-z][\w.-]*)", fenced):
        kind, name = m.groups()
        hits = [p for p, t in src_text.items()
                if re.search(r"\(def" + kind + r"\s+" + re.escape(name) + r"(?![\w.-])", t)]
        if not hits:
            flag("E1", doc, name, f"doc shows (def{kind} {name} ...) but no such "
                 f"def{kind} exists under src/")
            continue
        if kind == "record":
            doc_fields = parse_field_vector(fenced, fenced.find("[", m.end()))
            real_fields = record_fields_in(src_text[hits[0]], name)
            if doc_fields and real_fields and doc_fields != real_fields:
                flag("E1", doc, name,
                     f"(defrecord {name}) fields drifted: doc {doc_fields} "
                     f"vs code {real_fields} ({os.path.relpath(hits[0], ROOT)})")

    # E2: backticked var refs.
    for m in re.finditer(r"`([A-Za-z][\w.-]*)/([\w*+!?<>=.'-]+)`", whole):
        nsish, name = m.groups()
        token = f"{nsish}/{name}"
        if (nsish in NS_STOP or name.isdigit() or "<" in name or ">" in name
                or ("*" in name and not re.fullmatch(r"\*[^*]+\*", name))
                or re.search(r"\.(md|sh|clj|cljs|cljc|edn|txt|py|svg|yml|yaml|json|csv|log|idx)$", name)):
            continue
        if "." in nsish and nsish.startswith("vaelii"):
            ns = nsish
        elif nsish in ALIASES:
            ns = ALIASES[nsish]
        else:
            ns = None
        if ns:
            path = ns_to_path(ns)
            if os.path.exists(path):
                t = src_text.get(path, "")
                defined = re.search(DEF_RE + re.escape(name) + r"(?![\w*+!?<>=.'-])", t) \
                    or ("defprotocol" in t and re.search(r"^\s+\(" + re.escape(name) + r"\s+\[", t, re.M))
                if not defined:
                    flag("E2", doc, token,
                         f"`{token}` not defined in {os.path.relpath(path, ROOT)}")
            # ns file absent: skip (nothing to verify against).
        else:
            if nsish in MIME_PREFIXES:
                continue
            if "." in nsish and not nsish.startswith("vaelii"):
                continue  # Maven coordinate / java package, not an alias
            if nsish in KB_SYMBOL_PREFIXES:
                if token not in kb_corpus():
                    flag("W6", doc, token,
                         f"KB symbol `{token}` not found anywhere in src/ or "
                         f"resources/")
                continue
            # Unknown alias: any-namespace existence check.
            if re.fullmatch(r"[a-z][\w.-]*", nsish) and name not in all_def_names \
               and not name.startswith("*"):
                flag("W2", doc, token,
                     f"`{token}` — `{name}` not found as a definition anywhere "
                     f"under src/ or test/ (unknown alias `{nsish}`; rename?)")

    # E3: env vars.
    for var in set(re.findall(r"\bVAELII_[A-Z0-9_]+\b", whole)):
        if var in allow:
            allow_used.add(var)
            continue
        kw = ":" + var.lower().replace("_", "-")
        found = any(var in t or kw in t for t in src_text.values())
        if not found:
            # test/ carries the VAELII_TEST_* knobs; scan it too.
            roots = [os.path.join(ROOT, "project.clj"),
                     os.path.join(ROOT, "scripts"), RESOURCES, TEST_SRC]
            for p in roots:
                if os.path.isfile(p):
                    t = open(p).read()
                    if var in t or kw in t:
                        found = True
                        break
                    continue
                if os.path.isdir(p):
                    for dp, _, ns in os.walk(p):
                        for n in ns:
                            try:
                                t = open(os.path.join(dp, n)).read()
                                if var in t or kw in t:
                                    found = True
                                    break
                            except (UnicodeDecodeError, IsADirectoryError, OSError):
                                pass
                        if found:
                            break
                if found:
                    break
        if not found:
            flag("E3", doc, var,
                 f"env var {var} appears in docs but nowhere in code")

    # E4: backticked repo paths.
    for m in re.finditer(r"`((?:docs|scripts|src|resources)/[\w./-]+)`", prose):
        rel = m.group(1)
        if any(ch in rel for ch in "*<>{") or rel.endswith("/") \
           or "..." in rel or re.search(r"/[A-Z]($|/)", rel):
            continue
        if not os.path.exists(os.path.join(ROOT, rel)):
            flag("E4", doc, rel, f"path `{rel}` does not exist")

    # W1: line-number citations into clj files.
    for m in re.finditer(r"[\w/-]+\.clj:\d+", prose):
        flag("W1", doc, m.group(0),
             f"line-number citation `{m.group(0)}` — cite the var name instead")


# ── E5: no reference from inside the repo to an agent instruction file ──────
# They are gitignored here (stow-linked from a dotfiles repo), so a pointer at
# one is a dead end for anyone who clones this repo.  This file names them to
# check for them, so it excludes itself.
AGENT_FILE = re.compile(r"CLAUDE(\.local)?\.md|\.claude/")
SELF = os.path.abspath(__file__)


def repo_text_files():
    yield from md_files()
    for sub in ("src", "test", "bench"):
        for dirpath, _, names in os.walk(os.path.join(ROOT, sub)):
            for n in sorted(names):
                if n.endswith(".clj"):
                    yield os.path.join(dirpath, n)
    scripts = os.path.join(ROOT, "scripts")
    for dirpath, _, names in os.walk(scripts):
        for n in sorted(names):
            if n.endswith((".sh", ".py", ".clj")):
                yield os.path.join(dirpath, n)
    yield os.path.join(ROOT, "project.clj")


for path in repo_text_files():
    if os.path.abspath(path) == SELF or not os.path.exists(path):
        continue
    for i, line in enumerate(open(path, errors="replace"), 1):
        m = AGENT_FILE.search(line)
        if m:
            rel = os.path.relpath(path, ROOT)
            flag("E5", path, m.group(0),
                 f"{rel}:{i} references `{m.group(0)}` — an agent instruction "
                 f"file, gitignored here; state the fact in docs/ instead")

# ── E6: every doc under docs/ is linked from another doc ───────────────────
# index.md is the map, so it needs no inbound link; dependencies.md is
# generated.
UNLINKED_OK = {"docs/index.md", "docs/dependencies.md",
               "docs/design/index.md", "docs/design/README.md"}
MD_LINK = re.compile(r"\[[^\]]*\]\(([^)#]+)")

linked = set()
for doc in md_files():
    for m in MD_LINK.finditer(open(doc).read()):
        target = m.group(1).strip()
        if target.startswith(("http:", "https:", "mailto:")):
            continue
        resolved = os.path.normpath(os.path.join(os.path.dirname(doc), target))
        linked.add(os.path.relpath(resolved, ROOT))

for doc in md_files():
    rel = os.path.relpath(doc, ROOT)
    if rel == "README.md" or rel in UNLINKED_OK or rel in linked:
        continue
    flag("E6", doc, rel, f"`{rel}` is linked from no other doc — add it to the "
                         f"map so a reader can find it")

# ── E7/W7: no archaeology — the present is the only tense ──────────────────
# Split by how ambiguous the phrasing is.  ARCHAEOLOGY is unambiguous: nothing
# but the project's own past reads that way, so it fails the build.  AMBIGUOUS
# is the "X used to Y" family, which collides with "used to" meaning *employed
# to* — a warning here, and the write-time hook is where it earns its keep.
# This file names the phrases to look for them, so it excludes itself.
# The banned repo name is assembled from halves: the checker must not itself
# contain the name it bans, or it would be the tree's one occurrence.
_BANNED_REPO = "vaelii-" + "shell"
ARCHAEOLOGY = re.compile(
    r"\b(there|it|which|that|this) used to\b"
    r"|\bwe used to\b"
    r"|\b(was|were) previously\b"
    r"|\bpreviously (wrong|broken|answerable|detected|named|called|stored|"
    r"written|done|built|required|the case)\b"
    r"|\bthe old (way|approach|code|version|behaviou?r|implementation|scheme"
    r"|form|rule|check|path|semantics)\b"
    r"|\bbefore (the|this|that) fix\b|\bprior to the fix\b"
    r"|\bthe point of the change\b"
    r"|\b(formerly|renamed from|was renamed|used to be called)\b"
    r"|\b" + _BANNED_REPO + r"\b",
    re.I)
# "<lowercase word> used to <verb>", excluding the auxiliary ("be used to") and
# the appositive (", used to …") — both of which are the *employed to* sense.
AMBIGUOUS = re.compile(r"(?<!be )(?<!,)\b[a-z0-9`)\]*]+ used to [a-z]")
# A prompt under docs/design/**-prompts/ briefs work not yet done, so "before
# the change" there means "before you make it" — a verification step, not a
# memoir.
PROMPT_DIR = re.compile(r"docs/design/[a-z-]*prompts/")

for path in repo_text_files():
    if os.path.abspath(path) == SELF or not os.path.exists(path):
        continue
    rel = os.path.relpath(path, ROOT)
    if rel.startswith("docs/design/complete/") or rel.startswith("resources/"):
        continue          # dated reviews quote as-of; resources/ is third-party
    prompt = bool(PROMPT_DIR.search(rel))
    # W7 is prose-only: in a docstring "used to" is usually the *employed to*
    # sense ("the content used to diff against what is stored"), which would
    # make it permanent noise.  E7 still reads every file, and the write-time
    # hook covers the ambiguous half of a comment as it is typed.
    soft_ok = rel.endswith(".md") and not prompt
    for i, line in enumerate(open(path, errors="replace"), 1):
        m = ARCHAEOLOGY.search(line)
        kind = "E7"
        if not m and soft_ok:
            m, kind = AMBIGUOUS.search(line), "W7"
        if m:
            flag(kind, path, m.group(0).strip(),
                 f"{rel}:{i} `{m.group(0).strip()}` — archaeology; say what "
                 f"the code does now, not what it did")

# ── E9: no futurology — the other direction of the same rule ────────────────
# E7 bans narrating the project's past; this bans announcing its future. A doc
# that names work as forthcoming is making a commitment on behalf of whoever
# reads it next, and what gets built is not knowable in advance.
#
# The line to hold: an ABSENCE is a fact and belongs in the docs — "there is no
# beta network", "## What is not built", "nothing reads the `:out` slot". A
# PROMISE about that absence does not. So the patterns below match the promise
# ("on the roadmap", "left for a future pass", "is the next step"), never the
# bare statement that something does not exist.
#
# Deliberately narrow, for the reason E7 is: "a future handle", "a future
# channel" and "a future change to this test" are all ordinary present-tense
# prose, and a check that flags them is a check people learn to route around.
FUTUROLOGY = re.compile(
    r"^#{2,}\s*TODO\b"
    r"|\bon the roadmap\b|\bthe roadmap (files|names|calls|has)\b|\broadmap\.md\b"
    r"|\bis the next step\b|\bthe natural next (step|variant)\b"
    r"|\bleft for a (future|someday|later)\b"
    r"|\ba future (pass|release|version|variant|revision)\b"
    r"|\bwe (plan|intend) to\b|\bis planned for\b"
    r"|\bcoming soon\b|\bfor now, until\b"
    r"|\bthe remaining (step|work|win)\b"
    r"|\bis a follow-on\b|\bseparate follow-ons?\b"
    r"|\bwould replace it (later|eventually)\b",
    re.I | re.M)

for path in repo_text_files():
    if os.path.abspath(path) == SELF or not os.path.exists(path):
        continue
    rel = os.path.relpath(path, ROOT)
    # docs/design/ briefs unbuilt work by definition — that whole tree is the
    # place plans are allowed to live, and it does not ship. resources/ is
    # third-party. CONTRIBUTING.md states this rule, so it quotes the
    # phrasings in order to ban them.
    if (rel.startswith(("docs/design/", "resources/"))
            or rel == "CONTRIBUTING.md"):
        continue
    for i, line in enumerate(open(path, errors="replace"), 1):
        m = FUTUROLOGY.search(line)
        if m:
            flag("E9", path, m.group(0).strip(),
                 f"{rel}:{i} `{m.group(0).strip()}` — futurology; say what the "
                 f"engine does now. An absence is a fact and may be stated; a "
                 f"plan to remove it may not")

# ── E8: a layering cut belongs in the wiring inventory, not at its call site ─
# `(requiring-resolve 'ns/var)` on a *literal* symbol is an edge the require graph
# could express but does not — a layering cut.  Left at its call site it is
# invisible: nothing counts them and nothing stops the next one.  So they live in
# vaelii.impl.wiring, one file, each owing the reason it cannot be an ordinary
# require (see that namespace's docstring).  Two shapes are not cuts:
#
#   - a *computed* symbol — `(requiring-resolve sym)` read off a keyword->var
#     registry (core's reasoners / calculi / solvers, imperative's `do/` handlers,
#     foreign's plugins, the LLM providers).  Deferral is the feature: the table is
#     the public way to ask for a subsystem, and naming one must not load eight.
#   - an optional backend whose entire point is not being loaded — the dense TMS
#     (RoaringBitmap, fastutil) and the clingo bridge (JNA, libclingo).  Listed
#     here by target, so adding one is a deliberate edit rather than a habit.
#
# What this does NOT see, stated so nobody over-trusts it: only the literal form
# is matched, so binding the symbol first — `(let [s 'a.b/c] (requiring-resolve s))`
# — is a cut this rule reads as a registry and passes.  Closing that would mean
# banning the computed form outright, which is the shape the four legitimate
# registries above are built from.  So the rule catches the cut somebody writes
# without thinking, not the one somebody hides; the inventory is a convention the
# check defends, not a sandbox it enforces.
E8_OK_FILES = {"src/vaelii/impl/wiring.clj"}
E8_OK_TARGETS = {"vaelii.impl.dense-jtms/create-dense-tms",
                 "vaelii.impl.asp.clingo/solve",
                 "vaelii.impl.asp.clingo/classify-both",
                 "vaelii.impl.asp.clingo/available?"}
E8_LITERAL = re.compile(r"\(requiring-resolve\s+'([^\s()]+)")

for path in clj_files():
    rel = os.path.relpath(path, ROOT)
    if rel in E8_OK_FILES:
        continue
    for i, line in enumerate(open(path, errors="replace"), 1):
        m = E8_LITERAL.search(line)
        if not m or m.group(1) in E8_OK_TARGETS:
            continue
        flag("E8", path, m.group(1),
             f"{rel}:{i} `requiring-resolve '{m.group(1)}` — a layering cut at its "
             f"call site; give it a real fix, or move it to vaelii.impl.wiring "
             f"with the reason it cannot be a require")

# ── E10: a declare owes a reason, and a dead one owes nothing ───────────────
# `declare` is how a file admits its definitions do not fall in dependency
# order.  Two things go wrong with one, and both are mechanical:
#
#   - it carries no reason.  A genuine cycle (`cmp-term` descends to `cmp-seq`,
#     which compares with `cmp-term`) and a mere ordering accident read exactly
#     alike at the declare, and only one of them is allowed to stay — so the
#     comment above it is what says which, and without it the next reader has to
#     re-derive the call graph to find out.
#   - it is dead.  A name whose every use is below its own definition needs no
#     forward reference at all; `defn` interns the var before compiling the body,
#     so even self-recursion does not need one.  A dead declare reads as a claim
#     about the file that is not true.
#
# Reordering is the preferred fix and this rule does not know when one is
# possible — it asks for the reason, and the reason is where "an ordering cannot
# fix this" gets written down.
DECLARE = re.compile(r"^\s*\(declare\s+(.+?)\)\s*$")
DEFINES = r"^\s*\((?:defn-?|def|defmacro|defmulti|deftype|defrecord|defprotocol)\s+(?:\^\S+\s+)*{}[\s)]"


def blank_strings(text):
    """Strings and comments emptied, newlines kept, so line numbers still hold."""
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c == "\\" and i + 1 < n:          # char literal: \" \( \;
            out.append("  ")
            i += 2
        elif c == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == '"':
                    j += 1
                    break
                j += 1
            out.append("\n" * text[i:j].count("\n"))
            i = j
        elif c == ";":
            while i < n and text[i] != "\n":
                i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


for path in clj_files():
    rel = os.path.relpath(path, ROOT)
    raw = open(path, errors="replace").read().splitlines()
    code = blank_strings("\n".join(raw)).splitlines()
    for i, line in enumerate(code):
        m = DECLARE.match(line)
        if not m:
            continue
        j = i - 1
        while j >= 0 and not raw[j].strip():
            j -= 1
        if not (j >= 0 and raw[j].lstrip().startswith(";;")):
            flag("E10", path, f"{rel}:declare",
                 f"{rel}:{i + 1} `{line.strip()}` — a declare with no reason above "
                 f"it; say which cycle forces it, or reorder and drop it")
        for name in m.group(1).split():
            pat = re.compile(DEFINES.format(re.escape(name)))
            defined = next((k for k, l in enumerate(code) if pat.match(l)), None)
            if defined is None:
                continue
            word = re.compile(rf"(?<![\w.*+!?<>=/-]){re.escape(name)}(?![\w.*+!?<>=/-])")
            if not any(word.search(l) for k, l in enumerate(code)
                       if k != i and k != defined and k < defined):
                flag("E10", path, f"{rel}:{name}",
                     f"{rel}:{i + 1} `{name}` is declared but never used above its "
                     f"definition (line {defined + 1}) — the declare does nothing; "
                     f"`defn` interns the var before it compiles the body")

for e in errors:
    print(e)
for w in warnings:
    print("warn:", w)

# Dead allowlist entries: tokens that suppressed nothing this run, so the doc
# reference they excused is gone or the checker stopped flagging it. Advisory
# only (exit unaffected) — prune them from the allowlist.
dead = sorted(allow - allow_used)
if dead:
    print(f"\nadvisory: {len(dead)} dead allowlist entr"
          f"{'y' if len(dead) == 1 else 'ies'} (matched nothing this run) — "
          f"prune from scripts/check-doc-drift-allowlist.txt:")
    for tok in dead:
        print(f"  - {tok}")

print(f"\n{len(errors)} errors, {len(warnings)} warnings "
      f"across {sum(1 for _ in md_files())} docs.")
sys.exit(1 if errors else 0)

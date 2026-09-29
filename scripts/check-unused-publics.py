#!/usr/bin/env python3
"""scripts/check-unused-publics.py — a public var nothing calls is a finding, not a shrug.

`vaelii.impl.*` is explicitly free to change (`docs/namespaces.md`), which
makes this a **dead-code** check rather than an API-surface one: the six public
namespaces are frozen by `public_api_test`, and asking whether *they* have callers
would be asking the wrong question. What is left is exactly one question — is there a
`defn` under `impl/` (or in the test/bench trees) that nothing references.

The scan is clj-kondo's own analysis over `src test bench`: public var definitions
minus var usages, minus the categories below, diffed against
`scripts/unused-publics-baseline.txt`. A name that appears in the scan and not in the
baseline fails. `--update` rewrites the baseline.

    scripts/check-unused-publics.py            # diff against the baseline; exit 1 on a new one
    scripts/check-unused-publics.py --update   # rewrite the baseline (its own commit, please)

EXCLUDED BY CONSTRUCTION, and the list is the design. These are whole categories the
analysis can never see a caller for, not individual awkward cases:

  - private vars                    nothing outside the namespace could call them anyway
  - `-main`                         called by a JVM, not by code
  - `defrecord` / `deftype`         the type, and its `->Ctor` / `map->Ctor` pair
  - protocol methods                dispatched through the protocol, never named
  - `deftest` / `deftest-kb` / `defspec`   called by the test runner
  - `defmulti`                      dispatched, and its methods are `defmethod`
  - `declare`                       a forward declaration is not a definition
  - the six public namespaces       frozen by `public_api_test`; a different question

ADDED BY CONSTRUCTION: `vaelii.browser.access/defreads` defines one public wrapper per
name in its argument list, and kondo records none of them as a definition. The scan
reads that list from the source and counts each name as a definition in
`vaelii.browser.access`, so a wrapper nothing calls is a finding like any other defn.

Anything else that turns out to be invisible goes in the **baseline with a reason**,
never here. A category added to dodge one finding hides every future finding like it.

NO SIBLING-CLAIMS MACHINERY. A scan of this shape usually needs a way to say "this
var's only caller lives in a repo that is not checked out". Here that is one baseline
line with the reason, not a mechanism: the SQL record stores (`vaelii-postgres`,
`vaelii-sqlite`) build their roster with `roster/collector`, and the foreign-reader
plugin's contract is `requiring-resolve` from an edn manifest, calling nothing here.
"""

from __future__ import annotations

import argparse
import collections
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
BASELINE = ROOT / "scripts" / "unused-publics-baseline.txt"
PATHS = ["src", "test", "bench"]
ACCESS = ROOT / "src" / "vaelii" / "browser" / "access.clj"

# The six the public-namespace test freezes.  Naming them here is not a second manifest:
# the test decides what the set *is*, and a name that left it would fail there first.
PUBLIC_NAMESPACES = {
    "vaelii.core", "vaelii.client", "vaelii.starter",
    "vaelii.web", "vaelii.serve", "vaelii.cli",
}

DEFINED_BY_SKIP = {
    "clojure.test/deftest",
    "vaelii.test-util/deftest-kb",
    "clojure.test.check.clojure-test/defspec",
    "clojure.core/defprotocol",
    "clojure.core/defrecord",
    "clojure.core/deftype",
    "clojure.core/definterface",
    "clojure.core/declare",
    "clojure.core/defmulti",
}


def analysis() -> dict:
    """clj-kondo's analysis over the three trees."""
    proc = subprocess.run(
        ["clj-kondo", "--lint", *PATHS,
         "--config", '{:output {:analysis true :format :json}}'],
        cwd=ROOT, capture_output=True, text=True,
    )
    # kondo exits 2 when it has findings of its own; the analysis is still on stdout,
    # and the findings are the `kondo` check's business rather than this one's.
    if not proc.stdout.strip():
        sys.stderr.write("check-unused-publics: clj-kondo produced no analysis\n")
        sys.stderr.write(proc.stderr[-2000:])
        raise SystemExit(2)
    return json.loads(proc.stdout)["analysis"]


def defreads_names() -> list[str]:
    """The op names in `access.clj`'s `(defreads …)` form, comments stripped."""
    src = ACCESS.read_text()
    start = src.index("(defreads\n")
    depth = 0
    for i, ch in enumerate(src[start:], start):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0:
                body = src[start + len("(defreads"):i]
                return re.sub(r";[^\n]*", "", body).split()
    raise SystemExit("check-unused-publics: unbalanced (defreads …) in access.clj")


def scan() -> list[str]:
    """Every public var definition with zero var usages, as sorted `ns/name`."""
    a = analysis()
    # A var's call to itself is not a caller: a recursive fn nothing else names is as
    # unreached as one with no body at all.
    used = collections.Counter(
        (u.get("to"), u.get("name")) for u in a["var-usages"]
        if not (u.get("from") == u.get("to") and u.get("from-var") == u.get("name")))
    out = []
    defs = a["var-definitions"] + [{"ns": "vaelii.browser.access", "name": n}
                                   for n in defreads_names()]
    for v in defs:
        name, ns = v["name"], v["ns"]
        if v.get("private") or v.get("defined-by") in DEFINED_BY_SKIP:
            continue
        if name == "-main" or ns in PUBLIC_NAMESPACES:
            continue
        if name.startswith("->") or name.startswith("map->"):
            continue
        if used[(ns, name)] == 0:
            out.append(f"{ns}/{name}")
    return sorted(set(out))


def read_baseline() -> list[str]:
    if not BASELINE.exists():
        return []
    names = []
    for line in BASELINE.read_text().splitlines():
        line = line.split("#", 1)[0].strip()
        if line:
            names.append(line)
    return sorted(set(names))


def write_baseline(names: list[str], previous_text: str | None) -> None:
    """Rewrite the baseline, carrying the header and each surviving name's reason across.

    The reason is the point of the file, so a refresh must not silently drop one: a
    line whose reason is lost is a claim nobody can check later.

    What does *not* survive is a comment between entries. The entries are rewritten
    sorted, so an interior divider would keep its position while the lines under it
    moved — correct after one refresh and a lie after the next. The per-entry tag
    carries that distinction instead, which is why the file is one flat list.
    """
    reasons: dict[str, str] = {}
    header: list[str] = []
    if previous_text:
        for line in previous_text.splitlines():
            if line.startswith("#") or not line.strip():
                if not reasons:
                    header.append(line)
                continue
            name, _, comment = line.partition("#")
            if comment.strip():
                reasons[name.strip()] = comment.strip()
    body = []
    for n in names:
        body.append(f"{n}  # {reasons[n]}" if n in reasons else n)
    text = "\n".join(header + body) + "\n"
    BASELINE.write_text(text)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--update", action="store_true",
                    help="rewrite the baseline from the current scan")
    args = ap.parse_args()

    found = scan()

    if args.update:
        prev = BASELINE.read_text() if BASELINE.exists() else None
        write_baseline(found, prev)
        print(f"unused-publics: baseline written, {len(found)} entries")
        return 0

    baseline = read_baseline()
    new = [n for n in found if n not in baseline]
    gone = [n for n in baseline if n not in found]

    if new:
        print("A public var nothing calls, and not in the baseline:\n")
        for n in new:
            print(f"  {n}")
        print("\nEither it has a caller and the reference is missing, or it is dead and")
        print("should go. If it is reached by a route the analysis cannot see —")
        print("requiring-resolve, a quoted-symbol registry, a REPL affordance — add it to")
        print(f"{BASELINE.relative_to(ROOT)} with the reason, in its own commit.")
        return 1

    if gone:
        # Not a failure: a var that gained a caller or was deleted is the good direction,
        # and a ratchet that fails on improvement is one people route around.
        print(f"unused-publics: {len(found)} known; {len(gone)} baseline "
              f"entr{'y' if len(gone) == 1 else 'ies'} no longer unused "
              f"(refresh with --update): {', '.join(gone[:4])}"
              + (" …" if len(gone) > 4 else ""))
        return 0

    print(f"{len(found)} known, none new")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Draw the derived-state dependency graph: one self-contained HTML page from an export.

The export is the EDN `lein derived-state -- --edn <path>` writes (docs/caches.md, "The
derived-state register"): row ids, event ids, codes, registration sites and counts, and
no handle or sentence. The page template, scripts/derived-state-graph.html, reads the
export and scripts/derived-state-features.edn from two script elements and draws
everything in the browser, so a register change needs a new export and no edit here.

    lein derived-state -- --edn testbench/derived-state.edn
    python3 scripts/derived-state-graph.py testbench/derived-state.edn testbench/derived-state.html

The page also opens another export from a file input, so one generated page reads a
second reading without a regeneration.
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TEMPLATE = os.path.join(HERE, "derived-state-graph.html")
FEATURES = os.path.join(HERE, "derived-state-features.edn")


def embed(text):
    """EDN text safe inside a script element: `</` becomes `<\\u002f`, which the page's
    reader decodes back inside a string, the only place EDN can hold it."""
    return text.replace("</", "<\\u002f")


def main(argv):
    if len(argv) != 3:
        print(__doc__.strip().splitlines()[0])
        print("usage: derived-state-graph.py <export.edn> <out.html>")
        return 2
    src, out = argv[1], argv[2]
    with open(TEMPLATE, encoding="utf-8") as f:
        page = f.read()
    with open(src, encoding="utf-8") as f:
        export = f.read()
    with open(FEATURES, encoding="utf-8") as f:
        features = f.read()
    for mark in ("/*EXPORT*/", "/*FEATURES*/", "/*EXPORT-NAME*/"):
        if page.count(mark) != 1:
            print(f"derived-state-graph: the template holds {page.count(mark)} {mark}")
            return 1
    page = (page.replace("/*EXPORT*/", embed(export))
                .replace("/*FEATURES*/", embed(features))
                .replace("/*EXPORT-NAME*/", os.path.basename(src)))
    with open(out, "w", encoding="utf-8") as f:
        f.write(page)
    print(f"derived-state-graph: wrote {out} from {src}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

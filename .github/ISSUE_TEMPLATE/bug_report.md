---
name: Bug report
about: A reproducible defect in the engine, the starter KB, or the tooling
title: ''
labels: bug
assignees: ''
---

**What happened**
A clear description of the bug.

**Expected**
What you expected instead.

**Reproduce**
Steps to trigger it — ideally a self-contained REPL snippet starting from a fresh KB:

```clojure
(require '[vaelii.core :as v])
(def kb (v/open-kb {}))
;; minimal form that reproduces the problem
```

**Environment**
- Vaelii version / commit:
- Backend: <!-- memory | memory-dense | memory-columnar | disk | disk-memory |
                disk-dense | disk-columnar | overlay -->
- Reached through: <!-- library | lein cli | daemon (vaelii.impl.serve) | browser -->
- JDK / OS:

**Output**
Any stack trace, and the `:type` on the `ex-info` if the engine refused something.

For a *wrong answer* rather than a crash, `(v/why kb handle)` and
`(v/why-not kb goal context)` are usually more useful than a trace: they say what the
engine believed and what it was missing.

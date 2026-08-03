# Dependency licences

Every jar the engine's published coordinate resolves onto a consumer's
classpath: **55 artifacts**, 13 named by `project.clj` and
42 pulled in transitively.

This is the companion to [`THIRD-PARTY.md`](THIRD-PARTY.md), which covers the
assets *vendored into this repo* and deliberately excludes resolved
dependencies. Publishing an artifact is what makes the second list matter: a
coordinate is a promise about a whole classpath, not about one jar.

Each licence below is read from the artifact's own POM (following the parent
chain where a POM inherits one), not from a hand-kept list. Regenerate with:

```
scripts/build-dependency-inventory.py --src=../vaelii \
    --out=../vaelii/licenses/DEPENDENCIES.md
```

Generated 2026-07-31.

## Summary

| Licence | Artifacts |
|---|---|
| EPL-2.0 OR Apache-2.0 | 19 |
| EPL-1.0 | 15 |
| Apache-2.0 | 9 |
| MIT | 9 |
| 0BSD | 1 |
| Apache-2.0 OR EPL-1.0 | 1 |
| LGPL-2.1-or-later OR Apache-2.0 | 1 |

**Nothing a consumer resolves is GPL, AGPL or SSPL.** The one copyleft licence in
the runtime closure is LGPL-2.1-or-later, on JNA, and it appears as one half of a
dual licence the project states is the consumer's to choose:

> Java Native Access (JNA) is licensed under the LGPL, version 2.1 or later,
> or the Apache License, version 2.0. You can freely decide which license you
> want to apply to the project.

**Vaelii takes JNA under Apache-2.0.** Recording the election is the point:
an unrecorded dual licence is the one a reviewer has to re-derive.

The Eclipse and Apache licences carry no obligation the project does not
already meet by distributing this file and leaving upstream notices in the
jars intact. None of them restrict the SSPL terms under which the engine
itself is offered.

## Every artifact

`*` marks a dependency `project.clj` names directly.

| | Artifact | Version | Licence | As declared in the POM |
|---|---|---|---|---|
| * | `cheshire/cheshire` | 6.2.0 | MIT | The MIT License |
|  | `com.fasterxml.jackson.core/jackson-core` | 2.21.1 | Apache-2.0 | The Apache Software License, Version 2.0 |
|  | `com.fasterxml.jackson.dataformat/jackson-dataformat-cbor` | 2.21.1 | Apache-2.0 | The Apache Software License, Version 2.0 |
|  | `com.fasterxml.jackson.dataformat/jackson-dataformat-smile` | 2.21.1 | Apache-2.0 | The Apache Software License, Version 2.0 |
|  | `com.taoensso/encore` | 3.169.1 | EPL-1.0 | Eclipse Public License - v 1.0 |
| * | `com.taoensso/nippy` | 3.8.1 | EPL-1.0 | Eclipse Public License - v 1.0 |
| * | `com.taoensso/trove` | 1.2.0 | EPL-1.0 | Eclipse Public License - v 1.0 |
|  | `com.taoensso/truss` | 2.4.0 | EPL-1.0 | Eclipse Public License - v 1.0 |
|  | `commons-codec/commons-codec` | 1.15 | Apache-2.0 | Apache License, Version 2.0 |
|  | `commons-io/commons-io` | 2.21.0 | Apache-2.0 | Apache-2.0 |
|  | `crypto-equality/crypto-equality` | 1.0.1 | EPL-1.0 | Eclipse Public License |
|  | `crypto-random/crypto-random` | 1.2.1 | EPL-1.0 | Eclipse Public License |
| * | `hiccup/hiccup` | 2.0.0 | EPL-1.0 | Eclipse Public License |
|  | `io.airlift/aircompressor` | 2.0.3 | Apache-2.0 | Apache License 2.0 |
| * | `it.unimi.dsi/fastutil-core` | 8.5.19 | Apache-2.0 | Apache License, Version 2.0 |
|  | `meta-merge/meta-merge` | 1.0.0 | EPL-1.0 | Eclipse Public License |
|  | `metosin/reitit-core` | 0.10.1 | EPL-1.0 | Eclipse Public License |
| * | `metosin/reitit-ring` | 0.10.1 | EPL-1.0 | Eclipse Public License |
| * | `net.java.dev.jna/jna` | 5.19.1 | LGPL-2.1-or-later OR Apache-2.0 | LGPL-2.1-or-later; Apache-2.0 |
|  | `org.apache.commons/commons-fileupload2-core` | 2.0.0-M5 | Apache-2.0 | Apache-2.0 |
| * | `org.clojure/clojure` | 1.12.5 | EPL-1.0 | Eclipse Public License 1.0 |
|  | `org.clojure/core.specs.alpha` | 0.4.74 | EPL-1.0 | Eclipse Public License 1.0 |
|  | `org.clojure/spec.alpha` | 0.5.238 | EPL-1.0 | Eclipse Public License 1.0 |
|  | `org.clojure/tools.reader` | 1.6.0 | EPL-1.0 | Eclipse Public License 1.0 |
|  | `org.eclipse.jetty.ee/jetty-ee-webapp` | 12.1.8 | EPL-2.0 OR Apache-2.0 | EPL-2.0; Apache-2.0 |
|  | `org.eclipse.jetty.ee9.websocket/jetty-ee9-websocket-jetty-api` | 12.1.8 | EPL-2.0 OR Apache-2.0 | EPL-2.0; Apache-2.0 |
|  | `org.eclipse.jetty.ee9.websocket/jetty-ee9-websocket-jetty-common` | 12.1.8 | EPL-2.0 OR Apache-2.0 | EPL-2.0; Apache-2.0 |
|  | `org.eclipse.jetty.ee9.websocket/jetty-ee9-websocket-jetty-server` | 12.1.8 | EPL-2.0 OR Apache-2.0 | EPL-2.0; Apache-2.0 |
|  | `org.eclipse.jetty.ee9.websocket/jetty-ee9-websocket-servlet` | 12.1.8 | EPL-2.0 OR Apache-2.0 | EPL-2.0; Apache-2.0 |
|  | `org.eclipse.jetty.ee9/jetty-ee9-nested` | 12.1.8 | EPL-2.0 OR Apache-2.0 | EPL-2.0; Apache-2.0 |
|  | `org.eclipse.jetty.ee9/jetty-ee9-security` | 12.1.8 | EPL-2.0 OR Apache-2.0 | EPL-2.0; Apache-2.0 |
|  | `org.eclipse.jetty.ee9/jetty-ee9-servlet` | 12.1.8 | EPL-2.0 OR Apache-2.0 | EPL-2.0; Apache-2.0 |
|  | `org.eclipse.jetty.ee9/jetty-ee9-webapp` | 12.1.8 | EPL-2.0 OR Apache-2.0 | EPL-2.0; Apache-2.0 |
|  | `org.eclipse.jetty.toolchain/jetty-jakarta-servlet-api` | 5.0.2 | Apache-2.0 OR EPL-1.0 | Apache Software License - Version 2.0; Eclipse Public License - Version 1.0 |
|  | `org.eclipse.jetty.websocket/jetty-websocket-core-common` | 12.1.8 | EPL-2.0 OR Apache-2.0 | EPL-2.0; Apache-2.0 |
|  | `org.eclipse.jetty.websocket/jetty-websocket-core-server` | 12.1.8 | EPL-2.0 OR Apache-2.0 | EPL-2.0; Apache-2.0 |
|  | `org.eclipse.jetty/jetty-http` | 12.1.8 | EPL-2.0 OR Apache-2.0 | EPL-2.0; Apache-2.0 |
|  | `org.eclipse.jetty/jetty-io` | 12.1.8 | EPL-2.0 OR Apache-2.0 | EPL-2.0; Apache-2.0 |
|  | `org.eclipse.jetty/jetty-security` | 12.1.8 | EPL-2.0 OR Apache-2.0 | EPL-2.0; Apache-2.0 |
|  | `org.eclipse.jetty/jetty-server` | 12.1.8 | EPL-2.0 OR Apache-2.0 | EPL-2.0; Apache-2.0 |
|  | `org.eclipse.jetty/jetty-session` | 12.1.8 | EPL-2.0 OR Apache-2.0 | EPL-2.0; Apache-2.0 |
|  | `org.eclipse.jetty/jetty-unixdomain-server` | 12.1.8 | EPL-2.0 OR Apache-2.0 | EPL-2.0; Apache-2.0 |
|  | `org.eclipse.jetty/jetty-util` | 12.1.8 | EPL-2.0 OR Apache-2.0 | EPL-2.0; Apache-2.0 |
|  | `org.eclipse.jetty/jetty-xml` | 12.1.8 | EPL-2.0 OR Apache-2.0 | EPL-2.0; Apache-2.0 |
|  | `org.ring-clojure/ring-core-protocols` | 1.15.5 | MIT | The MIT License |
|  | `org.ring-clojure/ring-jakarta-servlet` | 1.15.5 | MIT | The MIT License |
|  | `org.ring-clojure/ring-websocket-protocols` | 1.15.5 | MIT | The MIT License |
| * | `org.roaringbitmap/RoaringBitmap` | 1.6.18 | Apache-2.0 | Apache 2 |
|  | `org.slf4j/slf4j-api` | 2.0.18 | MIT | MIT |
| * | `org.slf4j/slf4j-nop` | 2.0.18 | MIT | MIT |
| * | `org.tukaani/xz` | 1.12 | 0BSD | 0BSD |
|  | `ring/ring-codec` | 1.3.0 | MIT | The MIT License |
| * | `ring/ring-core` | 1.15.5 | MIT | The MIT License |
| * | `ring/ring-jetty-adapter` | 1.15.5 | MIT | The MIT License |
|  | `tigris/tigris` | 0.1.2 | EPL-1.0 | Eclipse Public License |

## Development and benchmark profiles

None of these ships. They are on the classpath only for the profile that names them,
they are absent from the published POM, and nothing a consumer resolves pulls them in
— which is why the closure above does not list them, and why the sentence about GPL is
scoped to that closure rather than to the repository.

| Profile | Coordinate | Licence | Note |
|---|---|---|---|
| `:bench` | `org.openjdk.jol/jol-core` | GPL-2.0 WITH Classpath-exception-2.0 | The Classpath Exception exists to permit exactly this linking: it lets an independent module link against the library without the GPL reaching that module. `bench/` is a profile-only source path and is not in the jar. |
| `:antq` | `com.github.liquidz/antq` | EPL-2.0 | The tool that generates this file. |
| `:dev` | `dev.weavejester/lein-cljfmt`, `lein-shell`, `lein-cloverage` | EPL-1.0 | Leiningen plugins. |
| `:test` | `org.clojure/test.check` | EPL-1.0 | Declared `<scope>test</scope>` in the POM. |
| `:repl` | `com.clojure-goes-fast/clj-async-profiler` | EPL-1.0 | Sampling profiler for a REPL session. |

EPL is a weak, file-level copyleft: it binds the EPL'd files themselves and imposes
nothing on a work that merely depends on them. `CONTRIBUTING.md` §7 and
[`../legal/ICLA.md`](../legal/ICLA.md) tell contributors that GPL-family *code* cannot
be combined into an SSPL work — that is about source you write or paste, not about a
build-time tool a profile links, and the jol-core entry above is the reason the
distinction is worth stating.

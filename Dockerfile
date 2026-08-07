# The daemon (`vaelii.impl.serve`) as an image: one JVM owns one KB and serves it
# over HTTP.  Two stages, because Leiningen is a build tool — a runtime image
# carrying it would carry a dependency resolver and a network fetch into
# production, and the uberjar already is the self-contained artifact.

# ---- build ----------------------------------------------------------------
FROM eclipse-temurin:21-jdk AS build

RUN apt-get update \
 && apt-get install -y --no-install-recommends curl ca-certificates \
 && rm -rf /var/lib/apt/lists/*

RUN curl -fsSL https://raw.githubusercontent.com/technomancy/leiningen/stable/bin/lein \
      -o /usr/local/bin/lein \
 && chmod +x /usr/local/bin/lein \
 && lein version

WORKDIR /build

# `project.clj` alone, and resolve against it, so that editing a source file does
# not re-resolve the whole dependency graph on every build.  Everything in
# `:dependencies` comes from Clojars or Maven Central and the uberjar path
# activates no profile, so this layer needs no local artifact and no checkout.
COPY project.clj ./
RUN lein deps

COPY . .
# `:target-path "target/%s"` puts it under the profile's own directory, and the
# name carries the version — glob rather than spell a version that moves.
RUN lein uberjar && mv target/uberjar/*-standalone.jar /build/vaelii.jar

# ---- run ------------------------------------------------------------------
FROM eclipse-temurin:21-jre AS run

# curl is here for HEALTHCHECK below and nothing else.
RUN apt-get update \
 && apt-get install -y --no-install-recommends curl \
 && rm -rf /var/lib/apt/lists/* \
 && useradd --system --create-home --home-dir /var/lib/vaelii \
            --shell /usr/sbin/nologin vaelii

COPY --from=build /build/vaelii.jar /app/vaelii.jar

# The store.  One container per directory: the `:disk` backend takes an exclusive
# file lock on open and a second opener is refused with `:disk-locked`, so
# scaling this service by replica count over one volume is a configuration error
# rather than throughput.
VOLUME /var/lib/vaelii
USER vaelii
EXPOSE 4200

# Unset, the log level installs **no backend at all** — a container that writes
# nothing is one nobody can operate, so the image names a level the operator can
# override rather than inheriting silence.
ENV VAELII_LOG_LEVEL=info

# No `-Xmx`.  A JVM in a container reads the cgroup limit, so the operator's
# `--memory` is the heap ceiling; a baked value would override it and be wrong at
# every size but the one it was written for.
#
# No collector flag either, and that is a measured answer rather than an omission.
# `lein perf` over two alternating passes at a fixed 6 GiB heap: the JDK default
# took 40.7-41.2 s at 1493-1510 MB peak RSS, generational ZGC 55.5-55.9 s at
# 6224-6258 MB — 36% slower holding 4.2x the resident set, and ZGC alone tripped
# the `:negation-arbitration` growth bound on both passes.  A concurrent collector
# earns its throughput cost on a live set of tens of gigabytes, and this engine's
# peak here is 1.5 GB — and in a container the resident set is what the memory limit
# is set against.  `lein with-profile +zgc` selects it for a JVM that has a reason.
#
# `clojure.main -m` rather than `java -jar`: `:gen-class` is on `vaelii.core`, so
# the jar's Main-Class is the API entry point and not this one.
ENTRYPOINT ["java", "-cp", "/app/vaelii.jar", "clojure.main", "-m", "vaelii.impl.serve"]

# `[port [dir]] [--listen ADDR]`.  Binding an address inside the container is what
# lets a published port reach the daemon — and the daemon refuses that bind unless
# `VAELII_API_TOKEN` is set, exiting 2 before it opens the KB.  So an image run
# without a token does not serve unauthenticated; it does not start.
CMD ["4200", "/var/lib/vaelii", "--listen", "0.0.0.0"]

# `/health` is the one route that answers without the token — a daemon only its
# token-holder can probe is one no orchestrator can watch.  The start period is
# generous because a restart over a populated volume runs `recover`, one pass over
# every stored record, before Jetty accepts its first connection.
HEALTHCHECK --interval=30s --timeout=3s --start-period=120s --retries=3 \
  CMD curl -fsS http://127.0.0.1:4200/health || exit 1

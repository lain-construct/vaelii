;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.serve
  "The headless daemon: one process owns one KB and serves it as EDN over HTTP.

  Public because it is a documented entry point — `lein serve`, or
  `lein run -m vaelii.serve 4200 /var/lib/vaelii`.  The implementation is
  `vaelii.impl.serve`, which is free to change.

  It binds loopback, and authenticates with one shared bearer token
  (`VAELII_API_TOKEN`) — required to bind anything else.  Read `.github/SECURITY.md`
  before `--listen` names an address."
  (:require [vaelii.impl.serve :as serve])
  (:import [org.eclipse.jetty.server Server]))

(def ops
  "The reachable operations, keyed by op keyword — the allowlisted `vaelii.core`
  surface a client can drive."
  serve/ops)

(defn app
  "The ring handler for `kb` — pure `request -> response`, so it is tested without a
  socket.  `:host` names the interface it will be served on, which fixes the `Host`
  values it answers to; `:token` is the bearer token every request must present
  (`VAELII_API_TOKEN` when the key is absent, an explicit nil to serve open)."
  ([kb] (serve/app kb))
  ([kb opts] (serve/app kb opts)))

(defn start
  "Start the daemon over `kb` and return the running Jetty server (non-blocking, so the
  caller controls its lifetime).  Opts: `:port` (default 4200; `0` binds an ephemeral
  one, read it back with `port`), `:host` (default loopback) and `:token` (`app`'s)."
  ^Server [kb opts]
  (serve/start kb opts))

(defn port
  "The actual TCP port a started server is listening on."
  ^long [^Server server]
  (serve/port server))

(defn -main
  "Run the daemon in the foreground.  Args: `[port [dir]] [--listen ADDR]` — `dir`
  selects the durable `:disk` backend, and with no `dir` the KB lives only as long as
  the process.  `--listen` with a non-loopback address requires `VAELII_API_TOKEN`;
  without one it is a line on stderr and exit 2."
  [& args]
  (apply serve/-main args))

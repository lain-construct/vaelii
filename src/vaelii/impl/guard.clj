;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.guard
  "The HTTP guards both servers hold to — `vaelii.impl.web` (the browser) and
  `vaelii.impl.serve` (the daemon).

  Neither server authenticates, and both bind loopback for that reason.  Loopback is
  what makes the checks here necessary rather than sufficient: a browser running on
  the same machine *is* a local client, so \"only this machine may reach it\" does not
  mean \"only this machine's owner may drive it\".  Two attacks follow from that, and
  each guard below closes one.

  **Cross-site request forgery.**  Any page the operator visits can `fetch` a loopback
  URL.  `same-origin?` rejects the write whenever the browser stamps `Origin`.
  `edn-body?` closes the case where it does not: `application/edn` is not a
  CORS-*simple* content type, so a browser must preflight it, and a server answering
  no CORS headers fails that preflight before the request is ever sent.

  **DNS rebinding.**  `same-origin?` compares `Origin` against the request's own
  `Host`, so an attacker controlling both — a domain that re-resolves to 127.0.0.1
  once the page is loaded — satisfies it.  `host-allowed?` is the check that does not
  fold, because the `Host` header must then name the interface the server was actually
  started on."
  (:require [clojure.string :as str]))

(def loopback-hosts
  "The `Host` values that name this machine.  Both bracketed and bare IPv6 spellings,
  since a client picks either."
  #{"localhost" "127.0.0.1" "[::1]" "::1"
    "0:0:0:0:0:0:0:1" "[0:0:0:0:0:0:0:1]"})

(defn- strip-port
  "The host part of a `Host` header value.  An IPv6 literal is bracketed when it
  carries a port (RFC 3986), so the bracket — not the last colon — is what delimits
  it; a bare `::1` has no port to strip at all."
  [^String h]
  (cond
    (str/starts-with? h "[") (if-let [c (str/index-of h "]")] (subs h 0 (inc c)) h)
    (> (count (re-seq #":" h)) 1) h
    :else (if-let [c (str/index-of h ":")] (subs h 0 c) h)))

(defn allowed-hosts
  "The allowlist for a server bound to `bound-host`.

  `VAELII_ALLOWED_HOSTS` (comma-separated) overrides everything.  Otherwise a
  loopback bind — the default — answers only to loopback names, which is what closes
  rebinding.  A bind that named an address is already an explicit choice made against
  a documented warning, and the operator reaches it under a name only they know, so
  it is left open rather than guessed at."
  [bound-host]
  (let [env (System/getenv "VAELII_ALLOWED_HOSTS")]
    (cond
      (seq env)
      (into #{} (comp (map str/trim) (remove str/blank?) (map str/lower-case))
            (str/split env #","))

      (contains? loopback-hosts (str/lower-case (str bound-host)))
      loopback-hosts

      :else ::any)))

(defn host-allowed?
  "Does this request's `Host` name an interface `allowed` covers?

  A request carrying **no** `Host` is allowed: HTTP/1.1 requires the header and every
  browser sends it, so its absence marks a non-browser client (curl, a test's request
  map) — which has no ambient browser context to ride, and is not the request
  rebinding is about.  Same carve-out `same-origin?` makes, for the same reason."
  [allowed req]
  (or (= allowed ::any)
      (if-let [h (get-in req [:headers "host"])]
        (contains? allowed (str/lower-case (strip-port (str/trim h))))
        true)))

(defn url-origin
  "The `scheme://authority` a URL names, or `::opaque` when it names none — a
  sandboxed frame sends `Origin: null`, which is a real origin claim that matches
  nothing and must not be read as \"no header\"."
  [url]
  (or (try (let [u (java.net.URI. (str url))]
             (when (and (.getScheme u) (.getAuthority u))
               (str (.getScheme u) "://" (.getAuthority u))))
           (catch Exception _ nil))
      ::opaque))

(defn same-origin?
  "Does this request come from the browser's own copy of this site?  A write route
  with no session to authenticate has to ask **who asked**: a browser stamps `Origin`
  (falling back to `Referer`) on a form or fetch POST and a page on another site
  cannot forge it, so comparing it to the request's own `Host` rejects a cross-site
  write while leaving the browser's own pages alone.

  A request carrying **neither** header is same-origin by default: that is a
  non-browser client, which has no ambient browser context for another site to ride.
  It is `host-allowed?` that keeps this from being the whole story — on its own this
  check folds under DNS rebinding, where both headers are the attacker's."
  [req]
  (if-let [claimed (some #(get-in req [:headers %]) ["origin" "referer"])]
    (= (url-origin claimed)
       (when-let [host (get-in req [:headers "host"])]
         (str (name (:scheme req :http)) "://" host)))
    true))

(defn edn-body?
  "Is this request's body declared `application/edn`?

  The daemon requires it, and the requirement is a CSRF guard rather than a parsing
  one: the three content types a cross-site `fetch` may set without a preflight are
  `text/plain`, `application/x-www-form-urlencoded` and `multipart/form-data`, so
  demanding anything else forces a preflight the daemon cannot answer."
  [req]
  (-> (get-in req [:headers "content-type"] "")
      str/trim
      str/lower-case
      (str/starts-with? "application/edn")))

(defn wrap-host-allowed
  "Wrap `handler` so a request whose `Host` falls outside `allowed` gets `refusal`
  instead.  Applied to the whole server rather than to its write routes: a rebound
  page reads as well as it writes, and the KB is what it came for."
  [handler allowed refusal]
  (fn [req]
    (if (host-allowed? allowed req)
      (handler req)
      (refusal req))))

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

;; ---- the request-body ceiling -------------------------------------------

(def max-body-bytes
  "The cap on a request body, `VAELII_MAX_BODY_BYTES` or 16 MiB.

  Neither server authenticates, so an unbounded body is heap an anonymous caller can
  spend by streaming one — and the legitimate bodies are tiny either side: the daemon's
  is a sentence and its context, the browser's is a form.  **One constant and one
  variable for both**, because two servers with two ceilings is one of them wrong, and
  an operator who lowers the limit means the machine rather than a route.

  A value that is not a positive integer is **refused at load**, naming itself.  This
  namespace is read by both servers, so a silent fallback would leave an operator who
  meant `16m` believing a cap they never set — and a raw `NumberFormatException` out of
  a `def` reports as a namespace that would not load rather than as the typo it is."
  (if-let [raw (System/getenv "VAELII_MAX_BODY_BYTES")]
    (let [n (try (Long/parseLong (str/trim raw))
                 (catch NumberFormatException _
                   (throw (ex-info (str "VAELII_MAX_BODY_BYTES is not a number: "
                                        (pr-str raw) " — want a byte count")
                                   {:type :unknown-option :value raw}))))]
      (when-not (pos? n)
        (throw (ex-info (str "VAELII_MAX_BODY_BYTES must be positive, got " n
                             " — a zero or negative ceiling refuses every request")
                        {:type :unknown-option :value raw})))
      n)
    (* 16 1024 1024)))

(defn- too-large!
  "The one refusal both servers' 413s are built from, so the wire `:type` is the same
  whichever answered."
  []
  (throw (ex-info (str "request body exceeds " max-body-bytes " bytes")
                  {:type :body-too-large :limit max-body-bytes})))

(defn read-capped-body-bytes
  "`req`'s body as a byte array, refusing past `max-body-bytes`.  `slurp` — and ring's
  own params middleware — read an unbounded body into the heap before anything gets to
  look at it, which is the whole of what this replaces."
  ^bytes [req]
  (if-let [^java.io.InputStream in (:body req)]
    (let [out   (java.io.ByteArrayOutputStream.)
          chunk (byte-array 8192)]
      (loop []
        (let [n (.read in chunk)]
          (when (pos? n)
            (when (> (+ (.size out) n) max-body-bytes) (too-large!))
            (.write out chunk 0 n)
            (recur))))
      (.toByteArray out))
    (byte-array 0)))

(defn read-capped-body
  "`req`'s body as a UTF-8 string, refusing past `max-body-bytes`."
  ^String [req]
  (String. (read-capped-body-bytes req) java.nio.charset.StandardCharsets/UTF_8))

(defn wrap-body-limit
  "Wrap `handler` so a request body past `max-body-bytes` gets `refusal` (a fn of the
  request) instead — the 413.

  For a server that does **not** read its own bodies.  The browser reads its forms
  through ring's params middleware, which slurps the body itself and has no ceiling, so
  the cap has to be applied outside it; the buffered copy this leaves on `:body` is what
  that middleware then reads.  The daemon reads its own body and calls
  `read-capped-body` directly."
  [handler refusal]
  (fn [req]
    (let [body (try (read-capped-body-bytes req)
                    (catch clojure.lang.ExceptionInfo e
                      (if (= :body-too-large (:type (ex-data e)))
                        ::over
                        (throw e))))]
      (if (= ::over body)
        (refusal req)
        (handler (assoc req :body (java.io.ByteArrayInputStream. ^bytes body)))))))

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.guard-test
  "The HTTP guards (`vaelii.impl.guard`) as pure functions — no KB, no socket.

  These pin the refusal paths of the `Host` allowlist that closes DNS rebinding, and
  the pieces it is built from.  The daemon- and browser-level tests
  (`vaelii.serve-test`, `vaelii.web-test`) drive the wrapped handlers; this namespace
  pins the guard's own decisions, including the deliberate carve-outs a handler test
  could mistake for gaps."
  (:require [clojure.test :refer [deftest is testing]]
            [vaelii.impl.guard :as guard]))

(def ^:private strip-port #'guard/strip-port)

;; ---- strip-port ----------------------------------------------------------

(deftest strip-port-reads-the-host-part
  (testing "a plain host:port loses the port"
    (is (= "localhost" (strip-port "localhost:3000")))
    (is (= "127.0.0.1" (strip-port "127.0.0.1:4200")))
    (is (= "evil.example.com" (strip-port "evil.example.com:3000"))))
  (testing "no port, nothing stripped"
    (is (= "localhost" (strip-port "localhost")))
    (is (= "127.0.0.1" (strip-port "127.0.0.1"))))
  (testing "a bracketed IPv6 literal keeps its brackets and loses the port"
    (is (= "[::1]" (strip-port "[::1]:3000")))
    (is (= "[::1]" (strip-port "[::1]"))))
  (testing "a bare IPv6 literal has no port to strip — the colons are the address"
    (is (= "::1" (strip-port "::1")))
    (is (= "0:0:0:0:0:0:0:1" (strip-port "0:0:0:0:0:0:0:1"))))
  (testing "an unclosed bracket is left whole, so the allowlist lookup fails closed"
    (is (= "[::1" (strip-port "[::1")))))

;; ---- allowed-hosts -------------------------------------------------------

(deftest allowed-hosts-follows-the-bind
  ;; `VAELII_ALLOWED_HOSTS` overrides both branches, and `System/getenv` is a static
  ;; call with no var to fake — so this asserts the default branches, and skips when
  ;; the environment carries the override (under it, the defaults are genuinely not
  ;; in force).  The override's *consumption* is pinned below through `host-allowed?`,
  ;; which takes the set as a value.
  (if (some? (System/getenv "VAELII_ALLOWED_HOSTS"))
    (println "SKIP vaelii.guard-test/allowed-hosts-follows-the-bind:"
             "VAELII_ALLOWED_HOSTS is set in this environment")
    (do
      (testing "a loopback bind answers only to loopback spellings"
        (is (= guard/loopback-hosts (guard/allowed-hosts "127.0.0.1")))
        (is (= guard/loopback-hosts (guard/allowed-hosts "localhost")))
        (is (= guard/loopback-hosts (guard/allowed-hosts "::1")))
        (is (= guard/loopback-hosts (guard/allowed-hosts "[::1]"))))
      (testing "the bind's own case does not matter"
        (is (= guard/loopback-hosts (guard/allowed-hosts "LocalHost"))))
      (testing "a non-loopback bind is an explicit operator choice and is left open"
        (is (= ::guard/any (guard/allowed-hosts "0.0.0.0")))
        (is (= ::guard/any (guard/allowed-hosts "192.168.1.5")))))))

;; ---- host-allowed? -------------------------------------------------------

(deftest host-allowed-refuses-a-rebound-name-on-a-loopback-bind
  (let [allowed guard/loopback-hosts               ; what a loopback bind yields
        req     (fn [host] {:headers {"host" host}})]
    (testing "a name that re-resolved to 127.0.0.1 is exactly what is refused"
      (is (not (guard/host-allowed? allowed (req "evil.example.com"))))
      (is (not (guard/host-allowed? allowed (req "evil.example.com:3000")))))
    (testing "an unknown name fails closed — the set says what is allowed, not what is blocked"
      (is (not (guard/host-allowed? allowed (req "kb.internal")))))
    (testing "every loopback spelling passes, with or without a port"
      (is (guard/host-allowed? allowed (req "localhost")))
      (is (guard/host-allowed? allowed (req "localhost:3000")))
      (is (guard/host-allowed? allowed (req "127.0.0.1:4200")))
      (is (guard/host-allowed? allowed (req "[::1]:3000")))
      (is (guard/host-allowed? allowed (req "::1"))))
    (testing "matching is case-insensitive and whitespace-tolerant, as header values are"
      (is (guard/host-allowed? allowed (req "LOCALHOST:3000")))
      (is (guard/host-allowed? allowed (req " localhost "))))))

(deftest a-request-with-no-host-is-allowed-by-design
  ;; the deliberate carve-out: HTTP/1.1 requires `Host` and every browser sends it,
  ;; so its absence marks a non-browser client (curl, a test's request map) — which
  ;; has no ambient browser context to ride, and is not the request rebinding is
  ;; about.  Pinned so any future tightening is a visible choice, not drift.
  (is (guard/host-allowed? guard/loopback-hosts {}))
  (is (guard/host-allowed? guard/loopback-hosts {:headers {}})))

(deftest an-any-allowlist-is-the-open-door-it-says-it-is
  ;; the non-loopback-bind branch: an operator who bound an address reaches the
  ;; server under a name only they know, so nothing is guessed at
  (is (guard/host-allowed? ::guard/any {:headers {"host" "evil.example.com"}})))

(deftest an-override-allowlist-is-consumed-verbatim
  ;; the set `VAELII_ALLOWED_HOSTS=kb.example.com` produces (`allowed-hosts`
  ;; lower-cases each entry), driven through the check that reads it
  (let [allowed #{"kb.example.com"}]
    (is (guard/host-allowed? allowed {:headers {"host" "kb.example.com:4200"}}))
    (is (guard/host-allowed? allowed {:headers {"host" "KB.Example.COM"}}))
    (is (not (guard/host-allowed? allowed {:headers {"host" "localhost"}}))
        "an override replaces the loopback set rather than adding to it")))

;; ---- wrap-host-allowed ---------------------------------------------------

(deftest wrap-host-allowed-refuses-before-the-handler-runs
  (let [ran     (atom 0)
        handler (fn [_] (swap! ran inc) {:status 200 :body "ok"})
        refusal (fn [_] {:status 400 :body "no"})
        wrapped (guard/wrap-host-allowed handler guard/loopback-hosts refusal)]
    (testing "a bad host gets the refusal and the wrapped handler never runs"
      (is (= 400 (:status (wrapped {:headers {"host" "evil.example.com"}}))))
      (is (zero? @ran)))
    (testing "a good host reaches the handler"
      (is (= 200 (:status (wrapped {:headers {"host" "localhost:3000"}}))))
      (is (= 1 @ran)))))

;; ---- edn-body? -----------------------------------------------------------

(deftest edn-body-prefix-matches-the-declared-type
  ;; the CSRF gate's own decision, at the pure level; the daemon-level consequences
  ;; (415, no side effect) are `vaelii.serve-test`'s
  (let [req (fn [ct] {:headers {"content-type" ct}})]
    (testing "parameters and case variants still declare EDN"
      (is (guard/edn-body? (req "application/edn")))
      (is (guard/edn-body? (req "application/edn; charset=utf-8")))
      (is (guard/edn-body? (req "Application/EDN")))
      (is (guard/edn-body? (req "  application/edn  "))))
    (testing "the three CORS-simple types — what a cross-site fetch can send without a
              preflight — are exactly what is refused"
      (is (not (guard/edn-body? (req "text/plain"))))
      (is (not (guard/edn-body? (req "application/x-www-form-urlencoded"))))
      (is (not (guard/edn-body? (req "multipart/form-data")))))
    (testing "no declaration at all is refused too"
      (is (not (guard/edn-body? {})))
      (is (not (guard/edn-body? {:headers {}}))))))

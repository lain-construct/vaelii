;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.serve-test
  "The operational surface: the EDN-over-HTTP daemon (`vaelii.impl.serve`) and its
  client (`vaelii.impl.client`).

  Two levels.  The handler is pure `request -> response`, so `app` is exercised
  without a socket — the fast, deterministic check that ops dispatch, results are
  EDN-clean, and bad input is refused.  Then one full loop starts jetty on an
  ephemeral port and drives it with the real client, proving the wire round-trips
  end to end: sentences out as symbol s-expressions, sentex records back as plain
  maps."
  (:require [clojure.edn :as edn]
            [clojure.set :as set]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.catalog :as catalog]
            [vaelii.impl.client :as client]
            [vaelii.impl.guard :as guard]
            [vaelii.impl.serve :as serve]
            [vaelii.test-util :as tu])
  (:import [java.io ByteArrayInputStream File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]
           [org.eclipse.jetty.server Server ServerConnector]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- post-op*
  "Call `handler` (from `serve/app`) with a POST /op carrying `{:op :args}` under
  exactly `headers`, and return the parsed EDN reply — no socket.  What `post-op`
  always sends, this lets a test withhold or misspell, which is how the guards'
  refusal paths are driven."
  [handler headers op args]
  (let [body (pr-str {:op op :args (vec args)})
        resp (handler {:request-method :post :uri "/op"
                       :headers headers
                       :body (ByteArrayInputStream. (.getBytes ^String body "UTF-8"))})]
    (assoc (edn/read-string (:body resp)) :status (:status resp))))

(defn- post-op
  "`post-op*` with the headers a real client sends.

  The `content-type` is not decoration: `guard/edn-body?` refuses the write route
  without it, which is the CSRF guard rather than a parsing one (a cross-site `fetch`
  cannot set this type without a preflight the daemon will not answer).  A real client
  sends it, so the helper that stands in for one has to as well.  `Origin`/`Referer` are
  deliberately absent — `guard/same-origin?` treats a request carrying neither as
  same-origin, which is what a non-browser client is."
  [handler op args]
  (post-op* handler {"content-type" "application/edn"} op args))

;; ---- the handler, no socket ---------------------------------------------

(tu/deftest-kb app-dispatches-ops-and-refuses-bad-input
  (tu/with-terms [dog animal Fido ServeContext]
    (let [handler (serve/app kb)]
      (testing "an assert op stores and returns the handle"
        (let [r (post-op handler :assert [(list dog Fido) ServeContext {:strength :monotonic}])]
          (is (:ok r))
          (is (nat-int? (:result r)))))
      (testing "a query op returns sentex maps — plain, not records"
        (let [r (post-op handler :sentexes-matching [(list dog '?x) ServeContext])]
          (is (:ok r))
          (let [sx (first (:result r))]
            (is (map? sx))
            (is (not (record? sx)) "a record must be projected to a plain map on the wire")
            (is (= (list dog Fido) (:sentence sx))))))
      (testing "an ask op returns binding maps"
        (v/assert kb (list 'genl dog animal) ServeContext)
        (let [r (post-op handler :ask [(list animal '?x) ServeContext])]
          (is (:ok r))
          (is (some #(= Fido (get % '?x)) (:result r))
              "specificity: (dog Fido) answers the (animal ?x) goal")))
      (testing "why returns a proof-tree map"
        (let [h (v/handle-of kb (list dog Fido) ServeContext)
              r (post-op handler :why [h])]
          (is (:ok r))
          (is (map? (:result r)))
          (is (= (list dog Fido) (:sentence (:result r))))))
      (testing "preview answers what a batch would believe, and stores nothing"
        ;; served with the writes because it applies the batch and rolls it back — the
        ;; daemon is the single writer, which is exactly the condition it needs
        (tu/with-terms [swims Willy]
          (let [before (tu/sentex-ids kb)
                r (post-op handler :preview
                           [{:add [[(list swims Willy) ServeContext]]}])]
            (is (:ok r))
            (is (= [(list swims Willy)]
                   (mapv :sentence (:believed-added (:result r))))
                "the answer crosses the wire as sentences, not records")
            (is (= before (tu/sentex-ids kb))
                "a preview over the wire stored something")
            (is (nil? (v/handle-of kb (list swims Willy) ServeContext))))))
      (testing "an unknown op is a 400 that lists the real ops"
        (let [r (post-op handler :not-an-op [])]
          (is (false? (:ok r)))
          (is (= 400 (:status r)))
          (is (some #{:assert} (:ops r)))))
      (testing "a refusal (a non-ground fact) comes back as an error, not a crash"
        (let [r (post-op handler :assert [(list dog '?x) ServeContext])]
          (is (false? (:ok r)))
          (is (= :not-ground (:type r)) "the ex-data :type rides the wire"))))))

;; ---- the guards' refusal paths -------------------------------------------

(tu/deftest-kb post-op-refuses-a-cors-simple-content-type
  ;; the CSRF gate: `application/edn` is not a CORS-*simple* type, so a browser must
  ;; preflight it and this daemon answers no preflight — demanding it is what keeps a
  ;; page the operator merely visits from driving the write route
  (tu/with-terms [dog Fido ServeContext]
    (let [handler (serve/app kb)
          before  (tu/sentex-ids kb)
          refused (fn [headers]
                    (post-op* handler headers :assert [(list dog Fido) ServeContext]))]
      (testing "no content-type at all is a 415 in the daemon's structured error shape"
        (let [r (refused {})]
          (is (= 415 (:status r)))
          (is (false? (:ok r)))
          (is (= :not-edn (:type r)) "the ex-data :type rides the wire")
          (is (string? (:error r)))))
      (testing "the three types a cross-site fetch may send without a preflight are refused"
        (doseq [ct ["text/plain"
                    "application/x-www-form-urlencoded"
                    "multipart/form-data"]]
          (let [r (refused {"content-type" ct})]
            (is (= 415 (:status r)) ct)
            (is (= :not-edn (:type r)) ct))))
      (testing "and the refusal runs nothing — the op is never executed"
        (is (= before (tu/sentex-ids kb)))
        (is (nil? (v/handle-of kb (list dog Fido) ServeContext)))))))

(tu/deftest-kb post-op-refuses-a-cross-origin-caller
  ;; the other CSRF gate, and the one that bites when a browser *does* stamp an origin:
  ;; `edn-body?` forces a preflight this daemon will not answer, and this refuses the
  ;; page that got one anyway.  A `:type` on the wire because a client discriminating on
  ;; the message string is discriminating on prose.
  (tu/with-terms [dog Fido ServeContext]
    (let [handler (serve/app kb)
          before  (tu/sentex-ids kb)
          from    (fn [hdrs]
                    (post-op* handler (merge {"content-type" "application/edn"} hdrs)
                              :assert [(list dog Fido) ServeContext]))]
      (doseq [[label hdrs] [["another site" {"host" "localhost:4200"
                                             "origin" "http://evil.example"}]
                            ;; a sandboxed frame sends `Origin: null` — an origin claim
                            ;; matching nothing, not an absent header
                            ["an opaque origin" {"host" "localhost:4200" "origin" "null"}]
                            ["a cross-site referer" {"host" "localhost:4200"
                                                     "referer" "http://evil.example/x"}]]]
        (let [r (from hdrs)]
          (is (= 403 (:status r)) label)
          (is (false? (:ok r)) label)
          (is (= :cross-origin (:type r)) label)))
      (testing "the daemon's own page still writes, so the refusal is the origin's doing"
        (let [r (from {"host" "localhost:4200" "origin" "http://localhost:4200"})]
          (is (= 200 (:status r)))
          (is (:ok r))))
      (testing "and the three refusals ran nothing — only the same-origin write landed"
        (is (= 1 (count (set/difference (tu/sentex-ids kb) before))))))))

(tu/deftest-kb post-op-accepts-edn-however-legally-spelled
  ;; `guard/edn-body?` trims, lower-cases and prefix-matches, so a parameterized or
  ;; case-varied header is still the declaration the gate requires
  (tu/with-terms [dog Fido ServeContext]
    (let [handler (serve/app kb)]
      (doseq [ct ["application/edn; charset=utf-8"
                  "Application/EDN"
                  "APPLICATION/EDN; CHARSET=UTF-8"
                  "  application/edn  "]]
        (let [r (post-op* handler {"content-type" ct} :assert
                          [(list dog Fido) ServeContext])]
          (is (= 200 (:status r)) ct)
          (is (:ok r) ct)))
      (is (some? (v/handle-of kb (list dog Fido) ServeContext))
          "the accepted spelling reached the op — the fact is stored"))))

(tu/deftest-kb the-daemon-refuses-a-rebound-host-on-every-route
  ;; the DNS-rebinding gate: `same-origin?` folds when the attacker controls both
  ;; `Origin` and `Host` (a domain re-resolving to 127.0.0.1), so `host-allowed?` is
  ;; the check that has to hold — and it wraps the whole server, because a rebound
  ;; page reads the KB as happily as it writes to it
  (tu/with-terms [dog Fido ServeContext]
    (let [handler (serve/app kb)
          before  (tu/sentex-ids kb)]
      (testing "a write op under a rebound Host is a 400 before anything runs"
        (let [r (post-op* handler {"content-type" "application/edn"
                                   "host"   "evil.example.com"
                                   "origin" "http://evil.example.com"}
                          :assert [(list dog Fido) ServeContext])]
          (is (= 400 (:status r)))
          (is (false? (:ok r)))
          (is (= :bad-host (:type r)))
          (is (= before (tu/sentex-ids kb)) "the refused op stored nothing")
          (is (nil? (v/handle-of kb (list dog Fido) ServeContext)))))
      (testing "a read route is refused too — the KB is what a rebound page came for"
        (let [r (handler {:request-method :get :uri "/health"
                          :headers {"host" "evil.example.com:4200"}})]
          (is (= 400 (:status r)))
          (is (= :bad-host (:type (edn/read-string (:body r)))))))
      (testing "the daemon's own names still pass, with or without a port"
        (doseq [h ["localhost:4200" "127.0.0.1:4200" "[::1]:4200" "localhost"]]
          (let [r (handler {:request-method :get :uri "/health" :headers {"host" h}})]
            (is (= 200 (:status r)) h))))
      (testing "a write under the daemon's own Host still lands"
        (let [r (post-op* handler {"content-type" "application/edn"
                                   "host" "127.0.0.1:4200"}
                          :assert [(list dog Fido) ServeContext])]
          (is (:ok r))
          (is (nat-int? (:result r)))))
      (testing "and a Host-less request (curl, every other test here) passes by design"
        (is (= 200 (:status (handler {:request-method :get :uri "/health"}))))))))

(tu/deftest-kb export-over-the-wire-writes-on-the-daemons-own-host
  (tu/with-terms [dog Fido ServeContext]
    (let [handler (serve/app kb)
          root (.toFile (Files/createTempDirectory "vaelii-serve-export-"
                                                   (into-array FileAttribute [])))
          dump (java.io.File. root "a-dump")]
      (try
        (v/assert kb (list dog Fido) ServeContext)
        (testing "the op answers with the writer's summary — every value already EDN, so
                  nothing about it needs the sentex-map projection"
          (let [r (post-op handler :export [(.getPath dump) {:compression :none}])]
            (is (:ok r))
            (is (= (v/sentex-count kb) (:sentexes (:result r))))
            (is (= (.getAbsolutePath dump) (:dir (:result r))))))
        (testing "and the directory it names is one on this host — the daemon's — which is
                  the only place it could be: there is no stream to hand a client back"
          (is (= :dump (catalog/classify dump))))
        (testing "a refusal crosses the wire as the writer's own message"
          (let [r (post-op handler :export [(.getPath dump) {}])]
            (is (false? (:ok r)))
            (is (re-find #"is not empty" (:error r)))
            (is (= :not-empty (:type r)))))
        (finally (doseq [^File f (reverse (file-seq root))] (.delete f)))))))

;; ---- the body ceiling ----------------------------------------------------
;;
;; `POST /op` is unauthenticated, so the caller who can reach it is the caller who can
;; spend the daemon's heap by streaming a body at it.  The reading half — that the
;; refusal happens *while* reading rather than after — is `vaelii.guard-test`, where the
;; ceiling lives; what belongs here is that the refusal reaches the wire as a 413 in the
;; daemon's own error shape, and that no op ran behind it.

(tu/deftest-kb an-oversized-post-is-a-413-that-runs-no-op
  (tu/with-terms [dog Fido ServeContext]
    (let [handler (serve/app kb)
          before  (tu/sentex-ids kb)
          body    (.getBytes ^String (pr-str {:op :assert
                                              :args [(list dog Fido) ServeContext]})
                             "UTF-8")
          resp    (with-redefs [guard/max-body-bytes 8]
                    (handler {:request-method :post :uri "/op"
                              :headers {"content-type" "application/edn"}
                              :body (ByteArrayInputStream. body)}))
          r       (edn/read-string (:body resp))]
      (is (= 413 (:status resp)))
      (is (false? (:ok r)))
      (is (= :body-too-large (:type r)) "the ex-data :type rides the wire")
      (is (re-find #"exceeds" (:error r)))
      (testing "and the op never ran — the refusal is before the dispatch, not after"
        (is (= before (tu/sentex-ids kb)))
        (is (nil? (v/handle-of kb (list dog Fido) ServeContext))))
      (testing "the same call under the shipped ceiling lands, so the 413 above is the
                ceiling's doing and not the request's"
        (let [r2 (edn/read-string
                  (:body (handler {:request-method :post :uri "/op"
                                   :headers {"content-type" "application/edn"}
                                   :body (ByteArrayInputStream. body)})))]
          (is (:ok r2))
          (is (nat-int? (:result r2))))))))

;; ---- what it binds -------------------------------------------------------

(tu/deftest-kb the-daemon-binds-loopback-unless-told-otherwise
  ;; `POST /op` is the write route of the **single writer** and nothing authenticates
  ;; it, so the default has to answer only this machine — the same rule the browser
  ;; holds to, and the more consequential of the two.  Jetty binds every interface when
  ;; no host is given, so "we passed no host" is precisely the bug: this reads the
  ;; connector rather than the options, because the options are what was wrong.
  (let [bound-host (fn [opts]
                     (let [^Server server (serve/start kb opts)]
                       (try
                         (.getHost ^ServerConnector (first (.getConnectors server)))
                         (finally (.stop server)))))]
    (is (= "127.0.0.1" (bound-host {:port 0}))
        "the daemon bound every interface — with no host given, jetty does, and POST /op
         is then an unauthenticated write route reachable off-machine")
    (testing "and an explicit address is still honoured"
      (is (= "127.0.0.1" (bound-host {:port 0 :host "127.0.0.1"}))))))

;; ---- the full wire loop --------------------------------------------------

(tu/deftest-kb client-round-trips-through-the-daemon
  (tu/with-terms [bird flies penguin Tweety WireContext]
    (let [server (serve/start kb {:port 0})]
      (try
        (let [conn (client/client "localhost" (serve/port server))]
          (testing "health"
            (is (:ok (client/health conn))))
          (testing "assert / query round-trip over the socket"
            (is (nat-int? (client/assert! conn (list bird Tweety) WireContext)))
            (let [rs (client/sentexes-matching conn (list bird '?x) WireContext)]
              (is (= (list bird Tweety) (:sentence (first rs))))))
          (testing "a forward rule fires server-side and the derived fact is asked back"
            (client/assert-rule! conn [(list bird '?b)] (list flies '?b) WireContext)
            (is (client/ask? conn (list flies Tweety) WireContext)))
          (testing "why over the wire returns a proof tree"
            (let [h (client/handle-of conn (list flies Tweety) WireContext)]
              (is (map? (client/why conn h)))))
          (testing "a remote refusal surfaces as an ex-info carrying the daemon error"
            (is (thrown? clojure.lang.ExceptionInfo
                         (client/assert! conn (list bird '?anything) WireContext))))
          (testing "retract over the wire tears the fact down"
            (let [h (client/handle-of conn (list bird Tweety) WireContext)]
              (client/retract! conn h)
              (is (empty? (client/sentexes-matching conn (list bird Tweety) WireContext))))))
        (finally
          (.stop server))))))

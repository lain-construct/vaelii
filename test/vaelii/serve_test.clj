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
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.catalog :as catalog]
            [vaelii.impl.client :as client]
            [vaelii.impl.serve :as serve]
            [vaelii.test-util :as tu])
  (:import [java.io ByteArrayInputStream File]
           [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]
           [org.eclipse.jetty.server Server ServerConnector]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- post-op
  "Call `handler` (from `serve/app`) with a POST /op carrying `{:op :args}`, and return
  the parsed EDN reply — no socket."
  [handler op args]
  (let [body (pr-str {:op op :args (vec args)})
        resp (handler {:request-method :post :uri "/op"
                       :body (ByteArrayInputStream. (.getBytes ^String body "UTF-8"))})]
    (assoc (edn/read-string (:body resp)) :status (:status resp))))

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
        "the daemon is reachable off-machine by default")
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

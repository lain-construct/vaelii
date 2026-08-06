;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.wire-contract-test
  "The daemon's wire contract, pinned pair by pair: every refusal `POST /op` can
  answer is a status code *and* a plain `:type` keyword, the two halves
  `docs/operations.md` promises together.  Driven against `serve/app` directly —
  the handler is pure `request -> response`, so no socket — with one property over
  the lot: `:ok` is false and `:type` is a non-nil keyword, whichever door refused."
  (:require [clojure.edn :as edn]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.impl.guard :as guard]
            [vaelii.impl.serve :as serve]
            [vaelii.test-util :as tu])
  (:import [java.io ByteArrayInputStream]))

(use-fixtures :each (tu/neutral-fresh tu/fresh))

(defn- post-raw
  "POST the exact `body` string to /op under `headers` and return the parsed EDN
  reply with `:status` assoc'd — raw, so an unreadable body is drivable at all."
  ([handler headers body] (post-raw handler headers body "/op"))
  ([handler headers ^String body uri]
   (let [resp (handler {:request-method :post :uri uri
                        :headers headers
                        :body (ByteArrayInputStream. (.getBytes body "UTF-8"))})]
     (assoc (edn/read-string (:body resp)) :status (:status resp)))))

(def ^:private edn-headers {"content-type" "application/edn"})

(defn- op-body [op args] (pr-str {:op op :args (vec args)}))

(tu/deftest-kb every-wire-refusal-is-a-status-and-a-type
  (tu/with-terms [dog Rex WireProbeContext]
    (let [handler (serve/app kb)
          oversized (with-redefs [guard/max-body-bytes 8]
                      (post-raw handler edn-headers
                                (op-body :assert [(list dog Rex) WireProbeContext])))
          pinned
          [["a wrong content-type" 415 :not-edn
            (post-raw handler {"content-type" "text/plain"}
                      (op-body :assert [(list dog Rex) WireProbeContext]))]
           ["a body that does not read as EDN" 400 :not-edn
            (post-raw handler edn-headers "{:op :assert :args [(dog")]
           ["an op the allowlist does not name" 400 :unknown-op
            (post-raw handler edn-headers (op-body :not-an-op []))]
           ["the wrong number of args for the op" 400 :bad-args
            (post-raw handler edn-headers (op-body :assert []))]
           ["a non-sequential :args" 400 :bad-args
            (post-raw handler edn-headers (pr-str {:op :assert :args 5}))]
           ["a body over the ceiling" 413 :body-too-large
            oversized]]
          ;; the engine's own refusal rides the wire under the engine's `:type`, and a
          ;; request-refusal is the *caller's* fault, so it is a 400 like the daemon's
          ;; own — answered 500 it counts as a backend fault at every reverse proxy
          ;; and 5xx alarm between the caller and the daemon
          engine (post-raw handler edn-headers
                           (op-body :assert [(list dog '?x) WireProbeContext]))]
      (doseq [[label status type reply] pinned]
        (testing label
          (is (= status (:status reply)) label)
          (is (= type (:type reply)) label)))
      (testing "an engine refusal keeps the engine's :type on the wire, at 400"
        (is (= :not-ground (:type engine)))
        (is (= 400 (:status engine))))
      (testing "the refusal-vocabulary statuses: naming, options, handles, levels"
        (doseq [[label args ty] [["snake_case arity 2" [(list 'lives_in Rex 'cold_place) WireProbeContext] :naming]
                                 ["an unread option" [(list dog Rex) WireProbeContext {:strenth :monotonic}] :unknown-option]]]
          (let [r (post-raw handler edn-headers (op-body :assert args))]
            (is (= 400 (:status r)) label)
            (is (= ty (:type r)) label))))
      (testing "a route nothing serves is a typed reply too"
        (let [r (post-raw handler edn-headers "{:op :assert}" "/nothing-here")]
          ;; any client, any body: the default handler answers 404 with a :type
          (is (= 404 (:status r)))
          (is (= :not-found (:type r)))))
      (testing "the property over every refusal: :ok false, :type a non-nil keyword"
        (doseq [[label _ _ reply] (conj pinned ["an engine refusal" nil nil engine])]
          (is (false? (:ok reply)) label)
          (is (keyword? (:type reply)) label))))))

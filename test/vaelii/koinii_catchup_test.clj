;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.koinii-catchup-test
  "Koinii catch-up: CDC snapshot+tail over the wire feed.  An agent that fell
  behind must reach the state it WOULD have reached had it never disconnected — the failure
  mode is silent loss, so these assert completeness, not just liveness.  Three cases, each
  on its own daemon (a fresh KB per test, so one test's queries never leak into another's
  cone-aware snapshot):

  - resume from a stored cursor while still in the ring — tail, no snapshot;
  - overflow past the ring — lag detected, snapshot recovers the full state;
  - re-read and replay converge — a tailing agent and a snapshotting agent reach the same
    view over the same window.

  Wire-only: the ring / cursor / lag exist on the wire feed, so this needs a daemon."
  (:require [clojure.test :refer [is testing use-fixtures]]
            [vaelii.client :as vc]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.koinii.catchup :as cu]
            [vaelii.impl.koinii.channel :as ch]
            [vaelii.impl.koinii.speech-acts :as sa]
            [vaelii.impl.serve :as serve]
            [vaelii.impl.subscribe :as sub]
            [vaelii.test-util :as tu])
  (:import [org.eclipse.jetty.server Server]))

(defn- household-kb []
  (doto (tu/fresh) (core-context/load-into) (sa/load-speech-acts)))

(use-fixtures :each (tu/neutral-fresh household-kb))

(def ^:private goal (list 'queries '?a '?q))

(defn- q [question] (list 'queries 'AgentAva question))

(defn- with-daemon
  "Run `f` with a fresh daemon over `kb`; `f` gets a 0-arg `conn` factory (each call a new
  connection) and a `wire` factory (each call a fresh agent handle on CxDeploy)."
  [kb f]
  (let [^Server server (serve/start kb {:port 0 :token nil})
        port (serve/port server)
        conn #(vc/client "localhost" port {:token nil :timeout-ms 5000})
        wire #(ch/join (ch/wire (conn)) 'CxDeploy %)]
    (try (f conn wire) (finally (.stop server)))))

(tu/deftest-kb ^:slow catch-up-resumes-from-a-stored-cursor
  (with-daemon kb
    (fn [_conn wire]
      (let [author (wire 'AgentAva)
            store  (cu/atom-store)
            c1 (cu/open (wire 'AgentBoreas) goal 'CxDeploy store)]
        (cu/sync! c1)
        (is (empty? (cu/view-of c1)) "a fresh consumer over an empty channel sees nothing")
        (ch/pose-query author 'Q1)
        (ch/pose-query author 'Q2)
        (cu/sync! c1)
        (is (= #{(q 'Q1) (q 'Q2)} (cu/view-of c1)) "the tail delivered both queries")
        (is (= (cu/snapshot (:handle c1) goal 'CxDeploy) (cu/view-of c1))
            "and the wire query grounds to the same set a snapshot would")
        (testing "a restart reloads the cursor + the durable view and tails the next write"
          (let [c2 (cu/open (:handle c1) goal 'CxDeploy store (cu/view-of c1))]
            (ch/pose-query author 'Q3)
            (cu/sync! c2)
            (is (= #{(q 'Q1) (q 'Q2) (q 'Q3)} (cu/view-of c2))
                "resumed from cursor N — Q3 tailed on, nothing missed or doubled")))))))

(tu/deftest-kb ^:slow catch-up-catches-overflow-with-a-snapshot
  (with-daemon kb
    (fn [_conn wire]
      (with-redefs [sub/max-events 4]                       ; a tiny ring, so a short absence overflows
        (let [author (wire 'AgentAva)
              store  (cu/atom-store)
              c (cu/open (wire 'AgentBoreas) goal 'CxDeploy store)]
          (cu/sync! c)                                      ; bootstrap at the tail (empty so far)
          (doseq [i (range 10)]                             ; > the ring's worth, past the idle consumer
            (ch/pose-query author (symbol (str "Over" i))))
          (cu/sync! c)                                      ; must detect lag and snapshot
          (is (= 10 (count (cu/view-of c)))
              "ended in the state it would have reached — the six that fell off the ring are
               recovered by the snapshot, not silently lost")
          (is (= (cu/snapshot (:handle c) goal 'CxDeploy) (cu/view-of c))
              "the view equals a full re-read"))))))

(tu/deftest-kb ^:slow catch-up-reread-and-replay-converge
  (with-daemon kb
    (fn [_conn wire]
      (with-redefs [sub/max-events 4]
        (let [author  (wire 'AgentAva)
              tailer  (cu/open (wire 'AgentBoreas) goal 'CxDeploy (cu/atom-store))
              snapper (cu/open (wire 'AgentCiel) goal 'CxDeploy (cu/atom-store))]
          (cu/sync! tailer)
          (cu/sync! snapper)                                ; both bootstrap at the tail
          (doseq [i (range 10)]
            (ch/pose-query author (symbol (str "Conv" i)))
            (cu/sync! tailer))                              ; the tailer keeps up — always in-ring
          (cu/sync! snapper)                                ; the snapshotter was idle — it lagged
          (is (= 10 (count (cu/view-of tailer))) "the tailer replayed every event")
          (is (= (cu/view-of tailer) (cu/view-of snapper))
              "identical state whether recovered by tail-replay or by snapshot re-read"))))))

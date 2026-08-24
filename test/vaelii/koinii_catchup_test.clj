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

  Wire-only: the ring / cursor / lag exist on the wire feed, so this needs a daemon.

  Four cases need no daemon and get a **scripted medium** instead: what `sync!` does when
  the poll fails, what it does when two threads drive one consumer, what a replayed
  `:believed-removed` leaves the view at, and how far one pass will re-snapshot when reply
  after reply reports a lag.  Each is about `sync!`'s own control flow rather than about a
  real feed, and a scripted medium is what makes the failing reply, the interleaving, the
  redelivery and the lag sequence deterministic."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [vaelii.client :as vc]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.koinii.catchup :as cu]
            [vaelii.impl.koinii.channel :as ch]
            [vaelii.impl.koinii.speech-acts :as sa]
            [vaelii.impl.serve :as serve]
            [vaelii.impl.subscribe :as sub]
            [vaelii.test-util :as tu])
  (:import [java.util.concurrent CountDownLatch TimeUnit]
           [org.eclipse.jetty.server Server]))

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

;;; ── the scripted medium: `sync!`'s control flow, without a daemon ─────────

(defn- scripted-medium
  "A `Medium` whose feed answers from `script` — `{:open (fn [] …) :query (fn [] …) :poll
  (fn [token cursor] …)}` — so a test says exactly what the far end does and when.  Only
  the three methods catch-up calls are implemented; the rest of the protocol is not this
  medium's business and reaching one is the test's own bug."
  [script]
  #_{:clj-kondo/ignore [:missing-protocol-method]}
  (reify ch/Medium
    (-feed-open [_ _goal _ctx] ((:open script)))
    (-query [_ _goal _ctx] ((:query script)))
    (-feed-poll [_ token cursor _opts] ((:poll script) token cursor))))

(defn- recording-store
  "A `CursorStore` over an atom, with `on-read` called at every `read-position` — the seam
  the interleaving test uses to hold two threads at the read that starts `sync!`."
  ([] (recording-store (fn [])))
  ([on-read]
   (let [a (atom nil)]
     (reify cu/CursorStore
       (read-position [_] (on-read) @a)
       (write-position! [_ p] (reset! a p) p)))))

(deftest a-poll-that-throws-without-a-type-is-still-a-failure
  ;; The refusals catch-up discriminates on carry a `:type`, but a transport is free to
  ;; throw something else — and read as `{:err nil}` that falls through to the
  ;; drained-to-head arm, which persists `{:cursor nil}` and hands back the stale view as
  ;; though the stream were current: silent loss, the one failure this module exists to
  ;; prevent.
  (let [store  (recording-store)
        medium (scripted-medium
                {:open  (fn [] {:token "T" :cursor 7})
                 :query (fn [] [])
                 :poll  (fn [_ _] (throw (ex-info "the proxy hung up" {})))})
        c      (cu/open {:medium medium} goal 'CxDeploy store #{'(queries Ava Q1)})]
    (cu/write-position! store {:token "T" :cursor 7})       ; a consumer mid-stream
    (testing "an exception with no :type is reported, not swallowed"
      (let [e (try (cu/sync! c) nil (catch clojure.lang.ExceptionInfo e e))]
        (is (some? e) "sync! reported the error")
        (is (= "the proxy hung up" (ex-message (ex-cause e)))
            "and carries the original as its cause")))
    (testing "and the cursor is left where it was — never advanced past a poll that failed"
      (is (= {:token "T" :cursor 7} (cu/read-position store))))
    (testing "the view is untouched too"
      (is (= #{'(queries Ava Q1)} (cu/view-of c))))))

(deftest two-threads-driving-one-consumer-do-not-corrupt-its-view
  ;; A consumer has one driving thread (`open`), and `sync!` takes the consumer's monitor so
  ;; a second caller cannot interleave inside the read-modify-write over `{:store :view}`.
  ;; Unguarded, both threads read "no cursor", both bootstrap, and the second's snapshot
  ;; `reset!` lands on top of the first's applied batch — the tail's work erased and the
  ;; events already consumed, so the view ends EMPTY where one sequential `sync!` ends full.
  (let [batch    [{:believed-added [{:sentence '(queries Ava Q1)}]}]
        entered  (CountDownLatch. 2)
        queried  (atom 0)
        applied  (CountDownLatch. 1)
        polls    (atom 0)
        medium   (scripted-medium
                  {:open  (fn [] {:token "T" :cursor 0})
                   ;; the FIRST snapshot answers at once; a second one waits until the
                   ;; first caller has applied its batch, which is the interleaving that
                   ;; makes the clobber deterministic rather than lucky
                   :query (fn []
                            (when (> (swap! queried inc) 1)
                              (.await applied 2 TimeUnit/SECONDS))
                            [])
                   ;; the batch is delivered ONCE, as a ring delivers it: whoever polls
                   ;; first gets it, and the next poll is the drained-to-head one
                   :poll  (fn [_ _]
                            (let [n (swap! polls inc)]
                              (when (= 2 n) (.countDown applied))
                              (if (= 1 n)
                                {:events batch :cursor 1 :lagged 0}
                                {:events [] :cursor 1 :lagged 0})))})
        ;; both threads must reach the opening `read-position` before either writes one,
        ;; or the race the monitor prevents never gets a chance to happen
        store    (recording-store (fn []
                                    (.countDown entered)
                                    (.await entered 300 TimeUnit/MILLISECONDS)))
        c        (cu/open {:medium medium} goal 'CxDeploy store)
        start    (CountDownLatch. 1)
        run      (fn [] (future (.await start) (cu/sync! c)))
        [f1 f2]  [(run) (run)]]
    (.countDown start)
    (is (= #{'(queries Ava Q1)} @f1 @f2)
        "each caller is handed the view a single sequential sync! would have left")
    (is (= #{'(queries Ava Q1)} (cu/view-of c))
        "and the consumer's view is that view — the second caller's snapshot did not
         land on top of the first's applied batch")))

(deftest a-replayed-remove-reaches-the-same-view-as-a-re-read
  ;; The `:believed-removed` half of `apply-events`: a sentence leaving belief leaves the
  ;; view.  The drop is set-based, which is what makes the replay claim true for removes as
  ;; well as adds — an at-least-once feed redelivering a batch that both added and removed
  ;; must land on the view a full re-read gives, not on one where the re-add outlived the
  ;; drop or the drop outlived a later add.
  (let [batch  [{:believed-added   [{:sentence (q 'Q1)} {:sentence (q 'Q2)}]}
                {:believed-removed [{:sentence (q 'Q1)}]}]
        polls  (atom 0)
        medium (scripted-medium
                {:open  (fn [] {:token "T" :cursor 0})
                 ;; the channel's current truth: Q1 has been retracted, Q2 stands
                 :query (fn [] [{'?a 'AgentAva '?q 'Q2}])
                 ;; an at-least-once feed: the same batch arrives twice before the head
                 :poll  (fn [_ _]
                          (let [n (swap! polls inc)]
                            (if (< n 3)
                              {:events batch :cursor n :lagged 0}
                              {:events [] :cursor n :lagged 0})))})
        c      (cu/open {:medium medium} goal 'CxDeploy (recording-store))]
    (is (= #{(q 'Q2)} (cu/sync! c)) "the removed sentence is not in the view")
    (is (= (cu/snapshot (:handle c) goal 'CxDeploy) (cu/view-of c))
        "and the twice-replayed remove leaves exactly what a full re-read gives")
    (is (= 3 @polls) "the drain really did apply the batch twice before the head")))

(deftest a-second-lag-inside-one-pass-is-recovered-by-the-next-sync
  ;; `snapped` stops one `sync!` pass re-snapshotting on every lagged reply — a drain that
  ;; keeps reporting drops would otherwise re-read the whole channel per poll.  What the
  ;; guard must not do is LOSE those later drops: a pass starts un-snapped, so the next
  ;; `sync!` re-reads and the view catches up.  The snapshot answers differently on the
  ;; second call, which is how the catch-up is visible at all.
  (let [queries (atom 0)
        polls   (atom 0)
        medium  (scripted-medium
                 {:open  (fn [] {:token "T" :cursor 0})
                  :query (fn [] (if (= 1 (swap! queries inc))
                                  [{'?a 'AgentAva '?q 'Q1}]
                                  [{'?a 'AgentAva '?q 'Q1} {'?a 'AgentAva '?q 'Q2}]))
                  ;; every reply is drained-to-head; the lag count falls to zero over four
                  :poll  (fn [_ _]
                           (let [n (swap! polls inc)]
                             {:events [] :cursor n :lagged (max 0 (- 4 n))}))})
        store   (recording-store)
        c       (cu/open {:medium medium} goal 'CxDeploy store)]
    (cu/write-position! store {:token "T" :cursor 7})        ; a consumer mid-stream
    (testing "one pass snapshots once, however many of its replies report a lag"
      (is (= #{(q 'Q1)} (cu/sync! c)))
      (is (= 1 @queries) "the second lagged reply in the same drain did not re-read")
      (is (= 2 @polls) "and the pass really did see two lagged replies"))
    (testing "and the lag it carried over is recovered by the next call"
      (is (= #{(q 'Q1) (q 'Q2)} (cu/sync! c)))
      (is (= 2 @queries) "a fresh pass starts un-snapped, so it re-read")
      (is (= {:token "T" :cursor 4} (cu/read-position store))
          "ending drained to the head, with the position persisted"))))

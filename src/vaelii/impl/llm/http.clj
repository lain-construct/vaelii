;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.llm.http
  "What every HTTP provider does that is not its wire format — the read deadline, the
  JSON-body refusal, and the excerpt both of them carry.

  A provider namespace (`vaelii.impl.llm.ollama`, `vaelii.impl.llm.anthropic`) is two
  things at once: an *encoding* of one vendor's messages, tools and stop reasons, and a
  *transport* that posts bytes and reads a body under a deadline.  The first is the whole
  reason each exists separately and is not shared.  The second was written out twice,
  identically bar the vendor's name inside a string — and a deadline policy that lives in
  two places is one that gets fixed in one.

  Each provider passes an **endpoint** descriptor, `{:label :slug}`: `:label` is how the
  far end is named in a message a reader sees (\"the Ollama host\", \"the Anthropic
  API\"), `:slug` how it is named in a thread title.  That pair is the entire difference
  between the two copies this replaces."
  (:require [cheshire.core :as json]))

(def connect-timeout-ms
  "How long to wait for the **connection** — the TCP handshake, and the TLS one over it.

  Fixed, and deliberately unrelated to a turn's `:timeout-ms`.  The two bound different
  things: a turn may legitimately run for minutes (a cold 14B load, a high-effort answer),
  while a connection either completes in well under a second or is not going to.  Handing
  the turn's budget to `connectTimeout` makes an unreachable host cost the whole turn —
  five minutes on Ollama, ten on the Messages API — for a host that never answered the
  SYN, which is the shape of a hang rather than of a refusal.

  Five seconds is far above any healthy handshake, the remote API's TLS one included, and
  far below every turn budget here.  A probe that wants to fail faster still can: the
  request's own `.timeout` bounds the exchange, connection included, so
  `vaelii.impl.llm.ollama/version` keeps its two-second gate."
  5000)

(defn excerpt
  "The opening of a body, for an exception's data.  A response can be megabytes and what
  says *why* it would not parse is its first line, so the bound costs no diagnosis."
  [^String s]
  (when s (subs s 0 (min (.length s) 200))))

(defn decode
  "A JSON body -> data.  Every refusal a provider raises carries a `:type`, and a 200
  whose body is not JSON is one: a caller discriminates on the keyword, and the JSON
  library's own exception is not something to discriminate on.  A proxy in front of the
  endpoint answering HTML is the case that reaches here.  The text stays out of the
  message and rides bounded in `:excerpt`."
  [{:keys [label]} ^String text status]
  (try
    (json/parse-string text)
    (catch Exception e
      (throw (ex-info (str label " answered " status " with a body that is not JSON")
                      {:type :llm-bad-response :status status :excerpt (excerpt text)}
                      e)))))

(defn watchdog
  "A daemon thread that runs `on-expiry` once `ms` have passed; interrupt it to cancel.
  Daemon because a probe or a stalled read must never be the reason a JVM cannot exit."
  ^Thread [{:keys [slug]} ms on-expiry]
  (doto (Thread. ^Runnable (fn []
                             (try
                               (Thread/sleep (long ms))
                               (on-expiry)
                               (catch InterruptedException _ nil)
                               (catch Exception _ nil)))
                 (str "vaelii-" slug "-deadline"))
    (.setDaemon true)
    (.start)))

(defn under-read-deadline
  "Run `f` under a hard deadline on **reading** a response body: a daemon watchdog runs
  `on-expiry` — closing the body, which is what makes a blocked read fail — once `ms`
  have passed, and a failure raised after it fires is reported as `:llm-timeout` rather
  than as whatever a closed socket happened to raise.

  The request's own `.timeout` bounds the response *arriving*, and a streamed turn is
  almost entirely what comes after that: the lines are pulled off the socket once `send`
  has returned.  This is what stops an endpoint that goes quiet mid-answer — a model
  evicted under memory pressure is the way that happens locally — from holding the
  calling thread for as long as it keeps the connection half-open.  `f` consumes its
  lines eagerly, so returning from it means the body is read.

  **`Throwable`, not `Exception`.**  What `f` does is parse bytes a far end chose, and the
  failures that reaches are not all `Exception`s: a deeply nested JSON body overflows the
  stack, an oversized one exhausts the heap, and both arrive as an `Error`.  Caught
  narrowly, an `Error` raised after the watchdog closed the body would escape as itself —
  a `StackOverflowError` where the caller's own catch expects `:llm-timeout`, reported as a
  parser bug rather than as the deadline that fired.  So both arms are widened: with the
  deadline spent the failure is rewritten `:llm-timeout` whatever its class, and with it
  unspent the original is rethrown unchanged.  The watchdog is cancelled either way — the
  `finally` runs before the throw leaves."
  [{:keys [label] :as endpoint} ms on-expiry f]
  (let [expired    (atom false)
        ^Thread wd (watchdog endpoint ms (fn [] (reset! expired true) (on-expiry)))]
    (try
      (f)
      (catch Throwable t
        (if @expired
          ;; the closed socket's own throwable rides as the cause: `:llm-timeout` says
          ;; the deadline fired, and what the read was doing when it did is the next
          ;; question anyone asks.
          (throw (ex-info (str label " stopped answering while its response was being"
                               " read — " ms " ms of the turn's :timeout-ms budget"
                               " remained for the body; raise :timeout-ms to wait longer")
                          {:type :llm-timeout :timeout-ms ms}
                          t))
          (throw t)))
      (finally (.interrupt wd)))))

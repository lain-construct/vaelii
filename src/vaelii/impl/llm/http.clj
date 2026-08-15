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
  lines eagerly, so returning from it means the body is read."
  [{:keys [label] :as endpoint} ms on-expiry f]
  (let [expired    (atom false)
        ^Thread wd (watchdog endpoint ms (fn [] (reset! expired true) (on-expiry)))]
    (try
      (f)
      (catch Exception e
        (if @expired
          (throw (ex-info (str label " stopped answering while its response was being read")
                          {:type :llm-timeout :timeout-ms ms}))
          (throw e)))
      (finally (.interrupt wd)))))

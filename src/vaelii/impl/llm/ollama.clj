;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.llm.ollama
  "A local backend: Ollama's chat API over raw HTTP.

  Same shape as `vaelii.impl.llm.anthropic` — the neutral request/response maps of
  `vaelii.impl.llm.protocol`, an explicit connection handle, no global state, **no new
  dependency** (`cheshire` for JSON, JDK `java.net.http`).  What differs is everything
  the transport does:

  * **No credential.**  Ollama serves on a host, not behind an API key, so
    `available?` is a reachability probe rather than a credential lookup.  That is what
    makes this backend testable end to end.
  * **The context window is the caller's to set** — `options.num_ctx`, per request.
    Ollama **silently truncates** a prompt longer than it, which would quietly drop the
    user's selection, so the caller sizes the prompt against `num-ctx` *before* sending
    (`vaelii.impl.llm.selection/budget-problem`); nothing here truncates.
  * **Constrained decoding instead of tool calls.**  `:format` carries a JSON schema
    that the sampler is restricted to, so a model with no `tools` capability still
    answers in an exact shape.  `capabilities` reads what a model can actually do, and
    `supports-tools?` is the gate — sending 61 tool schemas to a completion-only model
    spends the whole window on something it will never emit.
  * **Streaming is newline-delimited JSON**, not SSE: one object per token-ish chunk,
    the last carrying `done: true` and the run's counts.

  Counts come back on every response — `prompt_eval_count` is the **measured** prompt
  size, which is what a budget is checked against after the fact."
  (:require [cheshire.core :as json]
            [clojure.string :as str]
            [vaelii.impl.llm.http :as http]
            [vaelii.impl.llm.protocol :as proto])
  (:import [java.io BufferedReader InputStream InputStreamReader]
           [java.net URI]
           [java.net.http HttpClient HttpClient$Builder HttpRequest HttpRequest$Builder
            HttpRequest$BodyPublishers HttpResponse HttpResponse$BodyHandlers]
           [java.nio.charset StandardCharsets]
           [java.time Duration]))

(def default-host
  "The Ollama this backend talks to unless told otherwise — Ollama's own default address,
  on the machine running this code.  A host on the network is somebody's deployment and
  not a default: `VAELII_OLLAMA_HOST` names one, and `OLLAMA_HOST` is read too, so
  pointing this at another box is configuration rather than an edit."
  "http://localhost:11434")

(def default-model
  "The model this backend runs unless told otherwise.  `VAELII_OLLAMA_MODEL` overrides,
  and `provider`'s `:model` overrides per call.

  Measured on the selection-editing task, for a caller trading latency against rigor:

  | model | on this task | notes |
  |---|---|---|
  | `phi4:14b` | 1.7 s | the default; strong at rewriting shown lines, weak at coining new ones |
  | `qwen3.6:27b` | 11.8 s | better judgement; **ignores** `format`, answers in the line format anyway |
  | `qwen2.5-coder:32b` | 20.2 s | the most formally reliable; honours `format` |

  **Editing and generating want different models.**  This one is for the edit path, where
  it is both correct and the fastest thing available; it produces nothing usable on the
  page-generation path under either output contract.  That path's model is
  `default-generation-model`."
  "phi4:14b")

(def default-generation-model
  "The model the **page-generation** path runs (`vaelii.impl.llm.session/propose-page`)
  unless told otherwise.  `VAELII_OLLAMA_GENERATION_MODEL` overrides.

  Measured on the flesh-out task — write new type-level common sense about a term, under
  `page/output-schema`:

  | model | admissible assertions | warm wall clock | notes |
  |---|---|---|---|
  | `qwen3-coder:30b` | 20/20 | 1.9 s | the default; needs the vocabulary card to stop coining |
  | `phi4:14b` | 0 | — | nothing usable under either output contract |

  Generation is a different job from rewriting shown lines, so the two paths default
  differently rather than sharing one compromise."
  "qwen3-coder:30b")

(def default-keep-alive
  "How long the host holds the model resident after a turn.  `VAELII_OLLAMA_KEEP_ALIVE`
  overrides, and a request's `:keep-alive` overrides per call.

  Deliberately long, because **the latency of a local turn is model load, not
  generation**: measured on the page-generation task, three identical calls took 11.33 s,
  then 0.39 s, then 0.30 s — the first paid for reading 18 GB of weights off disk and the
  rest paid nothing.  Prefill of a full page prompt is 0.02–0.20 s and generation 1.2–2.5
  s, so a resident model is the whole difference between a usable panel and an unusable
  one."
  "30m")

(def default-num-ctx
  "The context window a request asks for unless told otherwise.  Deliberately far under
  the model's native ceiling: a selection-scoped prompt is small, and a smaller window
  is less KV cache, a faster prefill, and a hard budget that surfaces an oversized
  selection as a refusal instead of a silent truncation.  `VAELII_OLLAMA_NUM_CTX`
  overrides."
  8192)

(def default-num-predict
  "The output cap.  A rewritten selection is roughly one JSON object per selected
  sentex, so this bounds a runaway generation without cutting an honest answer short."
  4096)

;; ---- host resolution ----------------------------------------------------

(defn normalize-host
  "A host string -> the base URL to call.  A host is conventionally written bare
  (`localhost:11434`, `127.0.0.1`), so a missing scheme is filled in and a trailing
  slash dropped."
  [host]
  (let [h (str/trim (str host))
        h (if (re-find #"^https?://" h) h (str "http://" h))]
    (str/replace h #"/+$" "")))

(defn- bind-address?
  "Is this an `OLLAMA_HOST` set for a **server** rather than a client?  `OLLAMA_HOST`
  is overloaded — `ollama serve` reads it as the address to bind, and a machine running
  its own Ollama commonly has it set to a wildcard.  A wildcard is not somewhere to
  connect *to*, so it is not read as one."
  [host]
  (some? (re-find #"^(https?://)?(0\.0\.0\.0|\[?::\]?|\*)(:|$)" (str/trim (str host)))))

(defn base-url
  "The Ollama base URL: `VAELII_OLLAMA_HOST`, else `OLLAMA_HOST` when it names a real
  target, else `default-host`."
  []
  (normalize-host
   (or (not-empty (str (System/getenv "VAELII_OLLAMA_HOST")))
       (let [h (not-empty (str (System/getenv "OLLAMA_HOST")))]
         (when (and h (not (bind-address? h))) h))
       default-host)))

(defn configured-model
  "The model to run: `VAELII_OLLAMA_MODEL` when set, else `default-model`."
  []
  (or (not-empty (str (System/getenv "VAELII_OLLAMA_MODEL"))) default-model))

(defn configured-generation-model
  "The model the page-generation path runs: `VAELII_OLLAMA_GENERATION_MODEL` when set,
  else `default-generation-model`."
  []
  (or (not-empty (str (System/getenv "VAELII_OLLAMA_GENERATION_MODEL")))
      default-generation-model))

(defn configured-num-ctx
  "The context window to ask for: `VAELII_OLLAMA_NUM_CTX` when set and numeric, else
  `default-num-ctx`."
  []
  (or (try (some-> (System/getenv "VAELII_OLLAMA_NUM_CTX") str/trim not-empty Long/parseLong)
           (catch Exception _ nil))
      default-num-ctx))

(defn configured-keep-alive
  "How long to ask the host to hold the model resident: `VAELII_OLLAMA_KEEP_ALIVE` when
  set, else `default-keep-alive`."
  []
  (or (not-empty (str (System/getenv "VAELII_OLLAMA_KEEP_ALIVE"))) default-keep-alive))

;; ---- transport primitives -----------------------------------------------

(defn- new-client
  "A fresh `HttpClient` on the shared connect deadline (`http/connect-timeout-ms`).  The
  turn's own `:timeout-ms` rides on the *request* (`post-builder`), where it bounds the
  answer arriving rather than the socket opening."
  ^HttpClient []
  (let [^HttpClient$Builder b (HttpClient/newBuilder)]
    (.connectTimeout b (Duration/ofMillis (long http/connect-timeout-ms)))
    (.build b)))

(def probe-client
  "The one `HttpClient` every probe shares — `version`, `show` and `warm`, and so
  `available?` and `capabilities` above them.

  A client owns a connection pool and a selector thread, so building one per call leaks
  both: `available?` runs on every `/propose` the browser posts, and each of those was a
  fresh pool that answered one request and was left to the collector.  Nothing here varies
  per call — a probe's host rides on the request URI and its deadline on the request — so
  one client serves them all.

  A provider keeps its **own** client (`provider`): a turn is long-lived and streams, and
  its connections are not a probe's to share."
  (delay (new-client)))

(defn- post-builder
  ^HttpRequest$Builder [conn path payload]
  (let [^HttpRequest$Builder rb (HttpRequest/newBuilder (URI/create (str (:base-url conn) path)))]
    (.timeout rb (Duration/ofMillis (long (:timeout-ms conn))))
    (.header rb "content-type" "application/json")
    (.POST rb (HttpRequest$BodyPublishers/ofString ^String (json/generate-string payload)))
    rb))

(defn- api-error
  "The exception for a failed call.  **Ollama's `error` field is the message** — it is
  where a real diagnosis lives (a corrupt model blob answers 500 with
  `failed to load model … sha256-…`), and a body read only as JSON-to-parse turns that
  into an unrelated parse failure downstream.

  **The message is bounded, the body is data** — `http/decode`'s rule, and for the same
  reason: the failing body is whatever answered, a proxy in front of the host answers
  megabytes of HTML, and a megabyte in a message is a megabyte in every log line that
  reports it.  `http/excerpt` bounds what the message carries; the whole text rides under
  `:body`, where a caller that wants it reads it deliberately."
  [status ^String body-text]
  (let [parsed (try (json/parse-string body-text) (catch Exception _ nil))]
    (ex-info (str "Ollama API " status ": "
                  (http/excerpt (str (or (get parsed "error") body-text))))
             {:type :llm-api-error :status status :error (get parsed "error")
              :body body-text})))

(defn- throw-on-error-field
  "Ollama also reports a failure **inside a 200** — and inside a streamed chunk — so the
  field is checked whatever the status line said.  Returns the body."
  [m]
  (if-let [e (and (map? m) (get m "error"))]
    (throw (ex-info (str "Ollama error: " e) {:type :llm-api-error :error e}))
    m))

(def ^:private endpoint
  "How this provider's far end is named — in a message a reader sees, and in the
  deadline thread's title.  `vaelii.impl.llm.http` takes it; it is the whole of what
  distinguishes this namespace's transport from the Anthropic one's."
  {:label "the Ollama host" :slug "ollama"})

(defn- decode
  "This host's JSON-body refusal — `http/decode` with the endpoint supplied, so the
  read sites below stay a one-argument call."
  [text status]
  (http/decode endpoint text status))

;; ---- probes -------------------------------------------------------------

(defn version
  "The Ollama server's version string, or nil when it is not reachable.  `timeout-ms`
  is short by default: this is a gate, and a caller that must decide between this
  backend and the stub should not wait on a dead host."
  ([] (version {}))
  ([{:keys [host timeout-ms] :or {timeout-ms 2000}}]
   (try
     (let [url (or host (base-url))
           ^HttpClient http @probe-client
           ^HttpRequest$Builder rb (HttpRequest/newBuilder (URI/create (str url "/api/version")))
           _ (.timeout rb (Duration/ofMillis (long timeout-ms)))
           ^HttpResponse resp (.send http (.build (.GET rb)) (HttpResponse$BodyHandlers/ofString))]
       (when (<= 200 (.statusCode resp) 299)
         (get (json/parse-string ^String (.body resp)) "version")))
     (catch Exception _ nil))))

(defn available?
  "Is an Ollama reachable?  The gate a caller uses to decide between this backend and
  the stub, and the one the live tests skip on."
  ([] (available? {}))
  ([opts] (some? (version opts))))

(defn show
  "`/api/show` for one model — its template, parameters, and declared capabilities.
  nil when the host or the model is not reachable."
  ([model] (show model {}))
  ([model {:keys [host timeout-ms] :or {timeout-ms 10000}}]
   (try
     (let [conn {:base-url (or host (base-url))
                 :timeout-ms timeout-ms}
           ^HttpClient http @probe-client
           ^HttpResponse resp (.send http (.build (post-builder conn "/api/show" {"model" model}))
                                     (HttpResponse$BodyHandlers/ofString))]
       (when (<= 200 (.statusCode resp) 299)
         (json/parse-string ^String (.body resp))))
     (catch Exception _ nil))))

(defn capabilities
  "The capability keywords a model declares — `#{:completion}`, `#{:completion :tools}`,
  … — or nil when it cannot be read.  A model without `:tools` **cannot tool-call**: its
  chat template has no tools section, so schemas sent to it are window spent on nothing."
  ([model] (capabilities model {}))
  ([model opts]
   (some->> (get (show model opts) "capabilities")
            (map (comp keyword str/lower-case str))
            set)))

(defn supports-tools?
  "Can this model use tool schemas?  False for a completion-only model, and false when
  the host cannot be reached — the conservative answer, since the cost of guessing yes
  is a wasted context window."
  ([model] (supports-tools? model {}))
  ([model opts] (boolean (some-> (capabilities model opts) :tools))))

(defn- filler
  "About `tokens` tokens of ordinary prose for `warm` to prefill with.  Its content is
  irrelevant — only its length is — but it says what it is, so a stray warm-up request in a
  host log is not a mystery."
  [tokens]
  (apply str (repeat (max 1 (quot (long tokens) 12))
                     "This request only warms the model up; nothing here is knowledge. ")))

(defn warm
  "Make a model ready to answer fast, and hold it that way.  Returns
  `{:loaded? bool :elapsed-ms n :model m :prefill-tokens n}`.

  Loading the weights is only half the cost.  Measured on a 30B, with the model already
  resident, the *first* page turn still took 6.4 s to its first assertion while every turn
  after it took 0.40 s — the first real prefill pays for the window's KV cache and the
  compute path at that size.  So this warms with a **prefill of a realistic size**
  (`:prefill-tokens`, 2048) at the same window a request will use, and generates one token.
  That moves the one-off 6 s into the warm-up: the turn after it is 0.7 s to first
  assertion.

  Called when a page opens, it turns the reader's first question from a ten-second wait
  into a sub-second one.  Bare, not `warm!` — it destroys nothing; it spends memory on the
  host.

  `opts`: `:host`, `:timeout-ms` (300000), `:keep-alive`, `:num-ctx`, `:prefill-tokens`."
  ([] (warm (configured-generation-model) {}))
  ([model] (warm model {}))
  ([model {:keys [host timeout-ms keep-alive num-ctx prefill-tokens]
           :or {timeout-ms 300000 prefill-tokens 2048}}]
   (let [started (System/currentTimeMillis)
         conn {:base-url (or host (base-url)) :timeout-ms timeout-ms}
         payload {"model" model
                  "messages" [{"role" "system" "content" (filler prefill-tokens)}
                              {"role" "user" "content" "ok"}]
                  "stream" false
                  "options" {"num_ctx" (long (or num-ctx (configured-num-ctx)))
                             "num_predict" 1
                             "temperature" 0}
                  "keep_alive" (or keep-alive (configured-keep-alive))}
         out {:model model :prefill-tokens prefill-tokens}]
     (try
       (let [^HttpClient http @probe-client
             ^HttpResponse resp (.send http (.build (post-builder conn "/api/chat" payload))
                                       (HttpResponse$BodyHandlers/ofString))]
         (assoc out :loaded? (<= 200 (.statusCode resp) 299)
                :elapsed-ms (- (System/currentTimeMillis) started)))
       (catch Exception _
         (assoc out :loaded? false :elapsed-ms (- (System/currentTimeMillis) started)))))))

(defn context-length
  "The model's native context window from `/api/show`'s `model_info`, or nil.  The
  ceiling a caller's `num-ctx` must stay under; `default-num-ctx` sits well below it."
  ([model] (context-length model {}))
  ([model opts]
   (when-let [info (get (show model opts) "model_info")]
     (some (fn [[k v]] (when (str/ends-with? (str k) ".context_length") v)) info))))

;; ---- request encoding ---------------------------------------------------

(defn- block-text
  "The text one neutral content block contributes to an Ollama message.  Ollama's chat
  messages are plain strings, so a structured block is flattened into the text — a
  tool result included, which is how a tool-capable model reads one back."
  [block]
  (case (:type block)
    :text        (:text block)
    :thinking    nil
    :tool-result (str "tool result" (when (:error? block) " (error)") ": " (:content block))
    :tool-use    nil
    nil))

(defn- encode-message
  "One neutral message -> Ollama's `{role, content}`.  An assistant turn that carried
  tool-use blocks re-emits them as `tool_calls`, so a tool-capable model reads its own
  turn back."
  [{:keys [role content]}]
  (let [blocks (when-not (string? content) content)
        text   (if (string? content)
                 content
                 (str/join "\n" (keep block-text blocks)))
        calls  (for [b blocks :when (= :tool-use (:type b))]
                 {"function" {"name" (:name b) "arguments" (or (:input b) {})}})]
    (cond-> {"role" role "content" text}
      (seq calls) (assoc "tool_calls" (vec calls)))))

(defn- system-text
  "The system blocks joined into the one system message Ollama takes.  `:cache?` is
  dropped: a local model has no prompt-cache breakpoint to mark."
  [blocks]
  (str/join "\n\n" (keep :text blocks)))

(defn body
  "The neutral request -> Ollama's `/api/chat` body.

  `:format` (a JSON schema) constrains decoding, which is how a model with no `tools`
  capability is held to an exact output shape.  `:num-ctx` sizes the window, `:tools`
  is sent only when non-empty, and `temperature` defaults to 0 so a proposal is
  reproducible.

  `keep_alive` is **always** sent (`configured-keep-alive`, 30 minutes by default),
  because model load is the whole latency of a local turn and a host left to its own
  5-minute default evicts the model between one reader's question and the next."
  [{:keys [model system messages tools num-ctx max-tokens temperature keep-alive]
    fmt :format}
   {:keys [stream?]}]
  (let [msgs (cond->> (mapv encode-message messages)
               (seq system) (into [{"role" "system" "content" (system-text system)}]))]
    (cond-> {"model" (or model (configured-model))
             "messages" msgs
             "stream" (boolean stream?)
             "keep_alive" (or keep-alive (configured-keep-alive))
             "options" {"num_ctx" (long (or num-ctx (configured-num-ctx)))
                        "num_predict" (long (or max-tokens default-num-predict))
                        "temperature" (double (or temperature 0))}}
      fmt         (assoc "format" fmt)
      (seq tools) (assoc "tools" (vec tools)))))

;; ---- response decoding --------------------------------------------------

(defn- stop-reason
  "Ollama's `done_reason` -> the protocol's `:stop-reason`.  A turn carrying tool calls
  is `tool_use` whatever the reason says, because that is what the session loop
  branches on."
  [m tool-calls]
  (cond
    (seq tool-calls) "tool_use"
    (= "length" (get m "done_reason")) "max_tokens"
    :else "end_turn"))

(defn- usage
  "The run's counts, named as the protocol names them.  `:input-tokens` is Ollama's
  **measured** prompt size — the number a budget estimate is checked against."
  [m]
  {:input-tokens  (get m "prompt_eval_count")
   :output-tokens (get m "eval_count")
   :load-ms       (some-> (get m "load_duration") (quot 1000000))
   :prompt-ms     (some-> (get m "prompt_eval_duration") (quot 1000000))
   :eval-ms       (some-> (get m "eval_duration") (quot 1000000))
   :total-ms      (some-> (get m "total_duration") (quot 1000000))})

(defn- tool-blocks
  "The `tool_calls` of a message as neutral `:tool-use` blocks.  Ollama emits no call
  id, so one is synthesized positionally — the session loop only ever echoes it back."
  [message]
  (vec (map-indexed
        (fn [i c]
          (let [f (get c "function")]
            {:type :tool-use
             :id (str "ollama_tool_" i)
             :name (get f "name")
             :input (get f "arguments")}))
        (get message "tool_calls"))))

(defn parse-response
  "Ollama's chat JSON -> the neutral response map (`vaelii.impl.llm.protocol`)."
  [m]
  (let [message (get m "message" {})
        calls   (tool-blocks message)
        text    (get message "content")
        think   (get message "thinking")]
    {:stop-reason (stop-reason m calls)
     :model       (get m "model")
     :usage       (usage m)
     :content     (cond-> []
                    (not (str/blank? think)) (conj {:type :thinking :text think})
                    (not (str/blank? text))  (conj {:type :text :text text})
                    true                     (into calls))}))

;; ---- the two transports -------------------------------------------------

(defn- do-complete [conn request]
  (let [^HttpClient http (:http conn)
        payload (body (merge (select-keys conn [:model :num-ctx :keep-alive]) request)
                      {:stream? false})
        ^HttpResponse resp (.send http (.build (post-builder conn "/api/chat" payload))
                                  (HttpResponse$BodyHandlers/ofString))
        status (.statusCode resp)
        text   ^String (.body resp)]
    (if (<= 200 status 299)
      (parse-response (throw-on-error-field (decode text status)))
      (throw (api-error status text)))))

(defn- collect
  "Fold the newline-delimited JSON of a streamed run into the response map `complete`
  would have returned.  Each chunk carries the *delta* under `message.content`; the
  final chunk carries `done: true` and the counts, so the accumulated text is what the
  whole answer was and the counts come from the object that has them."
  [chunks on-event]
  (let [sb    (StringBuilder.)
        think (StringBuilder.)
        acc   (reduce (fn [acc m]
                        (let [msg   (get m "message")
                              d     (get msg "content")
                              t     (get msg "thinking")
                              calls (tool-blocks msg)]
                          (when (not (str/blank? d))
                            (.append sb ^String d)
                            (on-event {:type :text-delta :text d}))
                          (when (not (str/blank? t)) (.append think ^String t))
                          (cond-> acc
                            (seq calls)    (update :calls into calls)
                            (get m "done") (assoc :final m))))
                      {:calls []}
                      chunks)
        final (or (:final acc) {})]
    (on-event {:type :block-stop})
    {:stop-reason (stop-reason final (:calls acc))
     :model       (get final "model")
     :usage       (usage final)
     :content     (cond-> []
                    (pos? (.length think)) (conj {:type :thinking :text (str think)})
                    (pos? (.length sb))    (conj {:type :text :text (str sb)})
                    true                   (into (:calls acc)))}))

(defn- do-stream [conn request on-event]
  (let [^HttpClient http (:http conn)
        payload (body (merge (select-keys conn [:model :num-ctx :keep-alive]) request)
                      {:stream? true})
        ;; taken before the send, so `:timeout-ms` bounds the whole turn rather than the
        ;; headers and then the body for that long again
        deadline (+ (System/currentTimeMillis) (long (:timeout-ms conn)))
        ^HttpResponse resp (.send http (.build (post-builder conn "/api/chat" payload))
                                  (HttpResponse$BodyHandlers/ofInputStream))
        status (.statusCode resp)
        ^InputStream in (.body resp)]
    (http/under-read-deadline
     endpoint
     (max 1 (- deadline (System/currentTimeMillis)))
     #(.close ^InputStream in)
     (fn []
       (with-open [rdr (BufferedReader. (InputStreamReader. in StandardCharsets/UTF_8))]
         (let [lines (line-seq rdr)]
           (when-not (<= 200 status 299)
             (throw (api-error status (str/join "\n" lines))))
           (on-event {:type :block-start :block {:type :text}})
           (let [chunks   (->> lines
                               (remove str/blank?)
                               (map #(throw-on-error-field (decode ^String % status))))
                 response (collect chunks on-event)]
             (on-event {:type :done :response response})
             response)))))))

;; ---- the provider -------------------------------------------------------

(defn provider
  "An Ollama-backed `Provider`.  `opts`:

    :host        default `OLLAMA_HOST`, else `default-host`
    :model       default `VAELII_OLLAMA_MODEL`, else `default-model`
    :num-ctx     default `VAELII_OLLAMA_NUM_CTX`, else `default-num-ctx`
    :keep-alive  how long the host holds the model resident (default
                 `configured-keep-alive`, 30 minutes)
    :timeout-ms  default 300000 — a cold model load on a 14B is tens of seconds.  Bounds
                 the whole turn, the streamed body included, so a host that goes quiet
                 mid-answer releases the thread rather than holding it

  `:model` / `:num-ctx` here are defaults a request may override.  Nothing is validated
  at construction: building a provider opens no socket, so a caller that must know the
  host is up asks `available?`."
  ([] (provider {}))
  ([{:keys [host model num-ctx keep-alive timeout-ms]
     :or {timeout-ms 300000}}]
   (let [conn (cond-> {:base-url (normalize-host (or host (base-url)))
                       :timeout-ms timeout-ms
                       :http (new-client)}
                model      (assoc :model model)
                num-ctx    (assoc :num-ctx num-ctx)
                keep-alive (assoc :keep-alive keep-alive))]
     (with-meta
       (reify proto/Provider
         (complete [_ request] (do-complete conn request))
         (stream [_ request on-event] (do-stream conn request on-event)))
       {:conn (dissoc conn :http)}))))

(defn generation-provider
  "An Ollama provider on the **page-generation** model
  (`configured-generation-model`), for `vaelii.impl.llm.session/propose-page`.  `opts` is
  `provider`'s, and `:model` there still wins.

  It exists to name the pairing: editing and generating are different jobs with different
  best models, and a caller that reaches for `provider` on a page turn gets the edit
  model, which produces nothing usable there."
  ([] (generation-provider {}))
  ([opts] (provider (merge {:model (configured-generation-model)} opts))))

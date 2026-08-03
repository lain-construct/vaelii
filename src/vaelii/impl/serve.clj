;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.serve
  "Headless EDN-over-HTTP daemon: one JVM owns one KB and serves it to remote clients
  (`vaelii.impl.client`).  A thin reitit-ring + jetty layer over `vaelii.core`, the
  network dual of the in-process API.

  **Wire format is EDN.**  A sentence is a symbol s-expression — `(dog Fido)`, `?x`,
  `(genl dog animal)` — which EDN round-trips losslessly; JSON would mangle the symbols.
  The body of every call is `{:op <keyword> :args [...]}`, and the reply is
  `{:ok true :result …}` or `{:ok false :error \"…\"}`.  EDN is read with
  `clojure.edn/read-string` (never `clojure.core/read-string`), so an untrusted body
  cannot evaluate code — EDN has no reader-eval.

  **The daemon is the single writer** (docs/storage.md, the single-writer contract): it
  owns the one process allowed to mutate the store, so it serializes every op through
  one monitor.  Concurrent client writes therefore apply one at a time and cannot
  interleave; reads pay the same lock, which is conservative but keeps the contract
  simple.

  **Only the allowlisted ops are reachable** (`ops`).  Each is a `vaelii.core` fn with
  the KB supplied by the daemon — the client sends only the op and the remaining args —
  so no client can reach an arbitrary var.  Sentex records in a result are projected to
  plain maps before they hit the wire (the `sentex`-map contract), so the client reads
  them back without the `impl` record class.

  **Nothing authenticates a caller**, so `vaelii.impl.guard` stands in for the session
  the daemon does not have: `POST /op` requires `Content-Type: application/edn`, refuses
  a cross-origin `Origin`, and answers only to a `Host` naming the interface it was
  started on.  Together those stop a page the operator happens to visit from driving
  the KB over loopback — which binding to loopback alone does not."
  (:require [clojure.edn :as edn]
            [clojure.walk :as walk]
            [reitit.ring :as ring]
            [ring.adapter.jetty :as jetty]
            [taoensso.trove :as trove]
            [vaelii.core :as v]
            [vaelii.impl.guard :as guard])
  (:import [org.eclipse.jetty.server Server ServerConnector]))

;; ---- the op table: the allowlisted vaelii.core surface -------------------
;; op keyword -> (fn [kb args-vector]).  `apply`ing keeps the varying arities
;; (assert's optional context/opts, why-not's two shapes) working unchanged: the
;; client sends exactly the args it would pass in-process, minus the KB.

(defn- op [f] (fn [kb args] (apply f kb args)))

(def ops
  "The reachable operations, keyed by op keyword.  Reads, writes, and introspection —
  the working set a remote caller needs; extend by adding a `vaelii.core` fn here."
  {:assert       (op v/assert)
   :assert-rule  (op v/assert-rule)
   :assert-many  (op v/assert-many)
   :retract      (op v/retract!)
   :edit         (op v/edit)
   ;; the same write, reporting what it turned out to mean — the *after* to `:preview`'s
   ;; *before*, and the one a caller wants when it has just committed rather than when it
   ;; is deciding whether to
   :edit-with-consequences (op v/edit-with-consequences)
   ;; the dry run of the two above: what `assert` / `edit` would refuse, and why,
   ;; without storing anything.  A remote editor validates before it writes.
   :check        (op v/check)
   :check-edit   (op v/check-edit)
   ;; and the other dry run: not whether the batch would be *admitted* but what it would
   ;; *mean* — the belief it adds and takes away (docs/preview.md).  Served with the
   ;; writes rather than the reads because it applies the batch and rolls it back, so it
   ;; holds the daemon's single writer for its duration; it stores nothing, and hands the
   ;; KB back at the same handles.
   ;; a write to the **filesystem**, not to the KB.  Two things a caller has to know and
   ;; the wire cannot tell them: the directory is resolved on the **daemon's** host — the
   ;; only place it can be, since the daemon owns the KB and there is no stream to hand
   ;; back — and the export reports no progress, because `:on-progress` is a function and
   ;; functions do not cross an EDN wire.  Served with the writes so it runs under the
   ;; monitor: the walk fetches record by record, and a dump of a KB something is
   ;; asserting into is a dump of no single state.
   :export       (op v/export!)
   :preview      (op v/preview)
   :sentexes-matching (op v/sentexes-matching)
   :query        (op v/query)
   :query?       (op v/query?)
   :ask          (op v/ask)
   :ask?         (op v/ask?)
   :prove        (op v/prove)
   :provable?    (op v/provable?)
   :in?          (op v/in?)
   :believed     (op v/believed)
   :why          (op v/why)
   :why-not      (op v/why-not)
   :isa?         (op v/isa?)
   :types-of     (op v/types-of)
   :disjoint?    (op v/disjoint?)
   :genls        (op v/genls)
   :specs        (op v/specs)
   :types        (op v/types)
   :contexts     (op v/contexts)
   :sentex       (op v/sentex)
   :handle-of    (op v/handle-of)
   :find-sentexes (op v/find-sentexes)
   ;; the vocabulary — enumerate / count / search the terms themselves.  Served because
   ;; the alternative for a remote client is shipping every sentex over the wire to
   ;; collect the terms out of them.
   :terms        (op v/terms)
   :term-count   (op v/term-count)
   :sentex-count (op v/sentex-count)
   :find-terms   (op v/find-terms)
   :forward-chain (op v/forward-chain)
   :chain-stats  (op v/chain-stats)
   :conflicts    (op v/conflicts)
   :contradictions (op v/contradictions)
   :violations   (op v/violations)
   ;; the *standing* disjointness question, as against the arising one `settle` files
   ;; into `violations` above.  Computed on demand and not filed, so it is asked for
   ;; rather than accumulated — the read an imported KB needs, since a load rebuilds
   ;; belief rather than changing it and nothing is newly anything to report
   :exposed-clashes (op v/exposed-clashes)
   ;; how a goal would be answered: the provers bearing on it with their estimates, or
   ;; for a conjunction the join order and the counts behind it
   :query-plan   (op v/query-plan)
   ;; introspection reads — the surface a read client (the browser) needs to render
   ;; a KB it does not own; safe to serve, and shared with vaelii.impl.access
   :premise?     (op v/premise?)
   :defeat-class (op v/defeat-class)
   :justification    (op v/justification)
   :supporting-justifications (op v/supporting-justifications)
   :dependent-justifications  (op v/dependent-justifications)
   :lookup       (op v/lookup)
   :escalate     (op v/escalate)
   :explain-levels (op v/explain-levels)
   :context-size (op v/context-size)
   :sentexes-in-context   (op v/sentexes-in-context)
   :sentexes-with-arg     (op v/sentexes-with-arg)
   :sentexes-with-functor (op v/sentexes-with-functor)
   :count-with-arg        (op v/count-with-arg)
   :count-with-functor    (op v/count-with-functor)
   :disjoint-metatypes    (op v/disjoint-metatypes)
   :metatype-members      (op v/metatype-members)
   ;; what a reified term denotes (docs/nat.md).  A remote reader has no other way to
   ;; ask: the constant is opaque by construction, so a client that could not resolve it
   ;; would have to show a reader `nat/g17` — which is the one thing it must not do
   :term-expression       (op v/term-expression)
   ;; qualitative constraint reasoning (docs/qcn.md).  Reads: they compute a network
   ;; from the believed facts and register nothing, so they are safe on a KB the caller
   ;; does not own.  Every result is already EDN — relation keywords, term symbols, and
   ;; vectors of the two — so none of them needs the sentex-map projection below.
   :qualitative-network   (op v/qualitative-network)
   :possible-relations    (op v/possible-relations)
   :qualitative-scenario  (op v/qualitative-scenario)
   :qualitative-scenarios (op v/qualitative-scenarios)})

(defn- wire-safe
  "Make a result EDN-clean for a client that lacks the `impl` record classes: project
  every sentex/record to a plain map (the `sentex`-map contract).  `clojure.walk/walk`
  `doall`s each seq, so a lazy answer stream is realized before the response closes;
  a **list stays a list** (a sentence `(dog Fido)` must not become `[dog Fido]`, or it
  would `pr-str` differently on the far side)."
  [x]
  (walk/postwalk (fn [y] (if (record? y) (into {} y) y)) x))

(def ^:private max-body-bytes
  "The cap on a request body, `VAELII_MAX_BODY_BYTES` or 16 MiB.  An op body is a
  sentence and its context, so the ceiling is nowhere near a legitimate call; it is
  here so an unauthenticated caller cannot spend the daemon's heap by streaming one."
  (or (some-> (System/getenv "VAELII_MAX_BODY_BYTES") Long/parseLong)
      (* 16 1024 1024)))

(defn- read-body
  "The request body as a string, refusing past `max-body-bytes`.  `slurp` would read
  an unbounded body into the heap before anything got to look at it."
  ^String [req]
  (if-let [^java.io.InputStream in (:body req)]
    (let [out   (java.io.ByteArrayOutputStream.)
          chunk (byte-array 8192)]
      (loop []
        (let [n (.read in chunk)]
          (when (pos? n)
            (when (> (+ (.size out) n) max-body-bytes)
              (throw (ex-info (str "request body exceeds " max-body-bytes " bytes")
                              {:type ::body-too-large :limit max-body-bytes})))
            (.write out chunk 0 n)
            (recur))))
      (String. (.toByteArray out) java.nio.charset.StandardCharsets/UTF_8))
    ""))

(defn- handle-op
  "Run one `{:op :args}` request under the write lock and answer with EDN.

  The two guards run before the body is read.  `POST /op` is the write route of an
  unauthenticated single writer, so a page the operator merely *visits* must not be
  able to drive it: `guard/edn-body?` forces a CORS preflight this daemon cannot
  answer, and `guard/same-origin?` refuses a browser that stamped someone else's
  origin.  See `vaelii.impl.guard`."
  [kb monitor req]
  (let [edn-reply (fn [status m]
                    {:status status
                     :headers {"content-type" "application/edn"}
                     :body (pr-str m)})]
    (try
      (cond
        (not (guard/edn-body? req))
        (edn-reply 415 {:ok false :type ::not-edn
                        :error "POST /op requires Content-Type: application/edn"})

        (not (guard/same-origin? req))
        (edn-reply 403 {:ok false :type ::cross-origin
                        :error "cross-origin request refused"})

        :else
        (let [{:keys [op args]} (edn/read-string (read-body req))
              f (ops op)]
          (if f
            (let [result (locking monitor (f kb (vec args)))]
              (edn-reply 200 {:ok true :result (wire-safe result)}))
            (edn-reply 400 {:ok false :error (str "unknown op: " (pr-str op))
                            :ops (vec (sort (keys ops)))}))))
      (catch clojure.lang.ExceptionInfo e
        (if (= ::body-too-large (:type (ex-data e)))
          (edn-reply 413 {:ok false :error (.getMessage e) :type ::body-too-large})
          (do (trove/log! {:level :warn :id ::op-error :error e})
              (edn-reply 500 {:ok false :error (.getMessage e)
                              :type (:type (ex-data e))}))))
      ;; `Throwable`, not `Exception`: an oversized or deeply-nested body raises
      ;; `OutOfMemoryError`/`StackOverflowError`, which an `Exception` catch lets
      ;; escape the handler and kill the connection rather than answering on it.
      (catch Throwable t
        (trove/log! {:level :warn :id ::op-error :error t})
        (edn-reply 500 {:ok false :error (.getMessage t)
                        :type (:type (ex-data t))})))))

(def ^:private loopback
  "The interface the daemon binds unless told otherwise.  `POST /op` is the **write**
  route of the single writer and carries no authentication, so it answers only the
  machine it runs on; exposing it is an explicit choice (`--listen`), not the default.
  The same rule the browser holds to (`vaelii.impl.web`), and the more important of the
  two — the browser edits a KB, and this one *is* the KB's only writer.

  Loopback bounds *which machine* may reach the daemon and nothing more: a browser on
  that machine is a local client too, which is what `vaelii.impl.guard` is for."
  "127.0.0.1")

(defn app
  "The ring handler for a KB — pure `request -> response`, so it is tested without a
  socket.  One monitor per handler serializes the ops (the single-writer contract).

  `:host` names the interface this handler will be served on, which fixes the `Host`
  values it answers to (`guard/allowed-hosts`).  On the loopback default that refuses
  a rebound DNS name, the one attack `same-origin?` cannot see."
  ([kb] (app kb {}))
  ([kb {:keys [host] :or {host loopback}}]
   (let [monitor (Object.)
         allowed (guard/allowed-hosts host)]
     (guard/wrap-host-allowed
      (ring/ring-handler
       (ring/router
        [["/health" {:get (fn [_] {:status 200
                                   :headers {"content-type" "application/edn"}
                                   :body (pr-str {:ok true})})}]
         ["/op" {:post (fn [req] (handle-op kb monitor req))}]])
       (ring/create-default-handler
        {:not-found (fn [_] {:status 404 :headers {"content-type" "application/edn"}
                             :body (pr-str {:ok false :error "not found"})})}))
      allowed
      (fn [_] {:status 400
               :headers {"content-type" "application/edn"}
               :body (pr-str {:ok false :type ::bad-host
                              :error "unrecognized Host header"})})))))

(defn start
  "Start the daemon over `kb` and return the running jetty `Server` (`:join? false`, so
  the caller controls its lifetime — a test stops it in a `finally`).  `:port 0` binds
  an ephemeral port; read the actual one with `port`.

  `:host` defaults to loopback; pass an address (`\"0.0.0.0\"`) to bind publicly, and
  read the note on `loopback` before doing so."
  ^Server [kb {:keys [port host] :or {port 4200 host loopback}}]
  (jetty/run-jetty (app kb {:host host}) {:port port :host host :join? false}))

(defn port
  "The actual TCP port a started `Server` is listening on — the ephemeral one when it
  was started with `:port 0`, read off its first connector."
  ^long [^Server server]
  (.getLocalPort ^ServerConnector (first (.getConnectors server))))

(defn -main
  "Run the daemon in the foreground.  Args: `[port [dir]] [--listen ADDR]` — `dir`
  selects the durable `:disk` backend (recovered on open, so it persists across
  restarts); with no `dir` the KB is in-memory and lives only as long as the process.

    lein run -m vaelii.impl.serve 4200 /var/lib/vaelii
    lein run -m vaelii.impl.serve 4200 /var/lib/vaelii --listen 0.0.0.0   ; opt-in

  It binds **loopback** unless `--listen` says otherwise, for the reason on `loopback`
  above: `POST /op` writes, and nothing authenticates it.  Put a reverse proxy that does
  in front of it before naming an address — and note that naming one also drops the
  `Host` allowlist (`guard/allowed-hosts`), since the name you reach it by is then
  yours to know; set `VAELII_ALLOWED_HOSTS` to keep the check."
  [& args]
  (let [[port-s dir] (vec (take-while #(not (.startsWith ^String % "--")) args))
        host  (or (second (drop-while #(not= "--listen" %) args)) loopback)
        port  (if port-s (Integer/parseInt port-s) 4200)
        kb    (if dir
                (v/open-kb {:backend :disk :dir dir :recover? :auto})
                (v/open-kb {}))]
    (trove/log! {:level :info :id ::start
                 :msg "vaelii daemon listening"
                 :data {:port port :host host :dir (or dir :memory)}})
    (when-not (= host loopback)
      (trove/log! {:level :warn :id ::public-bind
                   :msg (str "daemon bound to " host " — POST /op writes and is "
                             "unauthenticated; put an authenticating proxy in front")
                   :data {:host host}}))
    (jetty/run-jetty (app kb {:host host}) {:port port :host host :join? true})))

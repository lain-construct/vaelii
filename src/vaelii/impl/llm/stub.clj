(ns vaelii.impl.llm.stub
  "The default provider: deterministic, offline, no credential.

  Standing in the same place `vaelii.impl.solve/local-solver` stands — the stub that
  makes the seam usable before (and without) a real backend.  `lein test` runs the
  whole pipeline against it, so the suite needs no API key and opens no socket, and a
  deployment with no credential degrades to a provider that proposes nothing rather
  than to an exception.

  Behaviour is **scripted**, so a test drives the session loop exactly: `:script` is
  the sequence of turns to hand back, one per `complete`/`stream` call, and `:default`
  answers every call past the end of it.  Each entry is a full response map, or one of
  three shorthands:

    \"some text\"                    a plain text answer
    {:batch {:add […] :remove […]}}  text holding that batch in a fenced `edn` block
    {:lines [[sentence context] …]}  the selection path's line set (`:json? true` for
                                     the JSON envelope shape instead)
    {:assertions [sentence …]}       the page path's bare sentences, in the JSON envelope
                                     it decodes under (`:lines? true` for the bare-line
                                     shape a model ignoring `format` writes)
    {:candidates [[sentence seg] …]} the reading path's candidates, each naming the
                                     document sentence it came from (`:untranslated`,
                                     `:notes`)
    {:verdicts [[item verdict] …]}   the judging path's answer, one verdict per numbered
                                     claim (`true` / `false` / `unsure`, optional note)
    {:tool \"kb_sentexes_matching\" :input {…}}  a tool-use turn (`:id` optional)

  With no `:script` the provider answers every turn with an empty batch — valid,
  applies to nothing, and never varies.  That default is the *whole-KB* path's answer;
  on the selection path (`session/propose-edit`) it reads as unparseable, which is the
  safe outcome — the only line set meaning \"change nothing\" is the reader's selection
  itself, and a provider that never saw it cannot write one."
  (:require [cheshire.core :as json]
            [clojure.string :as str]
            [vaelii.impl.llm.protocol :as proto]))

(defn batch-text
  "A model-shaped answer carrying `batch` in the fenced `edn` block the session parser
  reads.  `prose` (optional) is written above it."
  ([batch] (batch-text batch "Proposed edit batch:"))
  ([batch prose]
   (str prose "\n\n```edn\n" (pr-str batch) "\n```")))

(def empty-batch-response
  "The no-script answer: a syntactically valid proposal that changes nothing."
  {:stop-reason "end_turn"
   :model "vaelii-stub"
   :content [{:type :text :text (batch-text {:add [] :remove []}
                                            "The stub provider proposes no changes.")}]
   :usage {:input-tokens 0 :output-tokens 0}})

(defn lines-text
  "A model-shaped answer for the **selection** path: the line set in the editor's own
  format, which is the contract `vaelii.impl.llm.session/parse-lines` reads.  Each entry
  is `[sentence context]` or `[sentence context {:strength :monotonic}]`, so a test
  scripts exactly what the reader would have typed.  `notes` rides above them as prose,
  which is where a model's commentary lands in this format."
  ([lines] (lines-text lines nil))
  ([lines notes]
   (str (when notes (str notes "\n\n"))
        (str/join "\n" (map pr-str lines)))))

(defn json-lines-text
  "The same line set in the JSON envelope a model decoding under
  `vaelii.impl.llm.selection/output-schema` produces — the *other* shape the parser
  tolerates, for a test that drives it."
  ([lines] (json-lines-text lines nil))
  ([lines notes]
   (json/generate-string
    (cond-> {"lines" (for [[sentence context opts] lines]
                       (cond-> {"sentence" (pr-str sentence) "context" (str context)}
                         (= :monotonic (:strength opts)) (assoc "strength" "monotonic")))}
      notes (assoc "notes" notes)))))

(defn assertions-text
  "A model-shaped answer for the **page** path: bare sentences in the JSON envelope
  `vaelii.impl.llm.page/output-schema` constrains decoding to, which is that path's
  contract.  Each entry is a sentence, or `[sentence {:strength :monotonic}]` to claim it
  known-true.  No context — the caller supplies it."
  ([sentences] (assertions-text sentences nil))
  ([sentences notes]
   (json/generate-string
    (cond-> {"assertions" (for [s sentences
                                :let [[sentence opts] (if (and (vector? s) (map? (second s)))
                                                        s
                                                        [s nil])]]
                            (cond-> {"sentence" (pr-str sentence)}
                              (= :monotonic (:strength opts)) (assoc "strength" "monotonic")))}
      notes (assoc "notes" notes)))))

(defn assertion-lines-text
  "The same sentences as bare lines — what a model that ignores `format` writes, and the
  shape `vaelii.impl.llm.session/parse-assertions` falls back to."
  ([sentences] (assertion-lines-text sentences nil))
  ([sentences notes]
   (str (when notes (str notes "\n\n"))
        (str/join "\n" (map #(pr-str (if (and (vector? %) (map? (second %))) (first %) %))
                            sentences)))))

(defn candidates-text
  "A model-shaped answer for the **reading** path: the JSON envelope
  `vaelii.impl.llm.text/output-schema` constrains decoding to.  Each entry is
  `[sentence segment]`, or `[sentence segment opts]` where `opts` may carry
  `:confidence` and `:strength` — so a test scripts exactly which sentence of the document
  a candidate claims to have come from, which is the whole of how a span reaches
  provenance.  `untranslated` is `[[segment reason] …]`."
  ([candidates] (candidates-text candidates nil nil))
  ([candidates untranslated notes]
   (json/generate-string
    (cond-> {"candidates" (for [[sentence segment opts] candidates]
                            (cond-> {"sentence" (pr-str sentence) "segment" segment}
                              (:confidence opts) (assoc "confidence" (name (:confidence opts)))
                              (= :monotonic (:strength opts)) (assoc "strength" "monotonic")))}
      (seq untranslated) (assoc "untranslated"
                                (for [[segment reason] untranslated]
                                  (cond-> {"segment" segment} reason (assoc "reason" reason))))
      notes (assoc "notes" notes)))))

(defn verdicts-text
  "A model-shaped answer for the **judging** path: the JSON envelope
  `vaelii.impl.llm.oracle/output-schema` constrains decoding to.  Each entry is
  `[item verdict]` or `[item verdict note]`, where `verdict` is `true` / `false` /
  `unsure` — so a test scripts a judge that agrees, disputes or shrugs at a named claim,
  and can leave one out to drive the unanswered path."
  [verdicts]
  (json/generate-string
   {"verdicts" (for [[item verdict note] verdicts]
                 (cond-> {"item" item "verdict" (name verdict)}
                   note (assoc "note" note)))}))

(defn- expand
  "Shorthand -> response map."
  [entry i]
  (cond
    (string? entry)
    {:stop-reason "end_turn" :model "vaelii-stub"
     :content [{:type :text :text entry}] :usage {}}

    (contains? entry :verdicts)
    {:stop-reason "end_turn" :model "vaelii-stub"
     :content [{:type :text :text (verdicts-text (:verdicts entry))}]
     :usage {}}

    (contains? entry :candidates)
    {:stop-reason "end_turn" :model "vaelii-stub"
     :content [{:type :text :text (candidates-text (:candidates entry)
                                                   (:untranslated entry)
                                                   (:notes entry))}]
     :usage {}}

    (contains? entry :assertions)
    {:stop-reason "end_turn" :model "vaelii-stub"
     :content [{:type :text :text ((if (:lines? entry) assertion-lines-text assertions-text)
                                   (:assertions entry) (:notes entry))}]
     :usage {}}

    (contains? entry :lines)
    {:stop-reason "end_turn" :model "vaelii-stub"
     :content [{:type :text :text ((if (:json? entry) json-lines-text lines-text)
                                   (:lines entry) (:notes entry))}]
     :usage {}}

    (contains? entry :batch)
    {:stop-reason "end_turn" :model "vaelii-stub"
     :content [{:type :text :text (batch-text (:batch entry)
                                              (or (:prose entry) "Proposed edit batch:"))}]
     :usage {}}

    (contains? entry :tool)
    {:stop-reason "tool_use" :model "vaelii-stub"
     :content (cond-> []
                (:prose entry) (conj {:type :text :text (:prose entry)})
                true (conj {:type :tool-use
                            :id (or (:id entry) (str "stub_tool_" i))
                            :name (:tool entry)
                            :input (or (:input entry) {})}))
     :usage {}}

    :else entry))

(defn provider
  "A stub `Provider`.  `opts`:

    :script   a vector of turns (full response maps or the shorthands above)
    :default  the response for every turn past the script (default: an empty batch)
    :log      an atom the provider `conj`es each request onto, for assertions

  The returned value also answers `:log` and `:calls` through `meta`, so a test that
  did not supply an atom can still see what was asked."
  ([] (provider {}))
  ([{:keys [script default log]}]
   (let [cursor (atom 0)
         log    (or log (atom []))
         default (or default empty-batch-response)
         next-response
         (fn [request]
           (swap! log conj request)
           (let [i (dec (swap! cursor inc))]
             (if (< i (count script))
               (expand (nth script i) i)
               default)))]
     (with-meta
       (reify proto/Provider
         (complete [_ request] (next-response request))
         (stream [_ request on-event]
           (let [response (next-response request)]
             ;; Emit the same text the non-streaming path would, one whitespace-
             ;; separated chunk at a time — enough to exercise a consumer's delta
             ;; handling without pretending to be a network.
             (doseq [block (:content response)]
               (on-event {:type :block-start :block (dissoc block :text)})
               (when (= :text (:type block))
                 (doseq [chunk (re-seq #"\S+\s*" (or (:text block) ""))]
                   (on-event {:type :text-delta :text chunk})))
               (on-event {:type :block-stop}))
             (on-event {:type :done :response response})
             response)))
       {:log log :cursor cursor}))))

(defn requests
  "The requests a stub provider has been handed, oldest first."
  [p]
  @(:log (meta p)))

(defn last-user-text
  "The text of the newest user turn a stub provider saw — what a test asserts the
  repair loop actually fed back."
  [p]
  (let [msgs (:messages (last (requests p)))
        content (:content (last (filter #(= "user" (:role %)) msgs)))]
    (if (string? content)
      content
      (str/join "\n" (keep :text content)))))

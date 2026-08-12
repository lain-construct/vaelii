;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.llm-page-test
  "The page-scoped generation path: `vaelii.impl.llm.inventory`,
  `vaelii.impl.llm.page`, and `vaelii.impl.llm.session/propose-page`.

  Everything above the live section runs **offline against the stub** — no host, no model,
  no socket — because what is under test is the machinery: where the vocabulary inventory
  is sourced from, the arity trap it must not fall into, the coining flag that is the only
  guard against vocabulary fragmentation, the incremental scanner that makes streaming per
  assertion possible, and the invariant that proposing writes nothing.

  The live tier talks to a real Ollama and is **opt-in**: `lein test` skips it with a
  printed reason unless `VAELII_LLM_LIVE=1` says otherwise, so an ordinary run makes no
  model call.  Opted in, it still skips when the host or the model is missing."
  (:require [cheshire.core :as json]
            [clojure.string :as str]
            [clojure.test :refer [is testing use-fixtures]]
            [vaelii.core :as v]
            [vaelii.impl.core-context :as core-context]
            [vaelii.impl.llm.inventory :as inv]
            [vaelii.impl.llm.ollama :as ollama]
            [vaelii.impl.llm.page :as page]
            [vaelii.impl.llm.session :as session]
            [vaelii.impl.llm.stub :as stub]
            [vaelii.test-util :as tu]))

(use-fixtures :each (tu/neutral-fresh #(doto (tu/fresh) (core-context/load-into))))

;; ---- a small schema-only world, like the shipped one --------------------

(defn- world
  "A type hierarchy, three declared relations, and a rule — **no facts**, which is the
  shape the shipped schema has and the reason the inventory cannot be sourced from what
  appears in fact position.  Call it once per test; every call invents new terms."
  [kb]
  (let [animal (tu/fresh-term :type :animal)
        bird   (tu/fresh-term :type :bird)
        peng   (tu/fresh-term :type :penguin)
        food   (tu/fresh-term :type :food)
        eats   (tu/fresh-term :predicate :eats)
        flies  (tu/fresh-term :predicate :flies)
        likes  (tu/fresh-term :predicate :likes)
        ctx    (tu/fresh-term :context :Story)]
    (v/assert kb (list 'genlCx ctx 'CxCore) 'CxUniverse)
    (v/assert kb (list 'genl bird animal) ctx)
    (v/assert kb (list 'genl peng bird) ctx)
    (v/assert kb (list 'comment peng "A flightless bird.") ctx)
    (v/assert kb (list 'binaryPredicate eats) ctx)
    (v/assert kb (list 'argIsa eats 1 animal) ctx)
    (v/assert kb (list 'argIsa eats 2 food) ctx)
    (v/assert kb (list 'unaryPredicate flies) ctx)
    (v/assert kb (list 'argIsa flies 1 animal) ctx)
    ;; declared binary, but argIsa constrains only argument 1 — the arity trap
    (v/assert kb (list 'binaryPredicate likes) ctx)
    (v/assert kb (list 'argIsa likes 1 animal) ctx)
    {:animal animal :bird bird :penguin peng :food food
     :eats eats :flies flies :likes likes :ctx ctx
     :rule (v/assert kb (list 'implies (list 'and (list peng '?x))
                              (list 'not (list flies '?x)))
                     ctx)}))

;; ---- where the vocabulary comes from ------------------------------------

(tu/deftest-kb arity-comes-from-the-declarations-never-from-argisa
  (let [{:keys [likes eats flies]} (world kb)
        arities (inv/declared-arities kb)]
    (testing "a relation whose argIsa constrains only argument 1 is still binary"
      (is (= 2 (arities likes))
          "argIsa is deliberately partial — its highest position is a lower bound on arity")
      (is (= 2 (arities eats)))
      (is (= 1 (arities flies))))
    (testing "and the rendered signature says 2, with ? for the unconstrained position"
      (let [line (inv/predicate-line (inv/predicate-shape kb likes (arities likes)) 80)]
        (is (str/includes? line (str likes "`/2")))
        (is (str/includes? line "× ?"))))))

(tu/deftest-kb an-undeclared-predicate-gets-no-guessed-arity
  (let [p (tu/fresh-term :predicate :smells)
        ctx (tu/fresh-term :context :Story)
        t (tu/fresh-term :type :animal)]
    (v/assert kb (list 'genlCx ctx 'CxCore) 'CxUniverse)
    (v/assert kb (list 'argIsa p 1 t) ctx)
    (is (nil? (get (inv/declared-arities kb) p)))
    (testing "the shape falls back to a stored fact's arity, which is ground truth"
      (is (nil? (:arity (inv/predicate-shape kb p nil))))
      (v/assert kb (list p 'Muffet 'Roses) ctx)
      (is (= 2 (:arity (inv/predicate-shape kb p nil)))))))

(tu/deftest-kb the-inventory-is-sourced-from-declarations-not-facts
  (let [{:keys [penguin eats flies likes bird animal]} (world kb)
        i (inv/inventory kb penguin)
        preds (set (map :predicate (:relations i)))]
    (testing "a declared relation appears with no fact ever using it"
      (is (contains? preds eats))
      (is (contains? preds flies))
      (is (contains? preds likes)))
    (testing "the neighbourhood's types are there to reuse, nearest first"
      (let [ts (map :type (:types i))]
        (is (= penguin (first ts)))
        (is (every? (set ts) [bird animal]))))
    (testing "and each type carries its nearest supertype, so the block is the hierarchy"
      (is (= bird (:parent (first (filter #(= penguin (:type %)) (:types i)))))))))

(tu/deftest-kb structural-vocabulary-is-a-small-allowlist-not-the-whole-head
  (let [{:keys [penguin]} (world kb)
        i (inv/inventory kb penguin)
        domain (set (map :predicate (:relations i)))
        structural (map :predicate (:structural i))]
    (testing "the type-level structural predicates are offered"
      (is (= '[genl disjoint comment argIsa] (vec structural))))
    (testing "and the rest of the head's vocabulary is not — a penguin page has no use for it"
      (is (not-any? domain '#{genlCx lessThan evaluate rewriteOf forcedDecontextualizedPredicate}))
      (is (not-any? (set structural) '#{genlCx lessThan evaluate})))
    (testing "nor are the head's own types offered as type names"
      (is (not-any? (set (map :type (:types i))) '#{predicate unaryPredicate binaryPredicate})))))

(tu/deftest-kb a-lowercase-word-is-typed-by-the-kb-not-by-its-spelling
  (let [{:keys [penguin eats flies]} (world kb)]
    (testing "genl edges make it a type, whatever the spelling admits"
      (is (= :type (inv/term-kind kb penguin))))
    (testing "argIsa constraints make it a relation"
      (is (= :predicate (inv/term-kind kb eats)))
      (is (= :predicate (inv/term-kind kb flies))))
    (is (= :individual (inv/term-kind kb 'Muffet)))
    (is (= :context (inv/term-kind kb 'CxWell)))))

(tu/deftest-kb the-card-is-bounded-by-tokens-and-says-what-it-cut
  (let [{:keys [penguin]} (world kb)
        i (inv/inventory kb penguin)
        whole (inv/render i)
        cut (inv/render i {:max-tokens 40})]
    (is (> (count whole) (count cut)))
    (is (str/includes? cut "not listed here"))))

(tu/deftest-kb the-scan-bound-is-counted-rather-than-silent
  ;; the fact scan is the only tier that reads facts, so a predicate used with the term and
  ;; never declared is on the card because that scan reached it — and off the card
  ;; altogether when it did not, since no later tier looks for it.  A cut nobody is shown
  ;; reads as the whole of the vocabulary.
  (let [{:keys [ctx]} (world kb)]
    (tu/with-terms [Tux fedBy]
      (doseq [w (repeatedly 5 #(tu/fresh-term :individual :Who))]
        (v/assert kb (list fedBy Tux w) ctx))
      (testing "scanned, the undeclared predicate is on the card and nothing went unread"
        (let [i (inv/inventory kb Tux {:max-scan 5})]
          (is (some #(= fedBy (:predicate %)) (:relations i)))
          (is (zero? (:unscanned (:dropped i))))))
      (testing "unscanned, it is offered nowhere else — and the card says how much it did not read"
        (let [i (inv/inventory kb Tux {:max-scan 0})]
          (is (not-any? #(= fedBy (:predicate %)) (:relations i))
              "never declared and never argIsa'd, so the later tiers cannot demote it")
          (is (= 5 (:unscanned (:dropped i))))
          (is (str/includes? (inv/render i) "did not read 5 further facts")))))))

(tu/deftest-kb a-position-two-contexts-declare-reads-as-the-narrower-one
  ;; a term has to satisfy both declarations to stand in the position, so the narrower one
  ;; is what the card should state — `animal` says less than `bird` about what belongs
  ;; there, and the alphabet is not what decides between them.
  (let [{:keys [animal bird ctx]} (world kb)]
    (tu/with-terms [chases CxOther]
      (v/assert kb (list 'genlCx CxOther 'CxCore) 'CxUniverse)
      (v/assert kb (list 'binaryPredicate chases) ctx)
      (v/assert kb (list 'argIsa chases 1 animal) ctx)
      (v/assert kb (list 'argIsa chases 1 bird) CxOther)
      (v/assert kb (list 'argIsa chases 2 animal) ctx)
      (let [shape (inv/predicate-shape kb chases 2)]
        (is (= [[1 bird] [1 animal] [2 animal]] (:args shape)) "narrowest first, within a position")
        (is (= (str "2 : `" bird "` × `" animal "`") (inv/signature shape))
            "and the signature prints the first of a position, which is now the informative one"))
      (is (= bird (first (:arg-types (inv/seed-types kb chases))))
          "the predicate page's own neighbourhood ranks it the same way"))))

;; ---- the coining flag: the only guard against fragmentation -------------

(tu/deftest-kb coining-is-reported-with-arity-and-role
  (let [{:keys [penguin ctx]} (world kb)
        batch {:add [[(list 'implies (list penguin '?x) (list 'lives_in_ice '?x)) ctx]
                     [(list 'implies (list penguin '?x) (list 'capableOf '?x 'Swimming)) ctx]]
               :remove []}
        {:keys [coined vocabulary]} (session/coined kb batch)
        by-name (into {} (map (juxt :predicate identity) coined))]
    (testing "a coined one-place property is reported as a unary type"
      (is (= 1 (:arity (by-name 'lives_in_ice))))
      (is (= :type (:role (by-name 'lives_in_ice)))))
    (testing "a coined relation is reported with its arity, which is the reviewer's question"
      (is (= 2 (:arity (by-name 'capableOf))))
      (is (= :predicate (:role (by-name 'capableOf)))))
    (testing "the entry it came from is named, so a caller can point at the line"
      (is (= [:add 0] ((juxt :in :index) (by-name 'lives_in_ice))))
      (is (= [:add 1] ((juxt :in :index) (by-name 'capableOf)))))
    (testing "and the proposal is counted, which says conservative or inventive at a glance"
      (is (= {:literals 4 :reused 2 :coined 2 :coined-types 1 :coined-relations 1}
             vocabulary)))))

(tu/deftest-kb the-check-chain-admits-what-only-the-coining-flag-sees
  (let [{:keys [penguin ctx]} (world kb)
        batch {:add [[(list 'implies (list penguin '?x) (list 'has_black_and_white_feathers '?x)) ctx]
                     [(list 'implies (list penguin '?x) (list 'capable_of_swimming '?x)) ctx]
                     [(list 'implies (list penguin '?x) (list 'thermoregulates_via_blubber '?x)) ctx]]
               :remove []}]
    (testing "three fragmenting assertions, and the writer's own checks have no objection"
      (is (empty? (session/check-batch kb batch))
          "a unary snake_case functor is a legal type name and always will be"))
    (testing "so the coining flag is the only thing that sees them"
      (let [{:keys [coined vocabulary]} (session/coined kb batch)]
        (is (= 3 (count coined)))
        (is (= 3 (:coined-types vocabulary)))
        (is (zero? (:coined-relations vocabulary)))))))

(tu/deftest-kb known-vocabulary-is-not-reported-and-neither-is-the-frame
  (let [{:keys [penguin eats flies ctx food]} (world kb)
        batch {:add [[(list 'implies (list penguin '?x) (list 'not (list flies '?x))) ctx]
                     [(list 'implies (list penguin '?x) (list eats '?x food)) ctx]
                     [(list 'genl penguin 'thing) ctx]]
               :remove []}
        {:keys [coined vocabulary]} (session/coined kb batch)]
    (is (empty? coined))
    (testing "implies / and / not are frame, so they never count as vocabulary at all"
      (is (= 5 (:literals vocabulary)) "penguin, flies, penguin, eats, genl"))
    (testing "a declared-but-never-used predicate counts as known — the KB has seen it"
      (is (empty? (:coined (session/coined kb {:add [[(list eats 'Tom food) ctx]] :remove []})))))))

(tu/deftest-kb a-removal-cannot-coin-anything
  ;; "nothing was coined" is true of a batch that could not coin in the first place —
  ;; a `:remove` entry is a *handle*, and the test above already says a declared
  ;; predicate is never reported.  So the claim is checked as a difference: an `:add`
  ;; that genuinely coins, and the same report with removals beside it.
  (let [{:keys [rule ctx]} (world kb)]
    (tu/with-terms [novelOf Subject]
      (let [add   [[(list novelOf Subject) ctx]]
            alone (session/coined kb {:add add :remove []})
            with  (session/coined kb {:add add :remove [rule]})]
        (is (= [novelOf] (mapv :predicate (:coined alone)))
            "the add coins — without that the comparison below is two empties")
        (is (= alone with)
            "a removal changed the report: neither the coined list nor the counts may move")
        (testing "and a removal-only batch has nothing to say at all"
          (is (= {:coined []
                  :vocabulary {:literals 0 :reused 0 :coined 0
                               :coined-types 0 :coined-relations 0}}
                 (session/coined kb {:add [] :remove [rule]}))))))))

;; ---- what the page shows the model -------------------------------------

(tu/deftest-kb the-page-shows-bare-sentences-with-the-authors-variables
  (let [{:keys [penguin flies]} (world kb)
        rows (page/stored-lines kb penguin)
        lines (map :line rows)]
    (testing "a rule reads in the author's variable names, not the canonical numbering"
      (is (some #(str/includes? % "?x") lines))
      (is (not-any? #(str/includes? % "?var0") lines)))
    (testing "no context rides along — the answer shape has none either"
      (is (not-any? #(str/starts-with? % "[") lines)))
    (is (some #(str/includes? % (str flies)) lines))))

(tu/deftest-kb the-exceptwhen-meta-sentex-is-never-shown
  (let [{:keys [penguin flies bird ctx]} (world kb)]
    (v/assert kb (list 'exceptWhen (list penguin '?x)
                       (list 'set/defaultRule
                             (list 'implies (list 'and (list bird '?x)) (list flies '?x))))
              ctx)
    (testing "it names its rule by raw handle — meaningless to a model, and imitable"
      (is (not-any? #(str/includes? (:line %) "sentexHandle")
                    (page/stored-lines kb penguin))))))

(tu/deftest-kb the-cap-takes-the-content-first-lines-not-the-first-stored
  ;; the block is capped, so which lines the model is shown is a content choice — and the
  ;; term index answers with a set of handles, so a cap applied ahead of the sort would
  ;; show whichever facts the scan happened to lift.  Asserted in reverse of content order,
  ;; so the two rankings disagree at every position and a scan-ordered cut takes the
  ;; other end of the batch.
  (let [{:keys [penguin likes ctx]} (world kb)
        sens (mapv #(list likes % penguin)
                   (repeatedly 20 #(tu/fresh-term :individual :Who)))]
    (doseq [s (reverse (sort-by pr-str sens))] (v/assert kb s ctx))
    (let [all   (page/stored-lines kb penguin {:max-lines 1000})
          three (page/stored-lines kb penguin {:max-lines 3})]
      (is (= (sort (map :line all)) (map :line all)) "the full list is content-ordered")
      (is (= 3 (count three)))
      (is (= (take 3 (map :line all)) (map :line three))
          "the content-first three, whatever order they were written in"))))

(tu/deftest-kb the-same-knowledge-in-two-orders-gives-one-page
  ;; handles are allocated in assertion order, so a page cut on anything but content would
  ;; be a function of how the knowledge was loaded rather than of what it says.  Below the
  ;; scan bound everything the term is mentioned in is fetched and the cut is by content,
  ;; so two loads of one body of knowledge agree line for line.  Each load is torn down
  ;; before the next, so the second is asserting the same sentences at different handles.
  (let [{:keys [likes ctx]} (world kb)]
    (tu/with-terms [Tux]
      (let [sens    (mapv #(list likes Tux %) (repeatedly 12 #(tu/fresh-term :individual :Who)))
            page-of (fn [order]
                      (let [hs (mapv #(v/assert kb % ctx) order)
                            ls (mapv :line (page/stored-lines kb Tux {:max-lines 5}))]
                        (doseq [h (flatten hs)] (v/retract! kb h))
                        ls))
            loaded  (page-of sens)]
        (is (= 5 (count loaded)) "the cap bit, so the two loads have something to disagree about")
        (is (= loaded (page-of (reverse sens))))
        (is (= loaded (page-of (shuffle sens))))))))

(tu/deftest-kb the-scan-bound-samples-the-terms-earliest-mentions
  ;; the term index answers with a *set*, so a scan taking whatever it enumerated first
  ;; samples the term's knowledge by hash of handle — an order no reader can name and one
  ;; that moves with the index's representation.  Sorted, the sample is the mentions
  ;; recorded first: one answer per KB, on every backend and every read.
  (let [{:keys [likes ctx]} (world kb)]
    (tu/with-terms [Tux]
      (let [sens (mapv #(list likes Tux %) (repeatedly 20 #(tu/fresh-term :individual :Who)))]
        (doseq [s sens] (v/assert kb s ctx))
        (is (= 20 (count (v/find-sentexes kb Tux))) "nothing else mentions the term")
        (let [rows (page/stored-lines kb Tux {:max-lines 1000 :max-scan 6})]
          (is (true? (:truncated? (meta rows))))
          (is (= (sort (map pr-str (take 6 sens))) (map :line rows))
              "the six recorded first, read out in content order"))))))

(tu/deftest-kb a-page-shown-a-sample-is-told-it-is-one
  ;; a bare count of what is on screen reads as the whole of what is stored, and the same
  ;; prompt asks the model not to repeat anything already there
  (let [{:keys [penguin likes ctx]} (world kb)]
    (doseq [s (mapv #(list likes % penguin)
                    (repeatedly 12 #(tu/fresh-term :individual :Who)))]
      (v/assert kb s ctx))
    (testing "everything shown, and the heading claims nothing else"
      (let [rows (page/stored-lines kb penguin {:max-lines 1000})]
        (is (false? (:truncated? (meta rows))))
        (is (= (str (count rows)) (page/stored-heading rows)))))
    (testing "cut by the line cap: how many there were, and no more claimed than that"
      (let [rows (page/stored-lines kb penguin {:max-lines 4})]
        (is (= 4 (count rows)))
        (is (false? (:truncated? (meta rows))))
        (is (= (str "4 of " (:found (meta rows))) (page/stored-heading rows)))
        (is (str/includes? (page/user-turn kb penguin rows ctx "flesh it out")
                           (str "4 of " (:found (meta rows)))))))
    (testing "cut by the scan bound too: the count found is a floor, and says so"
      (let [rows (page/stored-lines kb penguin {:max-lines 4 :max-scan 6})]
        (is (true? (:truncated? (meta rows))))
        (is (= (str "4 of more than " (:found (meta rows))) (page/stored-heading rows)))))
    (testing "rows built without the metadata still get a plain count"
      (is (= "2" (page/stored-heading [{:line "(a)"} {:line "(b)"}]))))))

(tu/deftest-kb the-page-context-is-modal-and-never-the-vocabulary-head
  (let [{:keys [penguin ctx]} (world kb)
        rows (page/stored-lines kb penguin)]
    (is (= ctx (page/page-context rows nil)) "where the term's own sentexes are")
    (is (= 'CxWell (page/page-context rows 'CxWell)) "the caller always wins")
    (testing "the head is excluded — derived bookkeeping there can outnumber the definitions"
      (is (= 'CxUniverse
             (page/page-context [{:context inv/head-context} {:context inv/head-context}] nil))))
    (is (= 'CxUniverse (page/page-context [] nil)))))

(tu/deftest-kb the-prompt-shows-the-failure-and-the-fix
  (testing "telling a model to use arguments is not enough — the wrong answer is shown too"
    (is (str/includes? page/system-prompt "(implies (bat ?x) (lives_in_caves ?x))"))
    (is (str/includes? page/system-prompt "(implies (bat ?x) (livesIn ?x Cave))")))
  (testing "and the two things the critic would otherwise reject are stated"
    (is (str/includes? page/system-prompt "?x` is the only variable"))
    (is (str/includes? page/system-prompt "Write no context"))))

;; ---- reading the answer -------------------------------------------------

(tu/deftest-kb the-scanner-yields-each-sexp-as-its-closing-paren-arrives
  (let [feed (fn [deltas]
               (loop [st session/scan-init out [] [d & more] deltas]
                 (if (nil? d)
                   out
                   (let [[st' done] (session/scan st d)]
                     (recur st' (into out done) more)))))]
    (testing "split across deltas, one at a time"
      (is (= ["(genl penguin bird)" "(flies Tux)"]
             (feed ["(genl pen" "guin bird)" " and then (flies" " Tux)"]))))
    (testing "nested parens close once, at the outermost"
      (is (= ["(implies (penguin ?x) (flies ?x))"]
             (feed ["(implies (penguin ?x) (flies ?x))"]))))
    (testing "and it reads straight out of the JSON envelope, where the sentence is a string"
      (is (= ["(genl penguin bird)"]
             (feed [(json/generate-string {"assertions" [{"sentence" "(genl penguin bird)"}]})]))))))

(tu/deftest-kb parse-assertions-reads-the-envelope-the-lines-and-the-fence
  (testing "the contract: the constrained-decoding envelope"
    (let [{:keys [sentences notes]}
          (session/parse-assertions
           (json/generate-string {"assertions" [{"sentence" "(genl penguin bird)"}
                                                {"sentence" "(flies Tux)" "strength" "monotonic"}]
                                  "notes" "unsure about Tux"}))]
      (is (= '[(genl penguin bird) (flies Tux)] (map :sentence sentences)))
      (is (= :monotonic (:strength (second sentences))))
      (is (= "unsure about Tux" notes))))
  (testing "bare lines, for a model that ignores the schema"
    (let [{:keys [sentences notes]}
          (session/parse-assertions "Here you go:\n(genl penguin bird)\n- (flies Tux)")]
      (is (= '[(genl penguin bird) (flies Tux)] (map :sentence sentences)))
      (is (str/includes? notes "Here you go"))))
  (testing "and a fence around either"
    (is (= '[(genl penguin bird)]
           (map :sentence (:sentences (session/parse-assertions
                                       "```\n(genl penguin bird)\n```"))))))
  (testing "an answer with nothing readable is an error, not an empty answer"
    (is (seq (:errors (session/parse-assertions "Penguins are birds that cannot fly.")))))
  (testing "a line that starts like a sentence and does not read is a reported problem"
    (let [{:keys [sentences problems]} (session/parse-assertions "(genl penguin bird)\n(flies")]
      (is (= 1 (count sentences)))
      (is (= 1 (count problems)))))
  (testing "and reading cannot evaluate code"
    (is (seq (:errors (session/parse-assertions "(#=(clojure.core/println \"pwned\"))"))))))

(tu/deftest-kb an-assertion-already-stored-is-not-proposed-again
  (let [{:keys [penguin bird ctx]} (world kb)
        split (session/new-assertions kb ctx [{:sentence (list 'genl penguin bird)}
                                              {:sentence (list 'genl penguin 'thing)}
                                              {:sentence (list 'genl penguin 'thing)}])]
    (is (= [(list 'genl penguin 'thing) ctx] (first (:entries split))))
    (is (= 1 (count (:entries split))))
    (is (= [(list 'genl penguin bird)] (:known split)) "re-asserting is a no-op, so it is noise")
    (is (= 1 (count (:duplicates split))))
    (is (= {:proposed 3 :new 1 :known 1 :duplicate 1}
           (session/assertion-summary [1 2 3] split)))))

;; ---- propose-page, end to end against the stub -------------------------

(tu/deftest-kb propose-page-answers-a-reviewable-batch-in-the-callers-context
  (let [{:keys [penguin bird ctx eats food]} (world kb)
        p (stub/provider {:script [{:assertions [(list 'genl penguin bird)
                                                 (list 'implies (list penguin '?x) (list eats '?x food))]
                                    :notes "reused what was on the card"}]})
        r (session/propose-page kb {:term penguin :context ctx :provider p
                                    :message "flesh out the capabilities of this"})]
    (is (= :ok (:status r)))
    (is (= ctx (:context r)))
    (is (= [[(list 'implies (list penguin '?x) (list eats '?x food)) ctx]] (:add (:batch r)))
        "the stored genl edge is not proposed again")
    (is (empty? (:remove (:batch r))) "generation never removes")
    (is (= {:proposed 2 :new 1 :known 1 :duplicate 0} (:summary r)))
    (is (= "reused what was on the card" (:notes r)))
    (is (empty? (:coined r)))
    (testing ":lines is what a browser panel drops into the editor — entries, with context"
      (is (= 1 (count (str/split-lines (:lines r))))))
    (testing "and it reports where it got to"
      (is (number? (:first-assertion-ms r)))
      (is (number? (:elapsed-ms r))))))

(tu/deftest-kb propose-page-writes-nothing
  (let [{:keys [penguin ctx]} (world kb)
        before (set (map :id (v/sentexes-in-context kb ctx)))
        p (stub/provider {:script [{:assertions [(list 'genl penguin 'thing)]}]})
        r (session/propose-page kb {:term penguin :context ctx :provider p :message "x"})]
    (is (= :ok (:status r)))
    (is (seq (:add (:batch r))))
    (is (= before (set (map :id (v/sentexes-in-context kb ctx)))) "…and none of it happened")
    (testing "applying is the separate explicit call"
      (session/apply-proposal! kb r)
      (is (seq (v/sentexes-matching kb (list 'genl penguin 'thing) ctx))))))

(tu/deftest-kb each-assertion-is-handed-over-as-it-completes
  (let [{:keys [penguin bird ctx]} (world kb)
        evs (atom [])
        p (stub/provider {:script [{:assertions [(list 'genl penguin bird)
                                                 (list 'genl penguin 'thing)]}]})
        r (session/propose-page kb {:term penguin :context ctx :provider p :message "x"
                                    :on-event #(when (= :assertion (:type %)) (swap! evs conj %))})]
    (is (= :ok (:status r)))
    (is (= 2 (count @evs)) "one event per assertion, not one at the end")
    (let [[a b] @evs]
      (is (= (list 'genl penguin bird) (:sentence a)))
      (is (true? (:stored? a)) "the reader sees at once that this one is not news")
      (is (nil? (:problem a)))
      (is (= [(list 'genl penguin 'thing) ctx] (:entry b))))))

(tu/deftest-kb the-critic-runs-on-the-page-path-too
  (let [{:keys [penguin ctx]} (world kb)
        bad (list 'implies (list penguin '?x) (list 'NotAPredicate '?x))
        p (stub/provider {:script (repeat 3 {:assertions [bad]})})
        r (session/propose-page kb {:term penguin :context ctx :provider p :message "break it"})]
    (is (= :invalid (:status r)))
    (is (= :naming (:type (first (:rejections r)))))
    (testing "and the rejection was fed back before giving up"
      (is (= 2 (:attempts r)))
      (is (str/includes? (stub/last-user-text p) "naming")))))

(tu/deftest-kb an-unreadable-answer-is-repaired-then-reported
  (let [{:keys [penguin ctx]} (world kb)
        p (stub/provider {:script ["no sentences here" "still none"]})
        r (session/propose-page kb {:term penguin :context ctx :provider p :message "x"})]
    (is (= :unparseable (:status r)))
    (is (= 2 (:attempts r)))))

(tu/deftest-kb a-page-turn-needs-a-term
  (let [p (stub/provider {})
        r (session/propose-page kb {:term nil :message "x" :provider p})]
    (is (= :no-term (:status r)))
    (is (empty? (stub/requests p)))))

(tu/deftest-kb an-oversized-page-sends-nothing
  (let [{:keys [penguin ctx]} (world kb)
        p (stub/provider {})
        r (session/propose-page kb {:term penguin :context ctx :provider p :message "x"
                                    :num-ctx 64})]
    (is (= :too-large (:status r)))
    (is (neg? (:headroom (:budget r))))
    (is (empty? (stub/requests p)))))

(tu/deftest-kb decoding-is-constrained-by-default-on-this-path
  (let [{:keys [penguin bird ctx]} (world kb)
        p (stub/provider {:script (repeat 2 {:assertions [(list 'genl penguin bird)]})})
        _ (session/propose-page kb {:term penguin :context ctx :provider p :message "x"})
        req (first (stub/requests p))]
    (is (= page/output-schema (:format req))
        "constrained decoding rescues generation, so it is the contract here")
    (testing "and a caller can still send none"
      (let [p2 (stub/provider {:script [{:assertions [(list 'genl penguin bird)] :lines? true}]})]
        (session/propose-page kb {:term penguin :context ctx :provider p2 :message "x"
                                  :format nil})
        (is (nil? (:format (first (stub/requests p2)))))))))

(tu/deftest-kb the-user-turn-carries-the-page-the-card-and-the-instruction
  (let [{:keys [penguin bird ctx eats]} (world kb)
        p (stub/provider {:script [{:assertions [(list 'genl penguin bird)]}]})
        _ (session/propose-page kb {:term penguin :context ctx :provider p
                                    :message "flesh out the capabilities of this"})
        text (:content (first (:messages (first (stub/requests p)))))]
    (is (str/includes? text (str "The page: `" penguin "`")))
    (is (str/includes? text (str ctx)) "the context new assertions land in is stated")
    (is (str/includes? text (str eats)) "the declared relation is on the card to reuse")
    (is (str/includes? text "flesh out the capabilities of this"))))

;; ---- the local backend's latency levers --------------------------------

(tu/deftest-kb every-request-holds-the-model-resident
  (let [b (ollama/body {:messages [{:role "user" :content "hi"}]} {:stream? false})]
    (is (= (ollama/configured-keep-alive) (get b "keep_alive"))
        "model load is the whole latency of a local turn, so keep_alive is never omitted"))
  (is (= "5m" (get (ollama/body {:messages [] :keep-alive "5m"} {:stream? false}) "keep_alive"))))

(tu/deftest-kb the-two-paths-default-to-different-models
  (testing "editing and generating are different jobs"
    (is (not= (ollama/configured-model) (ollama/configured-generation-model)))))

;; ---- live: a real Ollama -----------------------------------------------

(defn- live-model
  "The generation model to run against, or nil with a printed reason.  Opting in is
  checked first, before the host is so much as probed."
  []
  (let [model (ollama/configured-generation-model)]
    (cond
      (not (tu/live-llm?))
      (do (println "  [skip] live page tests: set VAELII_LLM_LIVE=1 to opt in") nil)

      (not (ollama/available? {:timeout-ms 2000}))
      (do (println (str "  [skip] live page tests: no server at " (ollama/base-url))) nil)

      (nil? (ollama/capabilities model))
      (do (println (str "  [skip] live page tests: " (ollama/base-url) " has no model " model
                        " — set VAELII_OLLAMA_GENERATION_MODEL"))
          nil)

      :else model)))

(tu/deftest-kb ^:llm a-live-model-fleshes-out-a-page
  (when-let [model (live-model)]
    (let [{:keys [penguin ctx]} (world kb)
          _ (ollama/warm model)
          p (ollama/provider {:model model})
          r (session/propose-page
             kb {:term penguin :context ctx :provider p
                 :message "flesh out what is true of these — where they live, what they eat"})]
      (println (format "  [live] %s: ttfa %sms, total %sms, %s assertions, reuse %s/%s, coined %s"
                       model (:first-assertion-ms r) (:elapsed-ms r) (:new (:summary r))
                       (:reused (:vocabulary r)) (:literals (:vocabulary r))
                       (:coined (:vocabulary r))))
      (is (contains? #{:ok :invalid} (:status r))
          (str "unexpected status " (:status r) " — " (pr-str (:text r))))
      (is (pos? (:proposed (:summary r))) "it wrote something")
      (is (number? (:first-assertion-ms r)))
      (testing "the answer is type-level knowledge in this context"
        (is (every? #(= ctx (second %)) (:add (:batch r)))))
      (testing "and it reused the vocabulary the card offered"
        (is (pos? (:reused (:vocabulary r)))))
      (testing "proposing still writes nothing"
        (is (empty? (v/sentexes-matching kb (list 'genl penguin 'thing) ctx)))))))

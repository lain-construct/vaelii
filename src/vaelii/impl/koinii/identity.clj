;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.koinii.identity
  "Koinii actor identity: per-agent contexts as the identity substrate AND the
  write boundary, an admin-only agent registry, and the one auth seam whose strength
  is conditional on the adjudication policy.

  The engine deliberately pushes per-caller identity OUT — `*creator*` is an
  unauthenticated annotation and the daemon's only auth is one shared bearer token —
  so koinii's answer is the context lattice, not a new auth subsystem:

  - **An agent IS its context.**  Atlas writes into `CxAtlas`, lifted under the
    channel by `(genlCx CxDeploy CxAtlas)`.  A reader of `CxDeploy` sees the union of
    every agent's assertions; `CxAtlas` alone is 'everything Atlas said' — a plain
    context read.  Because context is part of sentex identity, Atlas's `P` and
    Boreas's `P` are two DISTINCT sentexes, each with its own creator, so
    first-writer-wins loses no co-source (`co-attribution-survives?`).
  - **The write boundary is 'your own context, and nothing else.'**  That is the one
    enforcement point identity needs, and it is why the registry context is the one
    context agents may NOT write — the governed may not write the authority that
    governs them.

  The auth seam is conditional on policy (koinii design D4):

  - **Cooperative** (the default) — `*creator*` bound by convention, the write routed
    to the agent's own context, trusted because the agents are.  Correct for a
    notify-only deployment.  It defends fat-fingers, NOT attackers: `authenticate`
    trusts the claimed id with no proof, so a client may claim any identity.  State
    plainly that identity is unauthenticated here.
  - **Proof-tier** — REQUIRED the moment trust-resolve is enabled, because
    trust-weighting a spoofable identity is worse than no trust.  `authenticate`
    verifies a credential (the `verify-fn` seam — sign-at-ingest, an authenticating
    proxy, or A2A AgentCards / DIDs) and REFUSES an unverified request; the
    write-boundary is enforced at that same seam.

  Every write goes through the provenance-stamping `assert` path — NEVER
  `bulk-assert-facts!`, which binds `*bulk-load?*` and writes no provenance at all."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [vaelii.core :as v])
  (:import [java.io PushbackReader]))

;; ---- loading a koinii seed context ---------------------------------------
;; koinii ships its own seed KB files under resources/kb/koinii/ and loads them
;; itself, through the public `assert` — the engine's ontology loader only walks
;; upper/ and middle/, and koinii depends on nothing under `vaelii.impl`.

(defn- read-seed
  "Every sentence of koinii's seed KB file for `context`, in file order.  Throws if the
  resource is missing — a silently empty registry is worse than a failure to start."
  [context]
  (let [path (str "kb/koinii/" (name context) ".txt")]
    (if-let [res (io/resource path)]
      (with-open [r (PushbackReader. (io/reader res))]
        (let [eof (Object.)]
          (loop [acc []]
            (let [form (edn/read {:eof eof} r)]
              (if (identical? form eof) acc (recur (conj acc form)))))))
      (throw (ex-info (str "koinii seed KB file not on the classpath: " path)
                      {:type :koinii/missing-seed :context context :resource path})))))

(defn load-seed-context
  "Assert every sentence of koinii's seed KB file for `context` into that context,
  **order-insensitively**: a sentence refused because content further down the file has
  not arrived yet is retried rather than fatal, so the file may be grouped term-centrically
  rather than in dependency order.  The sentences that survive a round changing nothing are
  re-asserted without a catch, so a genuinely ill-formed one still throws.  Returns kb."
  [kb context]
  (let [attempt (fn [ss]
                  (reduce (fn [acc s]
                            (try (v/assert kb s context) acc
                                 (catch clojure.lang.ExceptionInfo _ (conj acc s))))
                          [] ss))]
    (loop [pending (attempt (read-seed context))]
      (when (seq pending)
        (let [remaining (attempt pending)]
          (if (< (count remaining) (count pending))
            (recur remaining)
            (doseq [s remaining] (v/assert kb s context)))))))
  kb)

(defn load-registry
  "Load the CxRegistry vocabulary into `kb` from resources/kb/koinii/CxRegistry.txt.
  Koinii KB files are not auto-discovered (the starter only walks upper/ and
  middle/), so this explicit loader is how the registry context comes into being.
  Requires CxCore already loaded (CxRegistry wires `(genlCx CxRegistry CxCore)`).
  Returns kb."
  [kb]
  (load-seed-context kb 'CxRegistry))

;; ---- per-agent contexts: the identity substrate + write boundary ---------

(defn context-for
  "The per-agent context for `agent-id`, by convention: `AgentAtlas` -> `CxAtlas`
  (a leading `Agent` is dropped, then `Cx`-prefixed).  The destination of an agent's
  writes is a DETERMINISTIC function of its authenticated id, so 'write only your own
  context' needs no separate lookup — identity fixes the destination, and a principal
  can never be routed to a context that is not its own."
  [agent-id]
  (let [n    (name agent-id)
        base (if (str/starts-with? n "Agent") (subs n (count "Agent")) n)]
    (symbol (str "Cx" base))))

(def registry-context
  "The admin-only registry context.  The one context governed agents may not write."
  'CxRegistry)

(defn agent-context
  "Create/lift `agent-id`'s per-agent context under the channel `deploy-ctx` so the
  channel sees it — `(genlCx deploy-ctx CxAtlas)` — and root it under `CxCore` so the
  agent speaks the core vocabulary.  Both edges are monotonic topology.  Returns the
  agent context symbol."
  [kb deploy-ctx agent-id]
  (let [actx (context-for agent-id)]
    (v/assert kb (list 'genlCx deploy-ctx actx) 'CxUniverse {:strength :monotonic})
    (v/assert kb (list 'genlCx actx 'CxCore)    'CxUniverse {:strength :monotonic})
    actx))

;; ---- the auth seam: authenticate a principal (policy-conditional) --------

(def ^:dynamic *policy*
  "The identity policy (koinii design D4).

  - `:cooperative` (the default) — `*creator*` is trusted by convention; correct for
    a notify-only deployment.  It defends fat-fingers, not attackers: a client may
    claim any id, and there is no barrier to impersonation.
  - `:proof-tier` — REQUIRED once trust-resolve is enabled; a credential is verified
    at ingest and an unverified request is refused.  Trust-weighting a spoofable
    identity is worse than no trust."
  :cooperative)

(def ^:dynamic *verify-fn*
  "The proof-tier verifier SEAM: `(verify-fn claimed-id credential)` returns truthy
  iff the credential proves the claim.  nil ships no crypto — the design provides the
  seam (sign-at-ingest / an authenticating proxy / A2A AgentCards / DIDs) and the
  deployment wires it.  Under `:proof-tier` a nil verifier fails CLOSED: every
  request is refused rather than silently trusted."
  nil)

(defn authenticate
  "Turn a `request` into an authenticated principal, or refuse — the identity seam,
  behaviour CONDITIONAL ON POLICY.

  `request` is `{:claimed-id <agent-id> :credential <opaque> :source <str>}`.
  `opts` may override `{:policy … :verify-fn …}` (defaulting to `*policy*` /
  `*verify-fn*`).  Returns a principal
  `{:id :context :source :policy :authenticated?}` whose `:context` is
  `(context-for :id)` — derived, never client-supplied.

  - `:cooperative` — trust the claimed id; `:authenticated? false` records that the
    identity is UNVERIFIED (the documented cooperative gap).
  - `:proof-tier` — require a `verify-fn` and a passing credential; otherwise throw
    `:koinii/identity-unverified`.  THIS is where a client is stopped from stamping
    another agent's identity on its own write."
  ([request] (authenticate request nil))
  ([request opts]
   (let [policy (get opts :policy *policy*)
         verify (get opts :verify-fn *verify-fn*)
         id     (:claimed-id request)
         base   {:id id :context (context-for id) :source (:source request)}]
     (case policy
       :cooperative (assoc base :policy :cooperative :authenticated? false)
       :proof-tier  (if (and verify (verify id (:credential request)))
                      (assoc base :policy :proof-tier :authenticated? true)
                      (throw (ex-info "koinii: identity unverified under proof-tier"
                                      {:type :koinii/identity-unverified
                                       :claimed-id id :policy :proof-tier
                                       :verifier? (boolean verify)})))
       (throw (ex-info (str "koinii: unknown identity policy " (pr-str policy))
                       {:type :koinii/unknown-policy :policy policy}))))))

(defn admin-principal
  "The out-of-band admin principal — the only writer of `CxRegistry`.  Not a governed
  agent: its `:admin?` capability is what the registry write-boundary checks, and it
  is minted here rather than by `authenticate` precisely because it is out of band."
  ([] (admin-principal 'AdminRoot))
  ([admin-id] {:id admin-id :context registry-context :admin? true
               :policy :admin :authenticated? true}))

;; ---- the write boundary --------------------------------------------------

(defn- write-boundary-problem
  "The write-auth violation `principal` would commit writing `target-ctx`, or nil.
  Two rules, one boundary:
  - `CxRegistry` is admin-only — a governed agent writing it is refused
    (`:koinii/registry-forbidden`): the governed may not write the authority.
  - every other context: an agent writes ONLY its own `(context-for :id)` — a write
    aimed elsewhere is refused (`:koinii/foreign-context`)."
  [principal target-ctx]
  (cond
    (= target-ctx registry-context)
    (when-not (:admin? principal)
      {:type :koinii/registry-forbidden :principal (:id principal) :context target-ctx})

    (:admin? principal)
    {:type :koinii/admin-off-registry :principal (:id principal) :context target-ctx}

    (not= target-ctx (context-for (:id principal)))
    {:type :koinii/foreign-context :principal (:id principal)
     :context target-ctx :own (context-for (:id principal))}))

(defn check-write-boundary!
  "Throw if `principal` may not write `target-ctx`; else return nil.  The single
  enforcement point — the seam a proof-tier deployment relies on, and the reason no
  call site can route a write into a context it does not own."
  [principal target-ctx]
  (when-let [prob (write-boundary-problem principal target-ctx)]
    (throw (ex-info (str "koinii: write refused — " (name (:type prob)))
                    prob))))

(defn- principal-provenance
  "The open-provenance fields a principal rides onto its writes — `:source` and the
  identity `:policy` / `:authenticated?` it wrote under.  These are app fields the
  engine never reads (belief is provenance-blind), so a trust hint or a signature ref
  travels here without touching truth maintenance."
  [principal]
  (into {} (remove (comp nil? val))
        {:source (:source principal)
         :policy (:policy principal)
         :authenticated? (:authenticated? principal)}))

(defn- write
  "The one provenance-stamping write chokepoint.  Enforces the write boundary, binds
  `*creator*` to the AUTHENTICATED principal id (a client cannot supply a different
  creator through here), rides its provenance hints in the open map, and goes through
  `v/assert` — never `bulk-assert-facts!`.  Returns the sentex handle."
  [kb principal target-ctx sentence]
  (check-write-boundary! principal target-ctx)
  (binding [v/*creator* (:id principal)]
    (v/assert kb sentence target-ctx {:provenance (principal-provenance principal)})))

;; ---- THE ingest helper: bind identity onto writes ------------------------

(defn ingest
  "The sanctioned everyday write path.  Given an authenticated `principal` (from
  `authenticate`) and a `sentence`, assert it into the agent's OWN context with
  `*creator*` bound to the authenticated id — so no call site can forget either the
  attribution or the routing.  Automatic routing means this form CANNOT name another
  agent's context.  Returns the handle."
  [kb principal sentence]
  (write kb principal (context-for (:id principal)) sentence))

(defn ingest-into
  "The explicit-target write path, for a caller that names `target-ctx` — the write
  goes through the SAME boundary check `ingest` does, so a principal authenticated as
  Boreas targeting `CxAtlas` is refused (`:koinii/foreign-context`) and any governed
  agent targeting `CxRegistry` is refused (`:koinii/registry-forbidden`).  Returns the
  handle."
  [kb principal target-ctx sentence]
  (write kb principal target-ctx sentence))

;; ---- admin-only registry writes ------------------------------------------

(defn register-agent
  "Register `agent-id` in `CxRegistry` — its membership mark, display name, and
  bootstrap trust value — as the admin `principal`.  Refused
  (`:koinii/registry-forbidden`) if `principal` is not admin, so a governed agent
  cannot self-register or self-promote.  Returns the agent id."
  [kb principal agent-id display-name trust]
  (ingest-into kb principal registry-context (list 'agent agent-id))
  (ingest-into kb principal registry-context (list 'displayNameOf agent-id display-name))
  (ingest-into kb principal registry-context (list 'trustLevel agent-id trust))
  agent-id)

(defn set-trust!
  "OVERWRITE `agent-id`'s trust with `new-value`, as the admin `principal` (D3: trust
  is a mutable number).  `trustLevel` is functional, so the update retracts the old
  value and asserts the new rather than accumulating two.  Refused for a non-admin
  principal.  Returns the new handle."
  [kb principal agent-id new-value]
  (check-write-boundary! principal registry-context)      ; admin-gate the retract too
  (when-let [sx (first (v/sentexes-matching kb (list 'trustLevel agent-id '?v) registry-context))]
    (v/retract! kb (:id sx)))
  (ingest-into kb principal registry-context (list 'trustLevel agent-id new-value)))

;; ---- registry reads: queryable ground truth ------------------------------

(defn- object-of
  "The last argument of the believed `(pred subject ?o)` sentex in `CxRegistry`, or
  nil — a plain context-scoped read of one stored fact."
  [kb pred subject]
  (some-> (v/sentexes-matching kb (list pred subject '?o) registry-context)
          first :sentence last))

(defn trust-of
  "The stored trust number for `agent-id`, or nil — a plain context-scoped read of
  `CxRegistry`, ready for adjudication to weigh."
  [kb agent-id]
  (object-of kb 'trustLevel agent-id))

(defn display-name-of
  "The stored display name for `agent-id`, or nil."
  [kb agent-id]
  (object-of kb 'displayNameOf agent-id))

(defn registered-agents
  "Every registered agent id — the extent of `(agent ?a)` in `CxRegistry`.  'Which
  agents exist' as a plain context-scoped read."
  [kb]
  (->> (v/sentexes-matching kb (list 'agent '?a) registry-context)
       (map (comp second :sentence))
       distinct))

(defn co-attribution
  "Every context that independently asserts `sentence` — the set of per-agent contexts
  backing a claim.  Because context is part of sentex identity, an agent re-asserting
  a fact another already stated is a DISTINCT sentex in a DISTINCT context, so
  first-writer-wins provenance loses no co-source: 'how many sources back P' is this
  set, recovered from the per-agent contexts with no separate source index."
  [kb sentence]
  (v/contexts-of kb sentence))

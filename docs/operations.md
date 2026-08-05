# Operational surface

`vaelii.core` is the engine; the operational surface is the set of in-repo interfaces
that *drive* it. There are five:

| Interface | Namespace | Launch | For |
|-----------|-----------|--------|-----|
| Browser | `vaelii.web` | `lein run -m vaelii.web` | reading a KB in a browser |
| CLI | `vaelii.cli` | `lein cli <cmd> …` | driving a KB from a shell |
| Daemon | `vaelii.serve` | `lein serve [port [dir]]` | one process owns a KB, serves it over HTTP |
| Client | `vaelii.client` | *(library)* | talking to a daemon from Clojure |
| Access | `vaelii.impl.access` | *(library)* | a read that resolves to a local KB or a remote daemon |

All five go through `vaelii.core` alone — the same boundary the rest of the repo keeps
([api.md](api.md)). None of them is a separate repo: the
engine does its own storage (the `:disk` backend), so an interface is an in-repo
namespace, not a sibling.

## The single-writer contract

The store allows **one writer per directory** (docs/storage.md); the `:disk` backend
enforces it with a fail-fast file lock. That shapes how the interfaces coexist:

- The **daemon** is the canonical single writer — one JVM owns one KB and every client
  reaches it through that one process. The daemon serializes its ops through one
  monitor, so concurrent client writes apply one at a time.
- The **CLI** with `--dir` takes the same lock, so it and a daemon **cannot own one
  directory at once**. Point them at different directories, or let the daemon own the
  writable KB and give the CLI its own.
- An in-memory KB (no `--dir`) has no lock and no persistence — fine for a REPL session
  or a one-shot check, useless for one-shot commands that expect earlier facts.

## CLI — `vaelii.cli`

```sh
lein cli assert  '(dog Fido)' NaturalWorldContext --dir /var/lib/vaelii
lein cli match   '(dog ?x)'   NaturalWorldContext --dir /var/lib/vaelii   # => [(dog Fido)]
lein cli why     3                                --dir /var/lib/vaelii
lein cli export  /var/backups/vaelii-2026-07     --dir /var/lib/vaelii     # back it up
lein cli repl --starter                                                    # interactive
```

- **Commands:** `assert`, `assert-rule`, `match` (`sentexes-matching`, sentences only),
  `query`, `query?`, `ask`, `prove`, `provable?`, `retract`, `why`, `why-not`, `in`,
  `isa`, `types-of`, `handle-of`, `types`, `contexts`, `conflicts`, `contradictions`,
  `load`, `export`, `repl`. `--depth n` is how the line says how far to expand rules,
  and `query` without one expands none. A sentence is
  written as an EDN string (`'(dog Fido)'`), a context as a symbol, a handle as an
  integer, and a path as itself — an argument that reads as no EDN form is kept as the
  string it already was, which is what `/var/lib/vaelii` is.
- **`load <file>`** reads an EDN vector of `[sentence context]` (or `[sentence context
  opts]`) entries and asserts them in one batch (`with-deferred-settle` — one settle for
  the whole file).
- **`export <dir>`** writes the KB out as a portable dump (`vaelii.core/export!`) and
  prints the writer's summary. `--variant
  records|records+index`, `--compression gzip|xz|none`. The destination must be empty or
  absent; a refusal is printed as `error: …` in the engine's own words, with a non-zero
  exit status — the same message the daemon and the browser report, because none of them
  writes one of its own.
- **Options:** `--dir <path>` selects the durable backend (recovered on open, so it
  persists across invocations); `--memory` (the default) is ephemeral; `--starter` loads
  the shipped schema so you can explore the ontology; `--strength monotonic` marks an
  `assert` known-true.
- **`repl`** holds the KB in-process, so a memory KB accumulates for the session. Each
  line is `<cmd> <edn-forms…>`.

`dispatch` takes args already parsed to data, so the shell (which `edn`-reads each argv
string) and the REPL (which reads forms off the line) share one command table.

## Daemon — `vaelii.serve`

```sh
lein serve 4200 /var/lib/vaelii                    # disk-backed; omit the dir for in-memory
lein serve 4200 /var/lib/vaelii --listen 0.0.0.0   # reachable off-machine (opt-in)
```

- **It binds loopback**, and exposing it is an explicit choice. `POST /op` is the write
  route of the *single writer* and nothing authenticates it, so the default answers only
  the machine it runs on — the same rule the browser holds to ([web.md](web.md)), and the
  more consequential of the two, since the browser edits a KB where this one *is* the
  KB's only writer. Jetty binds every interface when no host is given, so this is a host
  the daemon passes rather than one it omits. `--listen` names an address and logs a
  warning when it is not loopback; put an authenticating reverse proxy in front before
  using it.
- **Wire format is EDN.** A sentence is a symbol s-expression — `(dog Fido)`, `?x` —
  which EDN round-trips losslessly; JSON would mangle the symbols. Bodies are read with
  `clojure.edn/read-string`, which has no reader-eval, so an untrusted body cannot run
  code.
- **The protocol is one endpoint.** `POST /op` with `{:op <keyword> :args [...]}` returns
  `{:ok true :result …}` or `{:ok false :error "…" :type <keyword>}`. `GET /health`
  returns `{:ok true}`. The op is looked up in an **allowlist** (`serve/ops`) of
  `vaelii.core` fns — the KB is supplied by the daemon, so the client sends only the op
  and the remaining args, and no client can reach an arbitrary var.
- **`POST /op` requires `Content-Type: application/edn`** — parameters and case are
  tolerated (`application/edn;charset=utf-8` passes), anything else is refused with 415
  in the same `{:ok false :error … :type …}` shape every refusal carries. The
  requirement is a CSRF guard rather than a parsing one: the type is not CORS-simple,
  so a browser must preflight it, and the daemon answers no CORS headers — which stops
  a page the operator merely visits from driving the write route over loopback. A
  request stamping another site's `Origin` (or `Referer`) is refused with 403, the
  second layer on the same door.
- **Every route answers only a recognised `Host`** — the allowlist follows the
  interface the daemon is bound to, so the loopback default answers only loopback
  names, which is what closes DNS rebinding; an unrecognised `Host` gets 400.
  `VAELII_ALLOWED_HOSTS` (comma-separated) overrides the list — a reverse proxy
  preserving the original `Host`, or a local alias name, needs it. A request with
  **no** `Host` header passes: every browser sends one, so its absence marks a
  non-browser client with no ambient browser context to ride. Binding to an address
  with `--listen` drops the allowlist (the name you reach it by is then yours to
  know); set `VAELII_ALLOWED_HOSTS` to keep the check.
- **A body over 16 MiB is refused** with 413 before it reaches the heap. An op body is a
  sentence and its context, so the ceiling is nowhere near a legitimate call — it is
  there so an unauthenticated caller cannot spend the daemon's heap by streaming one.
  The cap and its `VAELII_MAX_BODY_BYTES` override are `vaelii.impl.guard`'s
  (`max-body-bytes`, `wrap-body-limit`), not this namespace's, because the browser has
  the same exposure through a form body and reads the same number — one ceiling, two
  servers ([web.md](web.md)).
- **A read is realized under the write monitor.** Projecting the answer for the wire is
  what realizes a lazy result, so it runs *inside* the lock the daemon serializes ops
  with; run after it, a `:query` could straddle a concurrent `:assert` and report a
  KB that never existed.
- **Four refusals are the daemon's own**, and each carries a plain `:type` keyword —
  unqualified, like every other `:type` the tree throws (docs/api.md): `:not-edn` (415,
  the content-type guard above), `:cross-origin` (403), `:bad-host` (400) and
  `:body-too-large` (413). Every other `{:ok false}` carries whatever `:type` the engine
  threw, so a client discriminates on one vocabulary rather than on the status code.
- **Sentex records are projected to plain maps** before they hit the wire (the
  `sentex`-map contract, docs/api.md), so a client needs no `impl` record class.
- **The vocabulary is served** (`:terms`, `:term-count`, `:find-terms`): a remote client
  has no records to walk, so enumerating or prefix-searching the KB's terms has to be an
  op rather than something the client reconstructs. `:find-terms` filters daemon-side, so
  a search returns its hits and not the whole vocabulary; send a regex as its source
  string, since EDN carries no regex literal.
- **Belief is served in batch** (`:believed`): a client rendering n rows asks about n
  handles, and over the wire one op per row is one round-trip per row. `:believed` takes
  the whole handle list and answers the subset that is IN, so a listing costs one call.
- **The write path has a dry run** (`:check`, `:check-edit`): the remote spelling of
  "would this assert succeed, and why not?" (docs/api.md). It stores nothing and answers
  the problems with the same `:type` keywords a refusal carries, so a remote editor
  validates a line *before* it writes rather than by writing and catching.
- **…and a consequence preview** (`:preview`): not whether the batch would be admitted
  but what it would *mean* — the belief it adds and takes away (docs/preview.md). Served
  because the daemon is the single writer, which is exactly what a preview needs: it
  applies the batch and rolls it back, so it must not run beside another write. The
  answer is sentences and handles, EDN-clean, and it is why the op sits with the writes
  rather than the reads although it stores nothing.
- **…and its counterpart after the fact** (`:edit-with-consequences`): the same write as
  `:edit`, reporting what the batch turned out to mean. `:edit` answers with the handles it
  stored, which the caller already knows; this adds the belief that followed and the belief
  that went away, in `:preview`'s entry shapes, so a remote caller renders a promise and its
  outcome with one renderer.
- **Export runs on the daemon's host** (`:export`). It is a write to the *filesystem*
  rather than to the KB, and the directory it names is resolved where the daemon runs —
  the only place it can be, since the daemon owns the KB and there is no stream to hand a
  client back. Two consequences worth stating: it reports **no progress** (`:on-progress`
  is a function, and functions do not cross an EDN wire), and it runs under the write
  monitor, because the walk fetches record by record and a dump of a KB something is
  asserting into is a dump of no single state. There is no `:import` op — `import!` is
  a local operation, run in the process that owns the (empty) KB the dump lands in.
- `serve/app` is a pure `request -> response` handler (reitit-ring), so it is tested
  without a socket; `serve/start` runs it on jetty and returns the `Server`.

## Client — `vaelii.client`

```clojure
(require '[vaelii.client :as c])
(def conn (c/client "localhost" 4200))
(c/assert conn '(dog Fido) 'NaturalWorldContext)    ; => 1
(c/query  conn '(dog ?x)   'NaturalWorldContext)    ; => ({?x Fido})
(c/ask?   conn '(animal Fido) 'NaturalWorldContext)
(c/why    conn 1)
```

- A thin client over JDK `java.net.http` — **no dependency** (JDK 21 ships it).
- **Every call threads an explicit connection handle first** — `(query conn goal ctx)` —
  the network mirror of `vaelii.core`'s explicit-`kb` API. `client` returns a `conn`
  holding a reusable `HttpClient`; no socket opens until a call.
- A daemon `{:ok false}` reply becomes an `ex-info` carrying its `:error` and `:type`,
  so a remote naming / disjointness refusal reads like a local one.
- The convenience wrappers (`assert`, `assert-rule`, `sentexes-matching`, `ask`, `prove`,
  `why`, `retract!`, …) mirror the `vaelii.core` surface, bare and `!`-marked exactly as
  it spells them; `call` reaches any allowlisted op directly.

## Browsing a live daemon — `vaelii.impl.access`

The browser (`vaelii.web`) reaches a KB through the `vaelii.core` surface alone. That
surface is re-exported by `vaelii.impl.access` as a facade whose every op takes a
*target* that is either an in-process KB or a remote daemon — the reads the browser
renders with (`check` among them: it writes nothing, so it is a read), plus the four
writes it performs: `edit`, `edit-with-consequences`, `forward-chain`, and `preview`
(filed with the writes although it stores nothing, because it applies the batch and
rolls it back and so holds the single writer for its duration):

```sh
lein serve 4200 /var/lib/vaelii              # a daemon owns the KB
lein run -m vaelii.web --attach localhost 4200   # browse it, over the API, on :3000
```

- **Why it exists:** the single-writer lock means a second process can't open the
  daemon's disk KB directly, so to browse a *live* daemon you must go through its API.
  `--attach` does exactly that; every page reads over HTTP instead of in-process.
- **How:** `web/app` is written against the access facade (`local`/`remote`), so it runs
  unchanged either way — a raw KB takes the in-process path, `(remote host port)` takes
  the client. Local and remote dispatch through the *same* `serve/ops` table, so they
  can't drift, and a page renders byte-for-byte identically over either.
- The default (no `--attach`) is still an in-process starter KB — fast, standalone, and
  the right choice for local exploration. Attach is for inspecting a running daemon.
- **Writing over the wire:** the browser's Save and its Retract dispatch to the daemon
  `:edit` op, its assert form and its accepted-proposal commit to
  `:edit-with-consequences` (which answers with what the batch turned out to mean), its
  forward-chain trigger to `:forward-chain`, and its proposal preview to `:preview` —
  like any read, so modifying a KB works against an attached daemon too, with the daemon
  the single writer serializing each one under its lock. Each is preceded by a `:check`
  round-trip, so a refusal costs a message rather than a half-applied batch.

## Not here

There is no **read replica** — no way to tail a change log and re-derive belief on
another node. That would need a changelog or event-sourcing layer, and the engine has
none: a durable store records the records, not the sequence of edits that produced
them.

The **change feed** ([feed.md](feed.md)) is the in-process half of the same idea:
`watch` calls a listener with the belief every settle moved. It does not
cross the daemon, and deliberately — this surface is request/response, a listener is a
function in the writer's own process, and `read-ops` is an allowlist of questions with
answers. Pushing a feed to a remote client needs a transport that can hold a connection
open, which is a decision about the daemon rather than about the feed. So a KB behind
`serve` has exactly the polling an in-process caller no longer needs.

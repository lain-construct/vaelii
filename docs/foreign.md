# Foreign formats, and how they plug in

Vaelii reads formats it does not write, through a plugin: a dump in **another engine's
record dialect**, and a **translated OpenCyc corpus**, are the two this document works
through — [vaelii-foreign](https://github.com/vaelii/vaelii-foreign) declares five in
all (OpenCyc, RDF/OWL, WordNet, OBO, ATOMIC), which is the number a linked build
discovers below. They are bridges: each one is finished the day its corpus has been
converted once into the export dump format we do write — after which the reader would be
code that has to keep
compiling, keep passing tests, and keep being read by whoever changes a record shape, in
exchange for nothing.

So neither ships here. This engine reads its own dump format and nothing else, and a
bridge is a **separate artifact** that teaches it a format when it is on the classpath —
`vaelii-foreign` is the one we publish. Retiring a bridge is dropping a dependency; there
is no file here to delete and none to change when one arrives.

## The seam

`vaelii.impl.foreign` is the whole of it. A caller asks by kind and gets a map of
functions, or nil:

```clojure
(foreign/reader  :engine-dump)   ; the reader map, or nil
(foreign/reader! :cyc-corpus)    ; or throw, naming the kind and what this build reads
(foreign/available? :cyc-corpus) ; for a caller deciding what to attempt
(foreign/formats)                ; kind -> the var holding its reader map
```

A reader map holds whatever that reader offers — `{:name :versions :decode-frame
:replay-belief!}` for a dump dialect, `{:name :load-dir! :convert! :profiles}` for a
corpus. Deliberately **not** a protocol: two formats on the way out have nothing in
common worth abstracting, and a protocol is one more thing to agree on across a repo
boundary.

## How a plugin declares itself

One resource, `vaelii/foreign.edn`, mapping kind to the var holding its reader map:

```clojure
{:engine-dump vaelii.foreign.engine/reader
 :cyc-corpus  vaelii.foreign.cyc/reader}
```

Every copy of that resource on the classpath is read and merged, so a build reads the
union of the bridges it was given and several plugins compose without knowing about each
other. Three properties make that a seam rather than a coupling:

* **It is data.** A manifest is edn, so a plugin declares a name and can never run code
  — the same reason the shipped ontology is text ([storage.md](storage.md)).
* **The symbol resolves on use.** `requiring-resolve`, so a plugin's namespaces load when
  something actually asks for its format and no reference to one exists in this build's
  compile-time graph.
* **Which reader wins keys on content.** Two plugins claiming one kind is a warning plus
  the lexicographically smaller symbol, never classpath order — the same rule as every
  other tie-break here ([nmtms.md](nmtms.md)).

`(foreign/register :cyc-corpus 'my.ns/reader)` is the same registration done in code, for
an embedding application that has the reader in hand; it wins over a manifest, and
`unregister` undoes the call rather than the classpath. A malformed manifest throws
`:bad-foreign-manifest` naming the file, because a plugin that declares itself wrongly
otherwise reads exactly like a format nobody shipped.

| kind | reader | what it reads |
|------|--------|---------------|
| `:engine-dump` | `vaelii.foreign.engine` | frozen records of a class this build does not have, whose sentences are reconstructed from `:antecedent` / `:consequent` / `:variables`, and deductions that have to be classified into justifications and premise marks |
| `:cyc-corpus` | `vaelii.foreign.cyc` (+ `cycl`) | a CycL assertion dump, translated to vaelii sentences |

## Exercising one from here

Nothing in this repo needs a plugin and the suite runs without one, so reading a foreign
format from *this* checkout is an opt-in:

```sh
lein with-profile +with-foreign browser   # a corpus load through the catalog
lein with-profile +with-foreign repl      # a foreign dump through import-dump
```

The profile is an ordinary dependency (`project.clj`), resolved out of `~/.m2` and scoped
to the one command you prefix. The other route is `scripts/link-checkouts.sh`, which makes
`checkouts/vaelii-foreign` and resolves the readers from live source, so a change in the
plugin is visible here without an install in between.

They differ in blast radius, and the link's is worth stating: Leiningen puts a checkout on
**every** command's classpath, so a linked build discovers five formats where a shipped
build discovers none. A foreign read that works here may be the link rather than the code.
The suite is not what that endangers — its absence claims read this repo's source tree and
the seam rather than the classpath, and it is green either way — but a repl, the browser
and your own sense of what a bare build does are.

That profile is one step of a longer route. The whole of it — how the reader reaches the
classpath, converting a corpus before the catalog will offer it, and what each load
measures — is [kbs.md](kbs.md).

## Who asks

Two callers, and each one is a single expression:

* `vaelii.impl.io.import` — a frame carrying `:sentence` is ours and is decoded inline;
  anything else goes to `:engine-dump`, resolved **once per import** rather than per
  frame. A build with no such plugin refuses the dump with `:type :no-foreign-reader`
  instead of misreading it.
* `vaelii.impl.catalog` — `:corpus` loads through `:cyc-corpus`. A found KB is still
  *offered* whether or not a reader is present: the honest answer to "I cannot read this"
  is a load that fails saying so, not a KB that silently stops being listed.

## What this repo promises

`foreign_contract_test` reads the source tree rather than a KB, and pins the half a build
with no plugin can prove: no reader here, no manifest here, no file outside the seam
naming one, no compile-time reference in the seam — and an absent reader refused by name.
It also puts a manifest on the classpath and takes it away again, so discovery itself is
tested without a plugin installed. The complement — with a plugin present, every format
it declares is found, and each reader offers the keys these call sites reach for — is a
test in the plugin, since a build carrying a reader is the one thing this repo is not.

## What is not foreign

Our own dump format is not on this path, even though the importer reads both. The `:disk`
store, the index, the nippy framing and the compression codecs are all ours, and none of
them is a plugin's business.

;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.io.digest
  "The **content digest** of a stored sentex: `\"sha256:\"` and the 64 lowercase hex
  characters of a SHA-256 over the sentex's context, sign and canonical sentence, encoded
  by `encode!`.  A `(sentexHandle n)` inside the sentence digests as the identity of the
  record `n` names, so two stores holding one sentex compute one digest for it.  A digest
  is a checksum and locates nothing: a delta carries one per reference, and a merge
  compares it with the digest of the sentex the reference resolves to.  See
  docs/storage.md, \"Content digests\"."
  (:require [vaelii.impl.protocols :as p]
            [vaelii.impl.sentex :as sx])
  (:import (java.io ByteArrayOutputStream DataOutputStream)
           (java.math BigDecimal BigInteger)
           (java.security MessageDigest)))

;; ---- the canonical wire format: a deterministic, injective byte encoding ---

;; NOTE: sentences reaching here are already engine-canonicalized (canonical variables,
;; sorted symmetric arguments, folded comparisons — `docs/canonicalization.md`), so this
;; encoder only needs DETERMINISM and INJECTIVITY, not a canonicalization of its own.  It
;; must not, however, lean on `pr-str`: a printed form depends on ambient `*print-*` vars
;; and cannot type-tag, so two distinct values could print (and thus digest) alike.

(deftype ^:private SentexRef [tag payload]
  ;; A `(sentexHandle n)` term after `identity-of` has resolved it: `tag` is one of the
  ;; three reference tags `encode!` specifies, `payload` the value that tag carries.  A
  ;; type of this module's own, so no value a sentence can hold encodes as a reference.
  )

(defn- write-len-bytes!
  "Write a length-prefixed byte payload — a 4-byte big-endian count then the bytes — so a
  variable-width field is self-delimiting and cannot run into its neighbour."
  [^DataOutputStream out ^bytes b]
  (.writeInt out (alength b))
  (.write out b 0 (alength b)))

(defn- write-str!
  "Write a string as its length-prefixed UTF-8 bytes.  Fixed encoding (UTF-8) so the
  bytes never depend on a platform default charset."
  [^DataOutputStream out ^String s]
  (write-len-bytes! out (.getBytes s "UTF-8")))

(defn- write-optstr!
  "Write an *optional* string (a symbol/keyword namespace, absent for an unqualified
  name): a presence byte then, if present, the string.  Distinguishes a nil namespace
  from the empty-string one, so `(symbol nil \"a\")` and `(symbol \"\" \"a\")` cannot collide."
  [^DataOutputStream out s]
  (if (nil? s)
    (.writeByte out 0)
    (do (.writeByte out 1) (write-str! out s))))

(defn- write-bigint!
  "Write a `BigInteger` as its length-prefixed minimal two's-complement big-endian bytes
  (`.toByteArray`) — a bijection with the integer, so distinct values never share bytes."
  [^DataOutputStream out ^BigInteger bi]
  (write-len-bytes! out (.toByteArray bi)))

(defn- encode!
  "Emit the canonical bytes of `x` onto `out`.  **The wire-format spec:** every value is
  one type-tag byte then a self-delimiting payload —

      nil      0x00
      boolean  0x01 (false) | 0x02 (true)
      integer  0x03  int64 big-endian                          ; Long/Integer/Short/Byte
      bignum   0x04  len:int32  two's-complement bytes          ; BigInteger / clojure BigInt
      double   0x05  int64 big-endian of (Double/doubleToLongBits d)
      ratio    0x06  <bignum numerator> <bignum denominator>
      bigdec   0x07  <bignum unscaled> scale:int32
      string   0x08  len:int32  UTF-8 bytes
      keyword  0x09  <optstr namespace> <str name>
      symbol   0x0A  <optstr namespace> <str name>
      sequence 0x0B  count:int32  then each element encoded
      char     0x0C  int32 codepoint                          ; legal sentence content (naming/form-rank)
      target   0x0D  32 raw bytes: the SHA-256 of the named record's identity encoding
      backref  0x0E  distance:int32                           ; names a record on the current path
      dangling 0x0F  handle:int64                             ; names no record this store holds

  The last three are the reference tags: a `(sentexHandle n)` inside a sentence never
  reaches the encoder as the sequence it is spelled with.  `identity-of` replaces it with a
  `SentexRef`, so a sentence naming a stored record encodes that record's own digest
  (0x0D) and not the number one store minted for it.  A record whose walk re-enters a
  record already being digested — itself, or an ancestor in the chain of targets — encodes
  0x0E with the number of frames between the two (0 for a record naming itself), which is
  also a function of content.  A handle that names no record encodes 0x0F with the number:
  the content is gone, and the number is the only thing left to keep two such references
  distinct.

  The tag makes each type its own space (a symbol, a string and a keyword with the same
  characters take tags 0x0A / 0x08 / 0x09 and so differ); the length/count prefixes make
  every composite self-delimiting (so `(a b)` — count 2 — and `(a (b))` — count 2 with a
  nested count-1 sequence — differ); and a double is fixed by its IEEE-754 bits, never by
  a textual form, so `-0.0`, `1.0` and `1.0000000000000002` stay distinct and stable.  An
  unrecognised type throws rather than fall through to a lossy default — a silent
  collision is exactly what a content address must never permit."
  [^DataOutputStream out x]
  (cond
    (nil? x)              (.writeByte out 0x00)
    (instance? Boolean x) (.writeByte out (if x 0x02 0x01))
    (instance? clojure.lang.Ratio x)
    (do (.writeByte out 0x06)
        (write-bigint! out (.numerator ^clojure.lang.Ratio x))
        (write-bigint! out (.denominator ^clojure.lang.Ratio x)))
    (instance? BigDecimal x)
    (let [bd ^BigDecimal x]
      (.writeByte out 0x07)
      (write-bigint! out (.unscaledValue bd))
      (.writeInt out (.scale bd)))
    (float? x)   (do (.writeByte out 0x05) (.writeLong out (Double/doubleToLongBits (double x))))
    (instance? clojure.lang.BigInt x)
    (do (.writeByte out 0x04) (write-bigint! out (.toBigInteger ^clojure.lang.BigInt x)))
    (instance? BigInteger x)
    (do (.writeByte out 0x04) (write-bigint! out ^BigInteger x))
    (integer? x) (do (.writeByte out 0x03) (.writeLong out (long x)))
    (string? x)  (do (.writeByte out 0x08) (write-str! out x))
    (keyword? x) (do (.writeByte out 0x09)
                     (write-optstr! out (namespace x))
                     (write-str! out (name x)))
    (symbol? x)  (do (.writeByte out 0x0A)
                     (write-optstr! out (namespace x))
                     (write-str! out (name x)))
    ;; a char is legal sentence content (`naming/form-rank` ranks it), so it encodes
    ;; rather than reaching the `:else` throw
    (char? x)    (do (.writeByte out 0x0C) (.writeInt out (int ^Character x)))
    (instance? SentexRef x)
    (let [r ^SentexRef x
          t (long (.tag r))]
      (.writeByte out (int t))
      (case t
        0x0D (let [^bytes b (.payload r)] (.write out b 0 (alength b)))
        0x0E (.writeInt out (int (.payload r)))
        0x0F (.writeLong out (long (.payload r)))))
    (sequential? x) (do (.writeByte out 0x0B)
                        (.writeInt out (count x))
                        (doseq [e x] (encode! out e)))
    :else (throw (ex-info (str "a sentence holding a " (pr-str (class x)) " has no digest:"
                               " the encoding takes nil, a boolean, an integer, a"
                               " double, a ratio, a BigDecimal, a string, a keyword, a"
                               " symbol, a char, and a sequence of those")
                          {:type :not-encodable :value x :class (class x)}))))

(defn- canonical-bytes
  "The canonical byte encoding of `x` per `encode!`'s spec — the digest input, computed
  with no reliance on ambient print vars or platform charset."
  ^bytes [x]
  (let [bos (ByteArrayOutputStream.)
        out (DataOutputStream. bos)]
    (encode! out x)
    (.flush out)
    (.toByteArray bos)))

;; ---- SHA-256, hex, and the self-describing digest prefix ------------------

(def ^:private digest-prefix
  "The multihash-style algorithm tag every digest carries, so the primitive is explicit in
  the value."
  "sha256:")

(def ^:private sha256-hex-re
  "The body of every digest: exactly 64 lowercase hex characters, a SHA-256 written out."
  #"[0-9a-f]{64}")

(def ^:private digest-re
  "A well-formed digest string: the algorithm tag then the hex body, built from
  `digest-prefix` and `sha256-hex-re` so the format has one source."
  (re-pattern (str digest-prefix sha256-hex-re)))

(defn digest?
  "Is `x` a digest string — `\"sha256:\"` then 64 lowercase hex characters?"
  [x]
  (and (string? x) (some? (re-matches digest-re x))))

(defn- sha256
  "The raw 32-byte SHA-256 of `data`.  SHA-256, not SHA-1: the digest is a
  tamper-detection boundary and SHA-1's chosen-prefix collisions make it unfit here."
  ^bytes [^bytes data]
  (.digest (MessageDigest/getInstance "SHA-256") data))

(defn- hex
  "Lowercase hex of a byte array."
  [^bytes b]
  (apply str (map #(format "%02x" %) b)))

(defn- content-digest
  "The digest of value `x`: `\"sha256:\"` and the hex SHA-256 of its canonical bytes."
  [x]
  (str digest-prefix (hex (sha256 (canonical-bytes x)))))

;; ---- the digest: a content hash of a sentex's canonical identity ---------

(defn- sign-of
  "`:negative` when `sx` is a negative literal — its sentence a `(not S)` — and
  `:positive` otherwise.  A sentex map carries its sign in its sentence's head, and the
  digest covers this keyword beside the sentence, so every seat computes one digest
  for one sentex."
  [sx]
  (let [s (:sentence sx)]
    (if (and (nil? (:antecedent sx)) (sequential? s) (= 2 (count s)) (= 'not (first s)))
      :negative
      :positive)))

;; `resolve-refs` and `identity-digest` are mutually recursive: a sentence's references
;; are resolved by digesting the records they name, and digesting a record resolves the
;; references in its sentence.
(declare identity-digest)

(defn- resolve-refs
  "`x` with every `(sentexHandle n)` term replaced by the `SentexRef` `encode!` writes for
  it, as `[x' reach]`.  `path` is the vector of handles being digested, outermost first,
  and the frame `x` sits in is its last element.  `reach` is the smallest path index a
  back-reference anywhere inside `x` points at, `##Inf` when there is none; `identity-digest`
  reads it to decide whether a digest depends on the frames above it.  `x` comes back
  unchanged when it names no handle."
  [kb memo path x]
  (cond
    (sx/sentex-handle? x)
    (let [n (sx/handle-id x)
          i (.indexOf ^java.util.List path n)]
      (cond
        (>= i 0)
        [(SentexRef. 0x0E (- (dec (count path)) i)) i]

        (contains? @memo n)
        [(SentexRef. 0x0D (get @memo n)) ##Inf]

        :else
        (if-let [sx (p/get-sentex (:records kb) n)]
          (let [[d reach] (identity-digest kb memo path n sx)]
            [(SentexRef. 0x0D d) reach])
          [(SentexRef. 0x0F n) ##Inf])))

    (sequential? x)
    (let [rs (mapv #(resolve-refs kb memo path %) x)]
      (if (every? true? (map (fn [[x' _] e] (identical? x' e)) rs x))
        [x ##Inf]
        [(mapv first rs) (reduce min ##Inf (map second rs))]))

    :else [x ##Inf]))

(defn- identity-of
  "A sentex's canonical **identity** as a value: its context, sign (`sign-of`), and
  canonicalized sentence — everything the store keys a sentex on EXCEPT the per-store
  handle — as `[identity reach]` (`resolve-refs`).  The fields come off the constructor
  already canonical (canonical variables, sorted symmetric arguments, folded comparisons),
  so digesting them is digesting the same form in every store.  A `(sentexHandle n)` in the
  sentence carries the named record's own digest in place of `n` (`resolve-refs`, the
  reference tags in `encode!`), so two stores that minted different handles for one
  record and the records naming it compute one digest for each."
  [kb memo path sx]
  (let [[s reach] (resolve-refs kb memo path (sx/sentence-of sx))]
    [[(:context sx) (sign-of sx) s] reach]))

(defn- identity-digest
  "The raw SHA-256 of the identity of `sx`, stored at handle `h`, digested as a frame
  below `path`, as `[digest reach]`.  The digest goes into `memo` (a volatile
  `{handle digest}` scoped to one enumeration) when no back-reference inside it reaches
  above its own frame: such a digest is the same wherever the walk meets `h`, and a chain
  of replies is then digested once per record rather than once per path to it."
  [kb memo path h sx]
  (let [path'     (conj path h)
        [id reach] (identity-of kb memo path' sx)
        d         (sha256 (canonical-bytes id))]
    (when (>= reach (count path))
      (vswap! memo assoc h d))
    [d reach]))

(defn- new-memo
  "An empty digest memo for one enumeration (`identity-digest`).  Never held across calls:
  a KB is mutable, and a digest cached across a write could name a retracted target."
  []
  (volatile! {}))

(defn- digest-with
  "The digest of the stored sentex at `handle`, digesting through `memo`, or nil when the
  handle names no record."
  [kb memo handle]
  (when-let [sx (p/get-sentex (:records kb) handle)]
    (str digest-prefix (hex (first (identity-digest kb memo [] handle sx))))))

(defn digest
  "The digest of the stored sentex at `handle`, or nil when the handle names no record.
  Throws `:not-encodable` for a sentence holding a value `encode!` does not cover."
  [kb handle]
  (digest-with kb (new-memo) handle))

(defn digests
  "The digests of the stored sentexes at `handles`, in order, nil where a handle names no
  record, digesting each record a chain of references names once.  With `provenance?`,
  each digest covers `[creator created identity]` from the record's provenance, so it
  changes when the provenance does."
  [kb handles provenance?]
  (let [memo (new-memo)
        recs (:records kb)]
    (mapv (fn [h]
            (if provenance?
              (when-let [sx (p/get-sentex recs h)]
                (let [prov (p/get-provenance recs h)]
                  (content-digest [(:creator prov) (:created prov)
                                   (first (identity-of kb memo [h] sx))])))
              (digest-with kb memo h)))
          handles)))

(defn digester
  "A fn from a handle of `kb` to its digest, nil for a handle naming no record or a record
  holding a value the encoding does not cover.  One memo serves every call, so a caller
  holds it across no write."
  [kb]
  (let [memo (new-memo)]
    (fn [h] (try (digest-with kb memo h) (catch clojure.lang.ExceptionInfo _ nil)))))

(defn unstored-digest
  "The digest a canonical sentex `csx` (`res/kb-sentex`) holds once stored, computed
  without storing it.  A sentence naming the record it would be stored as has a digest
  only once stored, since the reference is a back-reference to its own frame."
  [kb csx]
  (str digest-prefix (hex (sha256 (canonical-bytes (first (identity-of kb (new-memo) [] csx)))))))

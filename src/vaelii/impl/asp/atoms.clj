;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.asp.atoms
  "Bidirectional atom id table for ASPIF translation.

   ASPIF atoms are positive integers; every entity referenced in the
   emitted program — sentex or contradiction marker — needs a unique id.
   Atom 0 is reserved as the ASPIF terminator and is never allocated.

   The table maps three kinds of source values to atom ids, sharing a
   single counter so ids are unique across kinds:

     (1) sentex ids — the :id field of a vaelii sentex record. These
         become the atoms the ASP solver reasons about.

     (2) contradiction descriptors — nested sentence-shaped Clojure
         values of the form
           (contradiction <head> :involved [[:sentex H1] [:sentex H2] …])
         where `<head>` is a sentence-shaped tag (e.g. `(negation S)`,
         `(disjointTypes ent t-a t-b)`, or a user-named head emitted by
         a grounding rule like `(wrongBulbCount 3 4)`) and `:involved`
         lists the sentex handles that participated. Atoms backed by
         contradiction descriptors get weight in the minimize statement;
         the solver avoids models in which they are true.

     (3) aux descriptors — auxiliary atoms used by translators (e.g. the
         `count ≥ N` heads of cardinality weight rules). They are
         distinct from contradictions: the minimize statement does not
         weight them, and clasp witnesses ignore them when reconstructing
         contradictions for callers.

   Labels are short string identifiers that appear in clasp's witness
   output; we read them back during result parsing to recover the
   originating sentex or contradiction. Format:

     s<sentex-id>   — sentex-backed atoms
     c<atom-id>     — contradiction-backed atoms
     a<atom-id>     — aux-backed atoms

   Using `s`/`c` prefixes keeps the two namespaces distinct even if a
   sentex id happens to numerically match a contradiction atom id.

   The table is a clojure.core/atom wrapping a plain map. Intern
   operations use swap! for atomicity; lookups are pure derefs. All
   intern operations are idempotent.")

(defn new-table
  "Return a fresh empty atom table."
  []
  (atom
   {:counter             0    ; last allocated atom id (0 = none)
    :sentex->atom        {}   ; sentex id → atom id
    :atom->sentex        {}   ; reverse
    :contradiction->atom {}   ; descriptor → atom id
    :atom->contradiction {}   ; reverse
    :aux->atom           {}   ; aux descriptor → atom id
    :atom->aux           {}   ; reverse
    :atom->label         {}   ; atom id → label string
    :label->atom         {}}))

(defn- intern!
  "Idempotent intern of `value` under `fwd-key`. If absent, allocate a
   fresh atom id, record both forward and reverse mappings, and assign
   a label via `label-fn`. Returns the atom id.

   `label-fn` is called as `(label-fn value assigned-atom-id)` and must
   return a unique non-empty string."
  [table fwd-key rev-key value label-fn]
  (or (get-in @table [fwd-key value])
      (-> (swap! table
                 (fn [{:keys [counter] :as t}]
                   (if (contains? (get t fwd-key) value)
                     t  ; lost the swap race — another caller interned
                     (let [new-id (inc counter)
                           label  (label-fn value new-id)]
                       (-> t
                           (assoc :counter new-id)
                           (assoc-in [fwd-key value] new-id)
                           (assoc-in [rev-key new-id] value)
                           (assoc-in [:atom->label new-id] label)
                           (assoc-in [:label->atom label] new-id))))))
          (get-in [fwd-key value]))))

(defn intern-sentex!
  "Ensure the sentex with id `sentex-id` has an atom id. Returns the
   atom id. Idempotent. Callers that have a sentex record should pass
   `(sentex/id sentex)`."
  [table sentex-id]
  (intern! table :sentex->atom :atom->sentex sentex-id
           (fn [sid _] (str "s" sid))))

(defn intern-contradiction!
  "Ensure `descriptor` has an atom id. `descriptor` is the nested
   sentence-shaped value
     (contradiction <head> :involved [[:sentex H1] [:sentex H2] …])
   so consumers can introspect a witness's contradiction atoms without
   secondary queries."
  [table descriptor]
  (intern! table :contradiction->atom :atom->contradiction descriptor
           (fn [_ atom-id] (str "c" atom-id))))

(defn intern-aux!
  "Ensure `descriptor` has an atom id, allocated in the aux namespace
   (distinct from contradictions — aux atoms are translator scratch
   space and do not appear in the minimize statement). `descriptor`
   must be an equality-comparable Clojure value."
  [table descriptor]
  (intern! table :aux->atom :atom->aux descriptor
           (fn [_ atom-id] (str "a" atom-id))))

(defn atom-of-sentex
  "Atom id for `sentex-id`, or nil if not yet interned."
  [table sentex-id]
  (get-in @table [:sentex->atom sentex-id]))

(defn sentex-id-of-atom
  "The sentex id backing `atom-id`, or nil if the atom is not sentex-backed."
  [table atom-id]
  (get-in @table [:atom->sentex atom-id]))

(defn contradiction-of-atom
  "Contradiction descriptor backing `atom-id`, or nil."
  [table atom-id]
  (get-in @table [:atom->contradiction atom-id]))

(defn label-of-atom
  "Label string for `atom-id`, or nil."
  [table atom-id]
  (get-in @table [:atom->label atom-id]))

(defn atom-of-label
  "Reverse: given a label string (from a clasp witness), return the
   atom id, or nil if the label is unknown."
  [table label]
  (get-in @table [:label->atom label]))

(defn count-atoms
  "Number of atoms allocated so far."
  [table]
  (:counter @table))

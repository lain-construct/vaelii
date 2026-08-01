(ns vaelii.impl.violations
  "The dropped-conclusion ledger: what the derivation path refused to store, kept as a
  value a caller can read afterwards instead of thrown at whoever happened to be
  writing.

  A namespace of its own because of **who writes it**.  Two paths file entries and they
  sit on opposite sides of the engine: the forward chainer
  (`vaelii.impl.chain`) files a conclusion it dropped, and the prover registry
  (`vaelii.impl.provers`) files an aggregate's numeric error — and the chainer is built
  *on* the registry, so the registry cannot name it.  The ledger reads nothing from
  either, only `(:violations kb)` and `(:chain-stats kb)`, so it sits below both and the
  edge runs the one direction the layering allows.

  Why a ledger rather than a throw: an entry is recorded from inside the semi-naive
  fixpoint and from inside a relabel, and neither may abort — a definitional check that
  aborted mid-fixpoint would leave belief half-computed, which is the failure the value-
  first checks (`vaelii.impl.checks`) exist to avoid.  So a violation is *reported*, and
  the run continues without the conclusion."
  (:require [taoensso.trove :as trove]))

(def ^:private max-violations
  "The ledger accumulates across chaining runs (see `vaelii.core/violations`); this caps
  it so a pathological load cannot grow it unbounded — newest entries win."
  1000)

(defn report
  "Append dropped-conclusion entries to the accumulating ledger, stamped with the
  chaining run that dropped them, and log each at :warn — a drop must be visible even to
  a caller who never reads the ledger (a bulk load polls nothing).

  No `!`: this accumulates a report and destroys nothing, and the ledger it appends to is
  emptied only by `vaelii.core/clear-violations!`, which does."
  [kb entries]
  (when (seq entries)
    (let [run     (:runs @(:chain-stats kb))
          stamped (mapv #(assoc % :run run) entries)]
      (doseq [e stamped]
        (trove/log! {:level :warn :id ::dropped-conclusion :data e}))
      (swap! (:violations kb)
             (fn [v]
               (let [v' (into v stamped)
                     n  (count v')]
                 (if (<= n max-violations)
                   v'
                   ;; `vec` *over* the `subvec`, not the subvec itself: a subvec holds a
                   ;; reference to the vector it was cut from, so returning one would pin
                   ;; every entry it just dropped — on a ledger that trims again on the
                   ;; next overflow, the cap would bound the count and nothing else.
                   (vec (subvec v' (- n max-violations))))))))))

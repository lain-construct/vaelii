;; SPDX-License-Identifier: SSPL-1.0
;; Copyright © 2026 Vaelii LLC and the Vaelii contributors.
(ns vaelii.impl.projection
  "Relation algebras built as **two independent projections onto the one-dimensional
  point algebra** — the form the cardinal directions (`vaelii.impl.orientation`) and the
  relative frame (`vaelii.impl.relative`) both have.

  Each names nine base relations, and each of the nine is a pair of coordinates on two
  orthogonal axes: north is `[:eq :gt]` east-west by north-south, front-left is
  `[:lt :gt]` left-right by front-back.  The two differ only in what the axes are called
  and which nine names sit on them.

  **Composition is computed, never looked up.**  Because the axes are independent,
  composing two relations is composing each axis through `point-compose` and taking the
  product of the two results — north-then-east is `:eq;:gt` = `:gt` on x and `:gt;:eq` =
  `:gt` on y, which is northeast.  Two opposite diagonals lose both axes at once and
  compose to the whole universe.  A 9×9 composition table would be 81 entries to get
  right by hand and to keep right; this derives them from nine projections and the
  point algebra's nine.

  **Totality is what makes it legitimate.**  The projection must be a bijection onto all
  nine `[x y]` combinations — three point relations on each of two axes — so whatever
  pair the axes compose to names a relation and nothing falls out of the algebra.
  `algebra` checks that rather than assuming it, because a projection table with a
  duplicate or a gap composes to `nil` and stores it as a relation.

  The point algebra here is spelled `:lt :eq :gt` — coordinates on an axis.
  `vaelii.impl.point` is the same three-element algebra as a *calculus* over instants,
  where the relations are `:before :equal :after` and name a claim about time; the two
  are not shared, because an axis coordinate and a temporal ordering are different
  claims that happen to compose alike."
  (:require [clojure.set :as set]))

(def point-compose
  "The one-dimensional point algebra: `[a b]` → the relations possible between x and z
  when a relates x to y and b relates y to z.  Only the two disagreeing pairs lose
  information — x < y and y > z says nothing at all about x and z."
  {[:lt :lt] #{:lt}, [:lt :eq] #{:lt}, [:lt :gt] #{:lt :eq :gt}
   [:eq :lt] #{:lt}, [:eq :eq] #{:eq}, [:eq :gt] #{:gt}
   [:gt :lt] #{:lt :eq :gt}, [:gt :eq] #{:gt}, [:gt :gt] #{:gt}})

(def point-converse
  "The one-dimensional point algebra's converse: reading a relation backwards flips it."
  {:lt :gt, :eq :eq, :gt :lt})

(def ^:private all-axis-pairs
  "The nine `[x y]` combinations a total projection must cover."
  (set (for [x [:lt :eq :gt] y [:lt :eq :gt]] [x y])))

(defn algebra
  "A `vaelii.impl.qcn` relation algebra from `relation->axes`, a map of base relation →
  its `[axis-1 axis-2]` projection.

  Returns `{:universe :identity :compose :converse}`, where the identity is whichever
  relation projects to `[:eq :eq]` — the one a thing stands in to itself, since neither
  axis separates it from itself.

  Refuses a projection that is not a bijection onto all nine axis pairs: a table with a
  gap or a repeat still composes, and what it composes to is a `nil` stored as though it
  were a relation."
  [relation->axes]
  (let [axes->relation (set/map-invert relation->axes)
        covered        (set (vals relation->axes))]
    ;; Both halves of "bijection", and the second is the one a table gets wrong quietly:
    ;; a *missing* pair composes to nil, but a *repeated* one still covers all nine while
    ;; `map-invert` silently drops one of the two relations sharing a projection — so the
    ;; count is checked as well as the coverage.
    (when-not (and (= all-axis-pairs covered)
                   (= (count relation->axes) (count all-axis-pairs)))
      (throw (ex-info (str "a two-axis projection must cover all nine [x y] pairs exactly"
                           " once, got " (count relation->axes) " relations over "
                           (count covered) " distinct pairs")
                      {:type :bad-algebra
                       :relations (count relation->axes)
                       :missing (vec (sort (set/difference all-axis-pairs covered)))
                       :repeated (vec (sort (keys (into {} (remove (fn [[_ n]] (= 1 n)))
                                                        (frequencies (vals relation->axes))))))})))
    {:universe (set (keys relation->axes))
     :identity #{(axes->relation [:eq :eq])}
     :compose
     (fn [s1 s2]
       (into #{}
             (for [r1 s1 r2 s2
                   :let [[a1 a2] (relation->axes r1)
                         [b1 b2] (relation->axes r2)]
                   c1 (point-compose [a1 b1])
                   c2 (point-compose [a2 b2])]
               (axes->relation [c1 c2]))))
     :converse
     (fn [rels]
       (into #{}
             (map (fn [r]
                    (let [[x y] (relation->axes r)]
                      (axes->relation [(point-converse x) (point-converse y)]))))
             rels))}))

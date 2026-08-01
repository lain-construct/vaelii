(ns vaelii.bench.util
  "Shared benchmark plumbing: Zipfian term generation.  Used by the `vaelii.bench.*`
  harnesses so the incantations live in one place.")

;; ---- Zipfian generation -------------------------------------------------

(defn zipf-cumulative
  "Cumulative Zipf weights for ranks 1..n at exponent `s` — the CDF a uniform draw
  binary-searches into, so rank 0 is the hottest and the tail is long."
  ^doubles [n s]
  (let [w (double-array n)]
    (loop [i 0, acc 0.0]
      (if (< i n)
        (let [acc' (+ acc (/ 1.0 (Math/pow (inc i) s)))]
          (aset w i acc')
          (recur (inc i) acc'))
        w))))

(defn zipf-sample
  ^long [^doubles cum ^java.util.Random rng]
  (let [total (aget cum (dec (alength cum)))
        r     (* total (.nextDouble rng))
        idx   (java.util.Arrays/binarySearch cum r)]
    (if (neg? idx) (min (dec (alength cum)) (- (- idx) 1)) idx)))

(defn terms [prefix n] (mapv #(symbol (str prefix %)) (range n)))

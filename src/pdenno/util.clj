(ns pdenno.util
  (:require
   [taoensso.timbre              :as log]))

(defn combinations-1
  "Create all combinations of elements from the sets, taking one item from each"
  [& sets]
  (reduce (fn [product clause]
            (doall
             (for [p product
                   lit clause]
                (conj p lit))))
          (mapv vector (first sets))
          (rest sets)))

(defn random-index
  "Create a vector of size n using each of the numbers 0 to n-1 once."
  [n]
  (letfn [(pick-from-ref!
            [unu]
            (let [picked (nth @unu (rand-int (count @unu)))]
              (dosync (swap! unu (fn [a] (remove #(= picked %) a))))
              picked))]
    (let [unused (atom (range n))]
      (reduce (fn [v _] (conj v (pick-from-ref! unused)))
              []
              (range n)))))
(defn nspaces
  "Return a string of n spaces."
  [n]
  (reduce (fn [s _] (str s " ")) "" (range n)))

(defn my-abbreviated-output-fn
  "I don't want :hostname_ and :timestamp_ in the log output."
  ([data]       (taoensso.timbre/default-output-fn nil  (dissoc data :hostname_ :timestamp_)))
  ([opts data]  (taoensso.timbre/default-output-fn opts (dissoc data :hostname_ :timestamp_))))

(log/set-config! (assoc log/*config* :output-fn #'my-abbreviated-output-fn))



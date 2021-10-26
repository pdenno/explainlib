(ns pdenno.explainlib
  (:require [libpython-clj2.require :refer [require-python]]
            [libpython-clj2.python :as py :refer [py. py.. py.-]]))

(require-python '[pysat.examples.rc2 :as rc2])
(require-python '[pysat.formula :as wcnf])

(defn run-rc2-problem
  "Execute the RC2 algorithm ntimes, blocking answers as you go.
   Result is a vector of maps each providing a model and its cost."
  [wcnf ntimes]
  (let [rc2 (rc2/RC2 wcnf)]
    (loop [result []
           cnt 0]
      (if (< cnt ntimes)
        (if-let [answer (py. rc2 compute)]
            (do (py. rc2 add_clause (mapv #(- %) answer)) ; Blocking is a mutation on rc2. 
                (recur (conj result {:model answer :cost (py/get-attr rc2 "cost")})
                       (inc cnt)))
            result)
       result))))





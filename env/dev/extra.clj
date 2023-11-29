(ns extra
  "I'm housekeeping with clojure-lsp, and the following aren't used."
  (:require
   [clojure.core.unify           :as uni]
   [explainlib.core :refer [form2lit comp-lit lit2form neg-log-cost run-problem]]))

(defn skolem?    [x] (-> x meta :skolem?))

(defn invert-clause
  "Return the clause with first literal complemented."
  [clause]
  (into (-> clause first comp-lit vector)
        (rest clause)))

(defn invert-lit
  [lit]
  (update lit :neg? not))

(defn invert-rule
  "Return the clause with first literal complemented. Doesn't varize"
  [rule]
  (-> rule
      (update :cnf  #(invert-clause %)) ; POD ugly method!
      (update :prob #(- 1.0 %))
      (update :id   #(-> % name (str "i") keyword))
      (update :head #(-> % form2lit comp-lit lit2form))))

(defn merge-kbs
  "Return a KB which is the union of the argument KBs."
  [& kbs]
  (-> (reduce (fn [kb other-kb]
                (-> kb
                    (update :rules        #(-> % (into (:rules        other-kb)) distinct vec))
                    (update :facts        #(-> % (into (:facts        other-kb)) distinct vec))
                    (update :observations #(-> % (into (:observations other-kb)) distinct vec))))
              {:rules [] :facts [] :observations []}
              kbs)
      (assoc-in [:vars :cost-fn] neg-log-cost)))

(defn add-facts
  [kb & facts]
    (update kb :facts
          into
          (->> facts
               (reduce into)
               distinct
               (sort #(> (:prob %1) (:prob %2))))))

(defn add-observations
  [kb & obs]
  (update kb :observations
          into
          (->> obs
               (reduce into)
               distinct
               (sort-by first))))

(defn cost2prob ; July experiment
  [cost]
    (Math/exp (/ (- cost) 100.0)))

(defn pred=
  "Return true if the predicate symbols match."
  [lit1 lit2]
  (= (-> lit1 :pred first)
     (-> lit2 :pred first)))

(defn sign=
  [lit1 lit2]
  (= (:neg? lit1) (:neg? lit2)))


;;; POD KB is now an arg to assumption-prob. Get rid of these!
;;;(def default-assumption-probability 0.40)
;;;(def default-black-list-probability 0.001)
;;;(def default-similarity-assumption-probability 0.001)

;;; (query-proofs (:proof-vecs fff) '[(ta/conceptType ta/DemandType nWorkers)])
;;; (query-proofs (:proof-vecs fff) '[(ta/conceptType ta/WorkerType nWorkers) (ta/simMatchVar nWorkers ta/WorkerType)])
(defn query-proofs
  "Return proof-ids of proof-vecs that contain the query. It uses uni/unify.
   Example (query-proof (:proof-vecs kb) '(ta/conceptType ta/DemandType demand)).
   Note that the queries argument is a collection but the not-queries are not."
  [proof-vecs queries & not-queries]
  (reduce-kv (fn [res proof-id pvec]
               (if (and (every? (fn [q]
                                  (some #(uni/unify % q) (->> pvec :steps (map :step))))
                                queries)
                        (not-any? (fn [q]
                                  (some #(uni/unify % q) (->> pvec :steps (map :step))))
                                  not-queries))
                 (conj res proof-id)
                 res))
             []
             proof-vecs))

(defn check-tournament-consistency
  "With a kb that is already ready for MPE analysis, run the analysis many times and see
   how often the same players appear in the final. Results won't be perfect if only because
   the tournament will have different numbers of players in it. (I'm getting 13-15)
   with a 15 limit."
  [kb & {:keys [run-times] :or {run-times 100}}]
  (-> (reduce (fn [res cnt]
                (println "Running tournament" cnt)
                (let [tourn (run-problem kb :loser-fn identity :max-together 10 :return-just-winners? true)]
                  (-> res
                      (update :in-final into tourn)
                      (update :won conj (first tourn)))))
              {:in-final []
               :won []}
              (range run-times))
      (update :in-final frequencies)
      (update :won frequencies)))

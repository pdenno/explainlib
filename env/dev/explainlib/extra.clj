(ns explainlib.extra
  "Functions defined here are for debugging.."
  (:require
   [clojure.core.unify           :as uni]
   [clojure.spec.alpha           :as s]
   [explainlib.maxsat            :refer [form2lit lit2form run-problem]]
   [explainlib.specs          :as specs]))

(defn good-fnot-meta? ; ToDo: Move to env/dev?
  "Walk through a structure and return it untouched if the the fnot propositions have the necessary metadata."
  ([obj] (good-fnot-meta? obj nil))
  ([obj tag]
   (letfn [(c4fn [x]
             (cond (map? x)                                    (reduce-kv (fn [m k v] (assoc m (c4fn k) (c4fn v))) {} x)
                   (vector? x)                                 (mapv c4fn x)
                   (and (seq? x) (= :fact/not (first x)))      (if (s/valid? ::specs/proposition x)
                                                                 x
                                                                 (throw (ex-info "fnot proposition does not have meta:" {:tag tag :specific x :part-of obj})))
                   (seq? x)                                   (map c4fn x)
                   :else                                       x))]
     (doall (c4fn obj)))))


;;; Keep this around! It puts diagnostics into the solution (but doesn't summarize probabilities).
(defn indv-probability
  "Return the probability of the individual.
   An individual is a vector of proposition-ids or (- proposition-id).
   Typically the individual is calculated by python maxsat (the :model returned).
   soft-clauses are the structures containing WDIMACS strings and info from the pclause."
  [indv soft-clauses]
    (letfn [(applies-to? [indv s-vals] (every? #(== (nth indv (-> % abs dec)) %) s-vals))]
      (reduce (fn [res sclause]
                (if (->> sclause :applies-to (applies-to? indv))
                  (conj res {:id (:id sclause) :prob (:prob sclause)})
                  res))
              []
              soft-clauses)))

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

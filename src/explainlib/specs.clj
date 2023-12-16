(ns explainlib.specs
  (:require
   [clojure.spec.alpha           :as s]))

(defn cvar?      [x] (-> x meta :cvar?))

;;; ToDo: kb should disallow cycles in rules.
(s/def ::neg?    boolean?)
(s/def ::pred    (s/and seq? #(-> % first symbol?) #(>= (count %) 2)))
(s/def ::literal (s/keys :req-un [::pred ::neg?]))
(s/def ::clause  (s/and vector? (s/coll-of ::literal)))
;;; BTW, the empty clause is false. (It is the identity in the monoid ({T,F} \/).)
(s/def ::non-empty-clause  (s/and vector? (s/coll-of ::literal :min-size 1)))
(s/def ::horn-clause     (s/and ::non-empty-clause #(<= (->> % (remove :neg?) count) 1)))
(s/def ::definite-clause (s/and ::non-empty-clause #(== (->> % (remove :neg?) count) 1)))
(s/def ::falsifiable     (s/and #(s/valid? ::non-empty-clause (:cnf %))
                                 (s/keys :req-un [::cnf]) ; recalled-facts (from proofs) are like this.
                                #(== (-> % :cnf count) 1)))

;; ToDo: Non-positional CNF will need some thought. See defn hard-clauses.
(s/def ::fact        (s/and ::falsifiable #(-> % :cnf first :neg? false?)))
(s/def ::ground-fact (s/and ::fact (fn [f] (not-any? #(cvar? %) (-> f :cnf first :pred)))))
(s/def ::observation ::ground-fact)
(s/def ::assumption  ::ground-fact)
(s/def ::head    ::pred) ; ToDo: Ensure head is positive.
(s/def ::tail    (s/and vector? (s/coll-of ::pred :min-count 1)))
(s/def ::prob    (s/double-in :min 0.0 :max 1.0))
(s/def ::id      keyword?)
(s/def ::rule    (s/and (s/keys :req-un [::head ::tail ::prob ::id])
                        #(s/valid? ::horn-clause (:cnf %))))
(s/def ::pclause (s/or :typical (s/keys :req-un [::cnf ::prob])
                       :empty  #(-> % :cnf empty?)))
(s/def ::bindings (s/and map? #(every? cvar? (keys %))))
(s/def ::binding-stack (s/and vector? (s/coll-of ::bindings :min-count 0)))
(s/def ::proposition (s/or :typical #(and (seq? %) (-> % first symbol?))
                           :fnot    #(and (seq? %)
                                          (-> % meta :factual-not?)
                                          (= :fact/not (first %))
                                          (-> % second symbol?))))

(ns explainlib.maxsat
  (:require
   [clojure.core.unify           :as uni]
   [clojure.pprint               :refer (cl-format)]
   [clojure.set                  :as sets]
   [clojure.string]
   [clojure.spec.alpha           :as s]
   [libpython-clj2.require       :refer [require-python]]
   [libpython-clj2.python        :as py :refer [py.]]
   [mount.core                   :refer [defstate]]
   [explainlib.specs             :as specs]
   [explainlib.util              :as util :refer [unify* varize collect-vars fact-not?]]
   [taoensso.timbre              :as log]))

(require-python '[pysat.examples.rc2 :as rc2])
(require-python '[pysat.formula :as wcnf])

;;; ToDo: Make sure :neg? is only used to set polarity in rule clauses. Use :fact/not otherwise.

(def diag (atom nil))
(def default-max-clause-probability      "Any clause probability larger than this value gets this value and a warning."     0.999999)

(defn lit2form
  "Return the literal list form for the argument literal map.
   Note that this doesn't care about polarity. :neg? is a pclause thing."
  [lit]
  (let [pred (:pred lit)]
    (if (= :fact/not (first pred))
      (with-meta pred {:factual-not? true})
      pred)))

(defn form2lit
  "Return a literal. It looks like {:pred (some form) :neg? true|false}.
   When argument form has {:factual-not? true} so will the :pred.
   :neg? is always returned false."
  [form]
  (s/assert ::specs/proposition form)
  (let [form (varize form)]  ; BTW varize preserves fnot meta.
    {:pred form :neg? false}))

(defn complement-lit
  "Complement the argument literal."
  [lit]
  (update lit :neg? not))

(defn opposite-lits?
  "Return true if the two literals are complements."
  [lit1 lit2]
  (and (unify* (:pred lit1) (:pred lit2))
       (not= (:neg? lit1) (:neg? lit2))))

;;; (Math/round (- (* 100.0 ##-Inf))) => 9223372036854775807. Really!!!
(defn rc2-cost-fn
  "Cost = 100 * -log(1 - P) rounded.
   This is the clause cost function for solvers like RC2 that minimize cost (not maximize score).
   The total cost of an individual is the sum of the costs of each clause it violates.
   A disjunctive clause is violated if ALL of its literals are violated by the individual.
   The cost of violating a clause is high if the clause is probable.
   Callers of this function should warn if the argument is larger than default-max-clause-probability,
   which is likely in [0.99999 1.0)."
  [prob]
  (Math/round (- (* 100.0 (Math/log (- 1.0 prob))))))

;;; This if not negating pclause in MAXSAT.
(defn rc2-cost-fn-inv
  "Inverse of neg-log-cost-fn"
  [cost]
  (- 1.0 (Math/exp (/ (- cost) 100.0))))

;;;==================================== pclauses, the heart of doing maxsat here ===========================
;;; ToDo: not-yet-implemented? and requires-evidence? aren't even defaults in defkb. Not that useful; used in just one core_test.
(defn assumption-prob
  "Return an assumption probability for the argument."
  [pred-sym kb]
  (let [not-yet-implemented? (when-let [check? (-> kb :params :not-yet-implemented?)] (check? pred-sym))
        requires-evidence?   (when-let [check? (-> kb :params :requires-evidence?)]   (check? pred-sym))
        black-listed-pred?   ((-> kb :params :black-listed-preds) pred-sym)]
    (cond not-yet-implemented?              (do (log/warn "using not-yet-implemented? for pred-sym" pred-sym) (-> kb :params :black-list-prob))
          black-listed-pred?                (do (log/warn "using black-list-pred? for pred-sym" pred-sym)     (-> kb :params :black-list-prob))
          requires-evidence?                (do (log/warn "using requires-evidence? for pre-dsym" pred-sym)   0.01)
          :else                             (do (log/warn "Using default assume-prob for" pred-sym)           (-> kb :params :default-assume-prob)))))


(defn pclause-for-non-rule
  "Return a pclause for non-rule proof-vec step, except when it is a negated fact, then return nil.
   This can be a bit confusing: negated predicates in a step are part of an explanation; they need their own pclauses.
   Later in processing we'll need a pclause for the negation of every predicate (whether it is positive or negative literal)."
  [kb proof-id step]
  (let [ground-atom (:form step)
        facts (-> kb :facts vals)]
    (as-> {:using-proof proof-id} ?pc
      (cond (:observation? step)          (-> ?pc
                                              (assoc :observation? true)
                                              (assoc :form ground-atom)
                                              (assoc :remove? true)
                                              (assoc :prob 1.0)
                                              (assoc :comment (cl-format nil "OB ~A" (:form step))))
            (:fact? step)                 (if-let [fact (some #(when (unify* ground-atom (:form %)) %) facts)] ; 2023rf Second arg to unify* was (-> % :cnf first :pred)
                                            (-> fact
                                                (assoc :fact? true)
                                                (assoc :from (:id fact))
                                                (assoc :cnf (vector {:pred ground-atom :neg? false}))
                                                (assoc :using-proof (:using-proof ?pc))
                                                (assoc :comment (cl-format nil "~A" ground-atom)))
                                            (log/error "Cannot unify fact for pclause: ground-atom=" ground-atom "step=" step)) ; ToDo: checking for this should be temporary.
            (:assumption? step)           (as-> ?pc  ?a ; ?pc will be a mapp with one key: {:using-proof ...}
                                              (assoc ?a :assumption? true)
                                              (assoc ?a :used-in (set [proof-id]))
                                              (assoc ?a :id (-> "assume-" (str (-> kb :vars :assumption-count deref)) keyword))
                                              (assoc ?a :from (:id ?a)) ; :id is going to defined using :from
                                              (assoc ?a :prob (assumption-prob (first ground-atom) kb))
                                              (assoc ?a :form ground-atom) ; 2023rf added. Might not be necessary, but looks useful.
                                              (assoc ?a :cnf (vector {:pred ground-atom :neg? false}))
                                              (assoc ?a :comment (cl-format nil "~A" ground-atom)))))))

(defn rule2cnf ; This ought to be called rule2horn!
  "Return the CNF corresponding to the rule, a vector of literal MAPS."
  [rule]
  (into (vector (form2lit (:head rule)))
        (mapv #(-> % form2lit complement-lit) (:tail rule))))

(defn pclauses-for-rule
  "Return
    (1) a pclauses for the rule, showing all bindings used and the proof from which it is being derived
    (2) the pvec with the head and non-rule steps consumed removed."
  [kb steps proof-id]
  (let [heads (->> kb :rules vals (map :head))
        rule-id (-> steps first :rule-id)
        rule (-> kb :rules rule-id)
        rule-preds (into (vector (:head rule)) (:tail rule))
        ;; ToDo: This isn't perfect (mutually recursive rules might screw it up), but I'm avoiding those.
        ground-atoms (reduce (fn [res rule-pred]
                               (conj res (some #(when (unify* rule-pred (:form %)) (:form %)) steps)))
                             []
                             rule-preds)
        bindings (reduce (fn [binds [pred fact]]
                           (let [pred (if (-> pred :meta :factual-not?) (rest pred) pred)]
                             (merge binds (unify* pred fact))))
                         {}
                         (map #(vector %1 %2) rule-preds ground-atoms))
        rule-pclause (-> rule
                         (assoc :cnf (rule2cnf rule)) ; 2023rf
                         (dissoc :head :tail :id)
                         (assoc :rule? true)
                         (assoc :using-proof proof-id)
                         (assoc :bindings bindings) ; ToDo: I don't know that it is useful, but bindings have been such a problem...
                         (assoc :from rule-id)
                         (update :cnf (fn [cnf] (mapv (fn [term] (update term :pred #(uni/subst % bindings))) cnf)))
                         (assoc :comment (str rule-id " "  bindings  " " (uni/subst (:head rule) bindings))))
        non-rule-steps-used (reduce (fn [res g-rhs] (conj res (some #(when (= g-rhs (:form %)) %) steps)))
                                    []
                                    (remove (fn [atm] (some #(unify* atm %) heads)) (rest ground-atoms)))]
    {:pclauses
     (into (vector rule-pclause)
           (mapv #(pclause-for-non-rule kb proof-id %) non-rule-steps-used))
     :steps
     (if (empty? non-rule-steps-used)
       (-> steps rest vec)
       (let [remaining (atom (-> steps rest vec))]
         (doseq [rem non-rule-steps-used]
           (let [pos (reduce (fn [pos ix]
                               (cond pos pos
                                     (= (:form rem) (-> remaining deref (nth ix) :form)) ix
                                     :else nil))
                             nil
                             (->> remaining deref count range))]
             (swap! remaining #(into (subvec % 0 pos) (subvec % (inc pos))))))
         @remaining))}))

;;; (collect-from-pvec eee (-> eee :proof-vecs :proof-1))
(defn collect-from-pvec
  "Loop through the pvec consuming steps and pushing pclauses."
  [kb pvec]
  (let [proof-id (:proof-id pvec)]
    (loop [steps (:steps pvec)
           collected []
           safe-max 200]
      (cond (empty? steps) collected
            (zero? safe-max) (log/error "Could not collect-from-pvec.")
            :else
            (let [{:keys [pclauses steps]} (pclauses-for-rule kb steps proof-id)]
              (recur steps (into collected pclauses) (dec safe-max)))))))

(defn collect-pclauses
  "Collect pclauses noting with the set :used-in which proofs they are used-in."
  [kb]
  (let [pclauses-by-cnf
        (as-> (-> kb :proof-vecs vals) ?p
          (mapcat #(collect-from-pvec kb %) ?p)
          (group-by :cnf ?p) ; No :cnf on observations. They all go to nil, which is okay.
          (dissoc ?p nil))]
    (->> (reduce-kv (fn [res _ clauses]
                      (let [used-in (-> (map :using-proof clauses) set)]
                        (conj res (-> (first clauses)
                                      (dissoc :using-proof)
                                      (assoc :used-in used-in)))))
                    []
                    pclauses-by-cnf)
         ;; These ID's will be made unique later, through reduction and inversion.
         (mapv #(assoc % :id (:from %))))))

(defn reduce-pclause-using-observations
  "Reduce the pclause's :cnf by applying evidence (See J.D. Park, 2002):
      (1) Set :remove? true if :cnf is true based on an observation.
      (2) Remove false from :cnf based evidence.
   The heads of inverse rules (which are negated literals) should not be removed.
   Observation-lits includes the query."
  [pclause observation-lits]
  (let [used-ev (atom [])]
    (as-> pclause ?pc
      (update ?pc :cnf (fn [cnf]
                         (reduce (fn [c lit]
                                   (if-let [e (and
                                               (not (and (:inverse-rule? ?pc) (= lit (first cnf))))
                                               (some #(when (opposite-lits? lit %) %) observation-lits))]
                                     (do (swap! used-ev conj e)
                                         c)
                                     (conj c lit)))
                                 []
                                 cnf)))
      (if (not-empty @used-ev)
        (update ?pc :comment #(cl-format nil "~A~{ | REDU ~A~}" % (map lit2form @used-ev)))
        ?pc)
      (assoc  ?pc :remove? (-> ?pc :cnf empty?))
      (s/assert ::specs/pclause ?pc))))

;;; Questionable to use unique-clauses above because
;;;  (1) I don't see why the same clause arrived at through different means might still be applied.
;;;      (But does RC2 maxsat allow that? Should I add up the cost of these?)
;;;  (2) It actually removes rather than sets :remove? true.
;;;  HOWEVER: I have seen it remove actual duplicates.
(defn reduce-pclauses
  "Return a vector of maps {:prob <probability> :cnf <clause> corresponding
   to the clauses used in the proofs and their complements reduced by the evidence."
  [kb]
  (let [observations (:observations kb)]
    (->> (:pclauses kb)
         (remove :remove?)
         (mapv #(reduce-pclause-using-observations % (map form2lit observations)))
         (remove :remove?)
         (mapv #(dissoc % :remove?)))))

(defn sort-clauses
  "Return the clauses sorted for easier debugging. See comments for how."
  [clauses]
  (letfn [(safe-min [x] (if (empty? x) 9999 (apply min x)))
          (typen [x] (cond (:fact? x) 1
                           (:assumption? x) 2
                           (:rule? x)  3))]
    (vec
     (sort
      (fn [x y]
        (cond (and (:remove? x) (not (:remove? y)))  1,
              (and (:remove? y) (not (:remove? x))) -1,
              (and (:remove? x) (:remove? y)) 0,
              (< (typen x) (typen y)) -1, ; facts, assumptions then rules
              (< (typen y) (typen x))  1,
              (and (< (typen x) 3) (<  (typen y) 3))
              (if (== (-> x :cnf first :pos) (-> y :cnf first :pos)) ; same fact/assum...
                (if (-> x :cnf first :neg?) +1 -1)                   ; ...positive first
                (if (< (-> x :cnf first :pos) (-> y :cnf first :pos)) -1 +1)), ; ...lower :pos facts first.
              :else ; complex clauses: clause with lowest min pos fact.
              (let [min-x (apply min (->> x :cnf (map :pos)))
                    min-y (apply min (->> y :cnf (map :pos)))]
                (cond (< min-x min-y) -1,
                      (< min-y min-x) +1,
                      :else ; choose the one with lowest sum of pos
                      (let [sum-x (apply + (->> x :cnf (map :pos)))
                            sum-y (apply + (->> y :cnf (map :pos)))]
                        (cond (< sum-x sum-y) -1
                              (< sum-y sum-x) +1
                              :else ; same sum of pos; choose the one with lowest positive min pos
                              (let [min-neg-x (safe-min (->> x :cnf (remove :neg?) (map :pos)))
                                    min-neg-y (safe-min (->> y :cnf (remove :neg?) (map :pos)))]
                                (if (< min-neg-x min-neg-y) -1 +1))))))))
      clauses))))

(defn set-pclause-prop-ids
  "Add a :pos key to every :pred of each :cnf of :pclauses.
   It indicates the proposition number for the MAXSAT analysis."
  [pclause prop-ids game]
  (update pclause :cnf
          (fn [cnf]
            (mapv (fn [lit]
                    (let [lit (util/reapply-fnot-meta lit)
                          id (or (get prop-ids (:pred lit))
                                 (get prop-ids (-> lit :pred fact-not?)))]
                      (if id
                        (assoc lit :pos id)
                        (throw (ex-info "Literal from pclause CNF not in prop-ids:"
                                        {:game game :pred (:pred lit)
                                         :pclause pclause :prop-ids prop-ids})))))
                  cnf))))

(defn make-prop-ids-map
  "Return map of proposition IDs to be used in MAXSAT.
   Most of the predicates are from proof vecs, but some are from inverse rules,
   which aren't part of proofs, of course, but are part of cost penalties."
  [game-kb]
  (let [lits (->> game-kb :proof-vecs vals (mapcat :steps) (map :form) distinct)
        fnots  (filter #(= :fact/not (first %)) lits)
        normal? (-> (remove #(= :fact/not (first %)) lits) set)]
    (when-let [bad (some #(when-not (normal? %) %) (map rest fnots))]
      (log/warn "Factual not predicate" bad "does not have a corresponding positive predicate."))
    (zipmap (sort-by first normal?) (range 1 (-> normal? count inc)))))

(defn inverse-assumptions
  "Return a vector inverses of the assumptions used."
  [kb]
  (letfn [(pinv [pc]
            (-> pc
                (update-in [:cnf 0 :neg?] not)
                (update :prob #(- 1.0 %))
                (update :id #(-> % name (str "-inv") keyword))
                (update :comment #(str % " | INV"))))]
    (map pinv (->> kb :pclauses (filter :assumption?)))))

(defn inverse-facts
  "Return a vector inverses of the facts used."
  [kb]
  (letfn [(pinv [pc]
            (-> pc
                (update-in [:cnf 0 :neg?] not)
                (update :prob #(- 1.0 %))
                (update :id #(-> % name (str "-inv") keyword))
                (update :comment #(str % " | INV"))))]
    (map pinv (->> kb :pclauses (filter :fact?)))))

(defn inverse-rules
  "Return a vector inverses of the assumptions and facts used."
  [kb]
  (letfn [(pinv [pc]
            (-> pc
                (update-in [:cnf 0 :neg?] not) ; Invert
                (update :prob #(- 1.0 %))
                (update :id #(-> % name (str "-inv") keyword))
                (assoc :inverse-rule? true)
                (update :comment #(str % " | INV"))))]
    (map pinv (->> kb
                   :pclauses
                   (filter :rule?)))))

(defn fact-probability
  "Unify the argument form with the facts and return the probability.
   truthy is merge of kb :facts :rules and :assumptions."
  [form truthy]
  (let [unifies-with (reduce (fn [res tr]
                               (if (unify* form (:form tr)) ; 2023rf second arg to unify was (-> f :cnf first :pred) AGAIN!
                                 (conj res (:id tr))
                                 res))
                             []
                             (vals truthy))]
    (if (== 1 (count unifies-with))
      (if-let [prob (-> (get truthy (first unifies-with)) :prob)]
        prob
        (throw (ex-info "No probability for unified form:" {:form form :truthy truthy})))
      (throw (ex-info "Not exactly one unifier:" {:unifies-with unifies-with :form form :truthy truthy})))))

(defn prop-id2prob
  "Return a map from prop-id integers to probabilities for facts and rules used in a proof.
   This has both polarities of the literal and it has +/- z-vars set to 1.0.
   This is computed for each proof-id because the proofs get to the propositions in the prop-ids through different rules.
   Where a proposition isn't used by the proof (it is a fact and) it is unified with a KB fact."
  [{:keys [proof-vecs prop-ids rules facts assumptions z-vars]} proof-id]
  (reset! diag rules)
  (letfn [(get-prob [step]
             (cond (:rule? step)       (-> (get rules (:rule-id step)) :prob)
                   (:fact? step)       (-> (get facts (:fact-id step)) :prob)
                   (:assumption? step) (-> (get assumptions (:assume-id step)) :prob)))]
    (let [truthy (-> facts
                     (merge assumptions)
                     (merge (reduce-kv (fn [m k v]
                                         (assoc m k (-> {}
                                                        (assoc :id   (:id v))
                                                        (assoc :form (:head v))
                                                        (assoc :prob (:prob v)))))
                                       {} rules)))  ; 2023rf was (merge rules)
          prop-ids-inv (sets/map-invert prop-ids)
          steps  (-> proof-vecs proof-id :steps)
          z-vars+ (into z-vars (map #(- %) z-vars))
          all-vars (into (range 1 (inc (apply max z-vars)))
                         (map #(- %) (range 1 (inc (apply max z-vars)))))]
      (as-> (zipmap all-vars (repeat (count all-vars) nil)) ?r
        (merge ?r (zipmap z-vars+ (repeat (count z-vars+) 1.0)))
        (merge ?r (reduce (fn [res step]
                            (let [prob (get-prob step)
                                  form (:form step)
                                  pid (or (get prop-ids form)
                                          (get prop-ids (fact-not? form)))]
                              (-> res
                                  (assoc pid prob)
                                  (assoc (- pid) (- 1.0 prob)))))
                          {}
                         steps))
        ;; Add in facts not used in the proof.
        (reduce-kv (fn [m k v]
                     (if v
                       (assoc m k v)
                       (let [prob (fact-probability (get prop-ids-inv (abs k)) truthy)]
                         (assoc m k (if (pos? k) prob (- 1.0 prob))))))
                   {} ?r)))))

;;; =================== For performing Python-based RC2 weighted partial MAXSAT analysis
;;; ToDo: change "request" to say "cmd" and the error you get will require (user/restart).
;;; Probably need to abstract out a better send for here and kquery.
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

(defn python-maxsat
  "Run a python RC2 MAXSAT problem. Return a vector describing results.
   The idea of running MAXSAT is to run a weighted satisifaction problem.
   N.B. Getting the cost of each individual solution is trivial; the true value of MAXSAT is realized
   when there are :protected clauses. In those cases it can solve a non-trivial satisfaction problem."
  [{:keys [wdimacs z-var2proof-id] :as kb}]
  (let [proof-ids (->> kb :proof-vecs keys)
        ;; map indexed by proof of pids and their inverse probability values.
        prob-map-by-proof-id (reduce (fn [res proof-id] (assoc res proof-id (prop-id2prob kb proof-id))) {} proof-ids)]
    (as-> (run-rc2-problem (wcnf/WCNF nil :from_string wdimacs) 40) ?r
      (mapv (fn [sol]
              (assoc sol :satisfies-proofs (-> (reduce (fn [res pid]
                                                         (if-let [proof-id (get z-var2proof-id pid)]
                                                           (conj res proof-id)
                                                           res))
                                                       []
                                                       (:model sol))
                                               sort vec))) ?r)
      (mapv (fn [sol]
              (assoc sol :probabilities
                     (reduce (fn [res proof-id]
                               (assoc res proof-id
                                      (reduce (fn [product pid]
                                                (* product (get (get prob-map-by-proof-id proof-id) pid)))
                                              1.0
                                              (:model sol))))
                             {}
                             (:satisfies-proofs sol)))) ?r)
      (let [summary-map-atm (atom (zipmap proof-ids (repeat (count proof-ids) 0.0)))]
        (doseq [sol ?r
                proof-id (:satisfies-proofs sol)]
          (swap! summary-map-atm
                 (fn [s] (update s proof-id #(+ % (-> sol :probabilities proof-id))))))
        {:solutions ?r
         :summary @summary-map-atm}))))

(defn pclause2pid-vec
  "Return a vector of the proposition ids for the given pclause."
  [pclause]
  (->> pclause
       :cnf
       (mapv (fn [{:keys [neg? pos]}] (if neg? (- pos) pos)))))

(defn one-clause-wdimacs
    "Return the argument pclause with :wdimacs set.
     WDIMACS-style MAXSAT penalizes instantiations that violate the (disjunctive) clause.
     A clause is violated if the instance disagree with the clause on ALL variables.
     Thus the WDIMACS clause should be viewed as the 'positive' (but disjunctive) form to which the instantiation is tested.
     Also, penalty increases as probability decreases (cost = -log(Prob)).
     The option :fancy-threshold just means that there are spaces in the string where predicates aren't used;
     the idea being when there's room, keep the numbers lined up for pretty formatting."
    [kb pclause & {:keys [commented? data-only? fancy-threshold] :or {fancy-threshold 10}}]
    (when (> (:prob pclause) default-max-clause-probability)
      (log/warn "Consider declaring this clause a hard clause (high probability):" pclause))
    (let [cost ((-> kb :vars :cost-fn) (:prob pclause))
          pid-vec (pclause2pid-vec pclause) ; A vector of natural numbers or their negatives.
          used?   (set pid-vec)
          clause-vals (if (< (-> kb :prop-ids count) fancy-threshold)
                        (reduce (fn [vs ix] ; create vector of pids (ix) and spaces
                                  (cond (used? ix)     (conj vs    ix)
                                        (used? (- ix)) (conj vs (- ix))
                                        :else          (conj vs " ")))
                                []
                                (range 1 (-> kb :prop-ids count inc)))
                        ;; If too many prop-ids, then only line up comments.
                        (let [largest (apply max (map #(-> % :cnf count) (:pclauses kb)))]
                          (into pid-vec (repeat (- largest (count pid-vec)) " "))))]
      (cond
        commented? (cl-format nil "~5A~{~5d~} c ~A" cost (conj clause-vals 0) (or (:comment pclause) ""))
        data-only? {:cost cost :pids (filter number? clause-vals)}
        :else (cl-format nil "~5A~{~5d~}" cost (conj clause-vals 0)))))

(defn z-vars
  "Return a vector of the Tseitin z-vars for the problem.
   They are numbers starting 1 + max prop-id, one for each proof."
  [kb]
  (let [prf-vecs (:proof-vecs kb)
        pids     (:prop-ids kb)]
    (vec (range (inc (count pids)) (inc (+ (count pids) (count prf-vecs)))))))

(defn z-using
  "Return a vector of Z vals that do not use the argument proposition."
  [prop prop2z]
  (reduce-kv (fn [res k v] (if (= prop k) (into res v) res))
             []
             prop2z))

(defn commented-hclause
  "Add some text to the end for the clause for use with reporting (for debugging)."
  [base-str clause-type clause kb]
  (let [base-str (clojure.string/trim-newline base-str)
        solution-zvar (apply max (map abs clause))
        min-elem      (apply min (map abs clause))
        index2pred (-> kb :prop-ids sets/map-invert)] ; This for type-3 and -4; there are just two elements.
    (case clause-type
      :type-0 (cl-format nil "~A c Must answer the query ~A.~%" base-str (:query kb))
      :type-1 (str base-str " c Require at least one of these solutions (defined by the other hard clauses).\n")
      :type-2 (str base-str (cl-format nil " c Sol ~A (~A) implies ~A to be ~A.~%" ; ToDo: (report!?!) format didn't work here!
                                       solution-zvar
                                       (get (:z-var2proof-id kb) solution-zvar)
                                       (-> min-elem abs index2pred)
                                       (if (pos? min-elem) "true" "false")))
      :type-3 (str base-str " c Optional, (needs thought!).\n")
      :type-4 (str base-str (cl-format nil " c ~A implies Sol ~A. (optional :global-disjoint?.)~%"
                                       (-> min-elem abs index2pred) solution-zvar)))))

(defn hard-clause-wdimacs-string
  "Return a map of hard clause information that includes a compact string of the
   hard constraints in wdimacs format.
   Option :fancy-threshold is for nice formatting; it puts spaces things out nicely."
  [kb clause-vecs {:keys [commented? fancy-threshold] :or {fancy-threshold 10}}]
  (let [pclauses  (remove :remove? (:pclauses kb))
        cost-fn   (-> kb :vars :cost-fn)
        hard-cost (inc (apply + (map #(-> % :prob cost-fn) pclauses)))
        zids      (:z-vars kb)
        wdimacs-string (atom "")]
    (if (< (-> kb :prop-ids count) fancy-threshold)
      (doseq [k (keys clause-vecs)]
        (doseq [clause (get clause-vecs k)]
          (let [tuple (set clause)
                valus (reduce (fn [vs ix] (cond (tuple ix)     (conj vs ix)
                                                (tuple (- ix)) (conj vs (- ix))
                                                :else (conj vs " ")))
                              []
                              (range 1 (inc (last zids))))
                base-str  (cl-format nil "~7A~{~5d~}~%" hard-cost (conj valus 0))]
            (swap! wdimacs-string str (if commented? (commented-hclause base-str k clause kb) base-str)))))
      (doseq [clause clause-vecs] ; don't bother to pretty print it.
        (swap! wdimacs-string str (cl-format nil "~7A~{~5d~}~%" hard-cost (conj (vec (sort-by #(Math/abs %) clause)) 0)))))
    {:h-wdimacs @wdimacs-string
     :hard-cost hard-cost
     :n-hclauses (count clause-vecs)
     :n-vars (last zids)}))

(defn hard-clause-wdimacs
  "Create the wdimacs string for hard clauses using a Tseitin-like transformation
   to avoid an exponential number of clauses.
   Specificaly, there are 2*num-props + (num-solutions)(num-solutions-1)/2 + 1 clauses
   divided among several types as follows:
     - type-0: optionally, where :all-individuals? is false (the default) the query must be true
     - type-1: mandatory, 1 clause with all the Z variables, requiring at least one of the solutions.
     - type-2: mandatory, implications for rules that have as their head the query; this DEFINES the z-vars.
               z-var => <a top-level rule RHS pred>, written as NOT z-var OR <the top-level rule RHS pred>
               for every pred in every rule that is top level (has the query var as its head).
     - type-3: optionally, (num-solutions)(num-solutions-1)/2 (combinations of 2) clauses with with pairs of Z variables,
               requiring no more than one solution to be true.
     - type-4: optionally, roughly num-props clauses that require that if the proposition is true, then so is every solutions using it.
               ('IF prop then Z' written as -prop V Z) " ; ToDo: This is :globally-disjoint?, and I think it should be eliminated!
  [kb commented?]
  (let [pids      (:prop-ids kb) ; A map indexed by the predicate, with integer values.
        pids-inv  (sets/map-invert pids)
        prop-ids  (vals pids)
        prf-vecs  (->> kb :proof-vecs vals (map :pvec-props))
        zids      (:z-vars kb)
        z2prop    (zipmap zids prf-vecs) ; These 'define' the Zs: index is a z-var; value is the rule RHS (vector of preds) that solved it.
        prop2z    (reduce (fn [m prop]
                            (let [res (reduce-kv (fn [res z v] (if (some #(= % prop) v) (conj res z) res)) [] z2prop)]
                              (if (not-empty res)
                                (assoc m prop res)
                                m)))
                          {}
                          (reduce into [] prf-vecs))
        query-int (-> pids (get (:query kb)))
        type-0    (if (-> kb :params :all-individuals?) [] (-> query-int vector vector))
        type-1    (vector zids)
        type-2    (cond->> (reduce-kv (fn [res z-var preds] (into res (mapv #(conj [(- z-var)] (get pids %)) preds))) [] z2prop) ; ToDo: Implement all-individuals.
                    true                                  (mapv (fn [vec] (sort vec))) ; pprint order the predicates in the clause.
                    true                                  (sort-by #(apply max (map abs %))))    ; pprint order the clause by rule they address.
        type-3    [] ;(mapv   (fn [[x y]] (vector (- x) (- y))) (combo/combinations zids 2)) ; ToDo: Needs thought!
        type-4    (if (-> kb :params :global-disjoint?)
                    (->> (map (fn [prop-id] (conj (z-using (pids-inv prop-id) prop2z) (- prop-id))) prop-ids)
                         (filter #(> (count %) 1)) ; ToDo: Not using anything; might be a mistake.
                         (mapv (fn [vec] (sort-by #(Math/abs %) vec)))
                         (sort-by #(-> % first Math/abs)))
                    {})]
    (hard-clause-wdimacs-string kb {:type-0 type-0 :type-1 type-1 :type-2 type-2 :type-3 type-3 :type-4 type-4}
                                {:commented? commented?})))

(defn wdimacs-string
  "Create the wdimacs problem (string) from the pclauses and the hard-conjunction.
   How to read the string: instances that are exact opposites acquire the penalty."
  [kb & {:keys [commented?]}]
  (let [pclauses  (remove :remove? (:pclauses kb))
        {:keys [h-wdimacs
                hard-cost
                n-hclauses
                n-vars]} (hard-clause-wdimacs kb commented?)
        p-wdimacs (cond->> (map #(one-clause-wdimacs kb % :commented? commented?) pclauses)
                    commented? (map (fn [num line] (cl-format nil "~2A: ~A" num line))
                                    (range 1 (-> pclauses count inc))))
        result (cl-format nil "p wcnf ~A ~A ~A~%~A~%~{~A~^~%~}"
                          n-vars                           ; number of variables in the problem
                          (+ (count pclauses) n-hclauses)  ; number of equations in the problem
                          hard-cost
                          h-wdimacs   ; all the hard clauses
                          p-wdimacs)] ; all the soft clauses
    result))

(defn maps-agree?
  "Return true if the values for all keys in m1 match those in m2
   or m2 does not contain the key. Checks in both directions"
  [m1 m2]
  (and
   (every? #(or (not (contains? m2 %))
                (= (get m1 %) (get m2 %)))
           (keys m1))
   (every? #(or (not (contains? m1 %))
                (= (get m2 %) (get m1 %)))
           (keys m2))))

;;; This is useful for unifying the tail of a rule with (1) kb, or
;;; (2) propositions from proofs used in the cnf of 'NOT rules'."
(defn match-form-to-facts
  "Return a vector of substitutions of all ground-facts (predicate forms)
   into the argument that (completely) unifies the form"
  [form facts]
  (reduce (fn [subs gf]
            (if-let [s (unify* form gf)]
              (conj subs s)
              subs))
          []
          facts))

(defn match-form-vec-to-facts
  "Return all combinations of bindings that substitute ground-facts individuals of
   the argument DB (ground-facts) for free variables in the argument 'conjunctive form'
   (a vector of predicates). This is essentially a query of the cform against the DB."
  [cform facts]
  (let [bindings (zipmap cform
                         (mapv #(match-form-to-facts % facts) cform))
        bsets (apply util/combinations-1 (vals bindings))]
    ;; Merge the maps of each binding set, returning a new map or
    ;; nil if they don't agree on a on a variable.
    (->> bsets
         (mapv (fn [bs] (reduce (fn [mset bs]
                                  (if (and mset (maps-agree? mset bs))
                                    (merge mset bs)
                                    nil))
                                {}
                                bs)))
         (filter identity))))

(defn query-cform
  "Return a vector of maps of instantiations cform (:form) and substitions used
   (:subs) from unifying the argument cform (vector of predicates with free
   variables) with ground-facts."
  [cform ground-facts]
  (->> (match-form-vec-to-facts cform ground-facts)
       (map #(-> {}
                 (assoc :subs %)
                 (assoc :form (uni/subst cform %))))
       (filterv #(-> % :form collect-vars empty?))
       (mapv :subs)))

(defn make-not-head-pclauses
  "Create all the pclauses (maps) for the argument rule and ground facts
   where these facts are the proposition forms of prop-id."
  [nhrule gfacts]
  (let [subs (query-cform (:tail nhrule) gfacts)]
    (->> subs
         (reduce (fn [pcs sub]
                   (let [cnf (uni/subst (:cnf nhrule) sub)]
                     (conj pcs
                           {:cnf cnf
                            :prob (:prob nhrule)
                            :type :rule
                            :id (-> (:id nhrule) name (str "-nh") keyword)
                            :comment (str "NH " (:id nhrule) " " sub)})))
                 [])
         ;; If the nhrule is about anti-symmetry only need one of the bindings.
         (group-by #(-> % :cnf set))
         (reduce-kv (fn [pcs _ v] (conj pcs (first v))) []))))

(defn unique-preds
  [pclauses]
  (reduce (fn [u c] (into u (map :pred c)))
          #{}
          (map :cnf pclauses)))

(defn add-not-head-pclauses
  "Return new pclauses for rules with NOT in the head.
   Purposes of these rules include
     (1) enforcing disjointed types of individuals, and
     (2) enforcing anti-symmetric relations, for example, {:head (not (biggerSet ?x ?y)) :tail [(biggerSet ?y ?x)]}
   This is only used in rather unusual circumstances, since here the rule does not concern causality.
   (You can't provide an explanation for why something didn't happen simply by putting a NOT in the head.)
   Also there may be a race condition in inference around these kinds of issues."
  [kb]
  (let [not-heads (filter #(-> % :head form2lit :neg?) (->> kb :rules vals))
        ground-facts (->> kb :pclauses unique-preds)]
    (mapcat #(make-not-head-pclauses % ground-facts) not-heads)))

(defn add-id-to-comments
  "Each pclause has an id and a comment string; put the id at the front of the comment string."
  [pclauses]
  (mapv (fn [pc] (update pc :comment #(str (name (:id pc)) " " %)))
        pclauses))

(defn random-games
  "Create a collection of randomized collections of proof-ids each containing game-size 'contestants'.
   Mostly it is just doing (partition-all game-size psets), but if the last game is short some
   contestants, it just adds (reuses) contestants from other games to make up the difference."
  [proof-ids game-size]
  (let [random-vecs  (reduce (fn [r pick] (conj r (nth proof-ids pick))) [] (util/random-index (count proof-ids)))
        almost-games (map vec (partition-all game-size random-vecs))
        short-game (last almost-games)
        short (- game-size (count short-game))]
    (if (zero? short)
      almost-games
      (let [short-used? (set short-game)
            available (remove short-used? random-vecs)
            play-twice (subvec (vec available) 0 short)
            with-added (into short-game play-twice)]
        (conj (vec (butlast almost-games)) with-added)))))

;;; ToDo: This projects out parts of the KB, which is a source of bugs.
(defn info-for-game
  "Produce a map of properties to merge into the kb to adjust it for a game.
   A game is a collection of proof-ids."
  [kb game & {:keys [pretty-analysis?]}]
  (as-> {} ?game-kb
    (assoc ?game-kb :game game)
    (assoc ?game-kb :vars (:vars kb))
    (assoc ?game-kb :params (:params kb))
    (assoc ?game-kb :query (:query kb))
    (assoc ?game-kb :rules (:rules kb))
    (assoc ?game-kb :facts (:facts kb))
    ;; Assumptions are sorta made on-the-spot!
    (assoc ?game-kb :assumptions (reduce (fn [res a] (assoc res (:id a) a))
                                         {}
                                         (->> kb :pclauses (filter :assumption?) (remove #(-> % :cnf first :neg?)))))
    (assoc ?game-kb :proof-vecs
           (reduce (fn [res pf-id] (assoc res pf-id (-> kb :proof-vecs pf-id)))
                   {}
                   game))
    (assoc ?game-kb :prop-ids (make-prop-ids-map ?game-kb))
    (assoc ?game-kb :pclauses
           (-> (reduce (fn [res pf-id]
                         (into res (filter #((:used-in %) pf-id)) (:pclauses kb)))
                       #{} ; A set or you will get one copy for every proof in which the clause is used.
                       game)
               util/reapply-fnot-meta))
    (update ?game-kb :pclauses (fn [pcs] (mapv #(set-pclause-prop-ids
                                                 % (:prop-ids ?game-kb) game)
                                               pcs)))
    (assoc ?game-kb :z-vars (z-vars ?game-kb))
    (assoc ?game-kb :z-var2proof-id (zipmap (:z-vars ?game-kb) (-> ?game-kb :proof-vecs keys)))
    (assoc ?game-kb :wdimacs (wdimacs-string ?game-kb))
    (reset! diag ?game-kb) ; Might be good to keep this one around.
    (if pretty-analysis?
      (as-> ?game-kb ?g2
        (update ?g2 :pclauses (fn [pcs] (mapv (fn [pc] ; This sorting for pretty wdimacs?
                                                (update pc :cnf
                                                        (fn [cnf] (vec (sort-by #(-> % :pred :pos) cnf))))) pcs)))
        (update ?g2 :pclauses sort-clauses)
        (assoc  ?g2 :wdimacsc (wdimacs-string ?g2 :commented? true))) ; Comments for this line.
      ?game-kb)))

(def ngames-played (atom 0))

(defn run-one
  ":pclauses has been prepared to run the MAXSAT problem.
   Create the wdimacs and run python-maxsat, setting :mpe."
  [kb game & {:keys [pretty-analysis?]}]
  (swap! ngames-played inc)
  (let [kb (info-for-game kb game :pretty-analysis? pretty-analysis?)]
    ;; Take what you want from this result.
    {:mpe (python-maxsat kb)
     :z-vars  (:z-vars kb)
     :pclauses (:pclauses kb)
     :wdimacs (:wdimacs kb)
     :wdimacsc (if pretty-analysis? (:wdimacsc kb) "")
     :prop-ids (:prop-ids kb)}))

(defn best-loser
  "Return the highest scoring loser. Most likely, the arguments is a collection
  of interesting losers, losers that contradict the expectation."
  [kb losers]
  (log/info "Running consolation game on" (count losers) "losers:" losers)
  (-> (run-one kb losers) :mpe first :proof-id))

(defn run-games
  "Split the :proof-vecs up into games; run the games and collect :winners and :losers.
   Loser-fn is a function for filter to find 'interesting' losers
   (e.g. ones that disagree with expectations)."
  [kb game-size num-kept]
  (let [game-groups (random-games (-> kb :proof-vecs keys) game-size)]
    (loop [groups game-groups
           result {:winners #{}
                   :losers  #{}}]
      (if (empty? groups)
        result
        (let [game (first groups) ; A 'game' is a collection proof-ids.
              kb (info-for-game kb game)]
          ;(log/info "Running game" game)
          (recur (rest groups)
                 (let [res (:mpe (run-one kb game :pretty-analysis? false))
                       [new-winners new-losers] (split-at num-kept (map :proof-id res))]
                   (-> result
                       (update :winners into new-winners)
                       (update :losers  into new-losers)))))))))

(defn run-tournament
  "Do plan-games until the number of winners is <= final-size. Then run the final.
   This calls run-games, iteratively splitting the result into winners and losers."
  [kb game-size num-kept final-size & {:keys [loser-fn] :or {loser-fn identity}}]
  (log/info "Tournament:" (-> kb :proof-vecs count) "contestants.")
  (let [loser? (not= loser-fn identity)
        t-result
        (loop [res {:winners (-> kb :proof-vecs keys set)
                    :losers  #{}}
               kb kb
               round 1]
          (if (<= (-> res :winners count) final-size)
            res
            (let [{:keys [winners losers]} (run-games kb game-size num-kept)]
              (log/info "Round" round "Winner count:" (count winners))
              (recur
               (-> res
                   (assoc :winners winners)
                   ;; ToDo: Not exactly the right place to pick up losers, but okay, I think.
                   (update :losers (fn [loo]
                                     (into loo
                                           (if (> (count losers) 2)
                                             (subvec (filterv #(loser-fn (-> kb :proof-vecs % :pvec-props)) losers) 0 2)
                                             losers)))))
               (update kb :proof-vecs #(reduce-kv (fn [res proof-id pvec]
                                                    (if (winners proof-id)
                                                      (assoc res proof-id pvec)
                                                      res))
                                                  {}
                                                  %))
               (inc round)))))
        winners (:winners t-result)
        loser (if loser? (vector (best-loser kb (:losers t-result))) [])
        final-contestants (into winners loser)]
    (when loser? (log/info "Added loser" loser))
    (log/info "Ran" (inc @ngames-played) "games.")
    (log/info "Running final of size" (count final-contestants))
    (log/info "Final is" final-contestants)
    (-> kb
        (merge (run-one kb final-contestants))
        (assoc :loser loser))))

;;; (run-problem eee)
;;; (run-problem eee :game-size 10 :num-kept 5)
(defn run-problem
  "If there are less than, :max-together proof-prop-sets, then run them all together.
   Otherwise run a tournament, where :game-size is the number of proof-prop-sets in
   a maxsat problem (a 'game'), :num-kept is how many of the highest finishers
   to advance to the next round, and :final-size is how many winners go into a
   last summary game."
  [kb & {:keys [max-together game-size num-kept final-size loser-fn return-just-winners?]
         :or {max-together 10,
              game-size 10,
              num-kept 5
              final-size 15 ; 20 runs up to 20 seconds.
              loser-fn identity}}]
  {:pre [(>= game-size 2) (< num-kept game-size)]}
  (reset! ngames-played 0)
  (if (<= (-> kb :proof-vecs count) max-together)
    (let [game (-> kb :proof-vecs keys)]
      (merge kb (run-one kb game :pretty-analysis? true)))
    (let [results (run-tournament kb game-size num-kept final-size :loser-fn loser-fn)]
      (if return-just-winners? ; for debugging
        (->> results :mpe (mapv :proof-id))
        results))))

;;;================== Starting and stopping ===================================

(defn start-maxsat
  "Call to py/initialize! and whatever else..."
  []
  (py/initialize!))

(defstate maxsat-python
  :start (start-maxsat))

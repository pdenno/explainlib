(ns explainlib.maxsat
  (:require
   [clojure.core.unify           :as uni]
   [clojure.pprint               :refer (cl-format)]
   [clojure.set                  :as sets]
   [clojure.string]
   [clojure.spec.alpha           :as s]
   [libpython-clj2.require       :refer [require-python]]
   [libpython-clj2.python        :as py]
   [mount.core                   :refer [defstate]]
   [explainlib.specs             :as specs]
   [explainlib.util              :as util :refer [unify* fact-not?]]
   [taoensso.timbre              :as log]))

(require-python '[pysat.examples.rc2 :as rc2])
(require-python '[pysat.formula :as wcnf])

;;; ToDo:
;;;   - Make sure :neg? is only used to set polarity in rule clauses. Use :fact/not otherwise.
;;;   - hunt down where factual-nots done't have proper metadata and eliminate use of reapply-fnot-meta.

(def diag (atom nil))
(def default-max-clause-probability  "Any clause probability larger than this value gets this value and a warning."  0.999999)

;;; ToDo: Of course, an objective is to eliminate this!
(defn really!
  "After saturating the code with doall around :form and getting nowhere, I try this."
  [obj]
  (if (= (type obj) clojure.lang.LazySeq)
    (let [res (cl-format nil "~A" (doall obj))]
      ;(log/info "Really!:" obj "returning res = " res)
      res)
    obj))

(defn lit2form
  "Return the literal list form for the argument literal map.
   Note that this doesn't care about polarity. :neg? is a pclause thing."  ; ToDo: probably wrong choice. Anyway, this is only used to generate WDIMACS comments
  [lit]
  (let [pred (:pred lit)]
    (if (= :fact/not (first pred))
      (with-meta pred {:factual-not? true})
      pred)))

(defn form2lit
  "Return a literal. It looks like {:pred (some form) :neg? true|false}."
  [form]
  (s/assert ::specs/proposition form)
  (if-let [base-form (util/fact-not? form)]
    {:pred base-form :neg? true}
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
  (let [facts (-> kb :facts vals)]
    (as-> {:using-proof proof-id} ?pc
      (cond (:observation? step)          (-> ?pc
                                              (assoc :observation? true)
                                              (assoc :cnf (-> step :form form2lit vector))
                                              (assoc :remove? true)
                                              (assoc :prob 1.0)
                                              (assoc :comment (cl-format nil "OB ~A" (:form step))))
            (:fact? step)                 (if-let [fact (some #(when (unify* (:form step) (:form %)) %) facts)]
                                            (let [fnot? (-> step :form fact-not?)]
                                              (as-> fact ?f
                                                (assoc ?f :fact? true)
                                                (assoc ?f :prob (if fnot? (- 1.0 (:prob fact)) (:prob fact)))
                                                (assoc ?f :from (:id fact))
                                                (assoc ?f :cnf (-> step :form form2lit vector))
                                                (assoc ?f :using-proof (:using-proof ?pc))
                                                (assoc ?f :comment (cl-format nil "~A" (:form step)))
                                                (dissoc ?f :form)))
                                            (log/error "Cannot unify fact for pclause: ground-atom=" (:form step) "step=" step)) ; ToDo: checking for this should be temporary.
            (:assumption? step)           (as-> ?pc  ?a ; ?pc will be a mapp with one key: {:using-proof ...}
                                              (assoc ?a :assumption? true)
                                              (assoc ?a :used-in (set [proof-id]))
                                              (assoc ?a :id (-> "assume-" (str (-> kb :vars :assumption-count deref)) keyword))
                                              (assoc ?a :from (:id ?a)) ; :id is going to defined using :from
                                              (assoc ?a :prob (assumption-prob (first (:form step)) kb))
                                              (assoc ?a :cnf (-> step :form form2lit vector))
                                              (assoc ?a :form (:form step)) ; Unlike :fact? and :observation, this is needed!
                                              (assoc ?a :comment (cl-format nil "~A" (:form step))))))))

(defn rule2cnf
  "Return the CNF corresponding to the rule, a vector of literal MAPS."
  [rule]
  (into (vector (form2lit (:head rule))) ; This should handle "not-head rules" too.
        (mapv #(-> % form2lit complement-lit) (:tail rule))))

(defn combine-rule-non-rule
  "Combine rule pclauses with non-rule pclause.
   This is broken out to facilitate debugging."
  [rule-pclauses fact-pclauses]
  (into rule-pclauses
        fact-pclauses))

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
                         (assoc :cnf (rule2cnf rule))
                         (dissoc :head :tail :id)
                         (assoc :rule? true)
                         (assoc :using-proof proof-id)
                         (assoc :bindings bindings) ; ToDo: I don't know that it is useful, but bindings have been such a problem...
                         (assoc :from rule-id)
                         (update :cnf (fn [cnf] (mapv (fn [term] (update term :pred #(uni/subst % bindings))) cnf)))
                         (assoc :comment (str rule-id " "  bindings  " " (really! (uni/subst (:head rule) bindings)))))
        ;; This one will produce pclauses for fnot-facts. Those are pulled out (if appropriate /always appropriate)? in combine-rule-non-rule
        non-rule-steps-used (reduce (fn [res g-rhs] (conj res (some #(when (= g-rhs (:form %)) %) steps)))
                                    []
                                    (remove (fn [atm] (some #(unify* atm %) heads)) (rest ground-atoms)))]
    {:pclauses
     (combine-rule-non-rule (vector rule-pclause)
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

(defn generate-pclauses-from-pvec
  "Generate a pclause for each step in a pvec."
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

(defn dedupe-pclauses
  "Several proofs can use essentially the same pclauses (differing only by :using-proof).
   This function reduces the set of pclauses to a unique set using their CNF.
   It sets the :used-in to a set of all proofs in which the pclause is found."
  [pclauses]
  (as-> pclauses ?p
    (group-by :cnf ?p)
    (reduce-kv (fn [res _k v]
                 (conj res (-> (first v)
                               (assoc :used-in (->> v (map :using-proof) set))
                               (dissoc :using-proof))))
               []
               ?p)
    (mapv #(assoc % :id (:from %)) ?p)))

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

(defn set-pclause-prop-ids
  "Add a :pid key to every :pred of each :cnf of :pclauses.
   It indicates the proposition number for the MAXSAT analysis."
  [pclause prop-ids game]
  (update pclause :cnf
          (fn [cnf]
            (mapv (fn [lit]
                    (let [lit (util/reapply-fnot-meta lit)
                          id (or (get prop-ids (:pred lit))
                                 (get prop-ids (-> lit :pred fact-not?)))]
                      (if id
                        (assoc lit :pid id)
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

(defn update-proof-vecs-with-prop-ids
  "Update the proof-vecs with the (polarized) prop-ids to which the steps refer."
  [proof-vecs prop-ids]
  (let [full-prop-ids (merge prop-ids (reduce-kv (fn [m k v] (assoc m (util/make-fnot k) (- v))) {} prop-ids))]
    (reduce-kv (fn [res pf-id proof]
                 (assoc res pf-id
                        (update proof :steps
                                (fn [steps]
                                  (mapv #(if-let [pid (get full-prop-ids (:form %))]
                                           (assoc % :pid pid)
                                           (throw (ex-info "There is no prop-id for proposition" {:prop (:form %)})))
                                        steps)))))
               {}
               proof-vecs)))

(defn has-inverse?
  "Return true if the inverse of pc is already found in the pclauses."
  [pc pclauses]
  (let [inv-cnf (update-in (:cnf pc) [0 :neg?] not)]
    (some #(= inv-cnf (:cnf %)) pclauses)))

(defn add-inverse-pclauses
  "Add to pclauses as necessary for every fact, rule and assumption that doesn't already have an inverse.
   Inverse facts may already be present owing to an fnot from a rule decomposition (into a proof-vec step).
   It is not possible to declare an fnot by means of defkb, so there is no cases where a positive-literal
   pclause would be added here, though the code would allow it if needed."
  [pclauses]
  (reduce (fn [res pc]
            (if (has-inverse? pc pclauses)
              (conj res pc)
              (let [inv (cond-> pc
                          true        (update-in [:cnf 0 :neg?] not)
                          true        (update :prob #(- 1.0 %))
                          true        (update :id #(-> % name (str "-inv") keyword))
                          true        (update :comment #(str % " | INV"))
                          (:rule? pc) (assoc :inverse-rule? true))]
                (into res [pc inv]))))
          []
          pclauses))

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
        (if-let [answer (py/py. rc2 compute)]
            (do (py/py. rc2 add_clause (mapv #(- %) answer)) ; Blocking is a mutation on rc2.
                (recur (conj result {:model answer :cost (py/get-attr rc2 "cost")})
                       (inc cnt)))
            result)
        result))))

(defn project-model-to-pids
  "The :model of an individual from python results has all the PID, including z-vars.
   This returns a vector of only the PIDs that concern propositions."
  [model prop-ids]
  (let [keep-id? (-> prop-ids vals set)]
    (filterv #(-> % abs keep-id?) model)))

(defn indv-probability-aux
  "Return the probability of the individual.
   An individual is a vector of proposition-ids or (- proposition-id).
   Typically the individual is calculated by python maxsat (the :model returned).
   soft-clauses are the structures containing WDIMACS strings and info from the pclause."
  [indv soft-clauses]
  (letfn [(applies-to? [indv s-vals] (every? #(== (nth indv (-> % abs dec)) %) s-vals))]
    (->> (reduce (fn [res sclause]
                   (if (->> sclause :applies-to (applies-to? indv))
                     (conj res (:prob sclause))
                     res))
                 [1.0]
                 soft-clauses)
         (apply *))))

;;; ToDo: Study the literature on model counting and fix this if necessary.
(defn indv-probabilities
  "Calculate the probability of each individual.
   If the analysis is :all-individuals?=true, there may not be pclauses that provide probability for the query,
   thus there can be a factor missing from the calculation.
   To address this, we normalize the individual populations relative to the total probabability.
   When :all-individuals?=false we calculate probability using the pclauses we have.
   There may be a 'model counting' error in this, but I think at least the relative values are reasonable.
   Note that in reporting, where :all-individuals?=false we'd typically calculate sums of individual probabilities
   by proofs they satisfy."
  [py-results {:keys [soft-clauses params]}]
  (let [raw-prob-indvs (map #(assoc % :prob (-> % :model (indv-probability-aux soft-clauses))) py-results)]
    (if (and (:all-individuals? params) (:normalize-probabilities? params))
      (let [normal (->> raw-prob-indvs (map :prob) (apply +))]
        (map (fn [indv] (update indv :prob #(/ % normal))) raw-prob-indvs))
      raw-prob-indvs)))

(defn find-matching-proofs
  "Find all the proofs matching the model arg.
   The model arg SHOULD NOT CONTAIN ANY Z-VARS but should contain PID for the query."
  [indv proof-vecs prop-ids]
  (let [model-set (-> indv :model (project-model-to-pids prop-ids) set)
        pvecs (reduce-kv (fn [m proof-id proof] (assoc m proof-id (mapv :pid (:steps proof)))) {}  proof-vecs)]
    (reduce-kv (fn [res proof-id requires-pids]
                 (if (every? #(model-set %) requires-pids) (conj res proof-id) res))
               []
               pvecs)))

(defn postprocess-indvs
  "Calculate the probability of each individual.
   Using :soft-clauses, collect the probabilities of all clauses for which the individual does not violate clause.
   Multiply those together."
  [python-results {:keys [params prop-ids proof-vecs] :as kb}]
  (as-> python-results ?mpe
    (indv-probabilities ?mpe kb)
    (if (-> params :all-individuals?)
      ?mpe
      (mapv #(assoc % :satisfies (find-matching-proofs % proof-vecs prop-ids)) ?mpe))
    (sort #(> (:prob %1) (:prob %2)) ?mpe)
    (vec ?mpe)))

(defn python-maxsat
  "Run a python RC2 MAXSAT problem. Return a vector describing results.
   The idea of running MAXSAT is to run a weighted satisifaction problem.
   N.B. Getting the cost of each individual solution is trivial; the true value of MAXSAT is realized
   when there are :protected clauses. In those cases it can solve a non-trivial satisfaction problem."
  [{:keys [wdimacs] :as kb}]
  (-> (run-rc2-problem (wcnf/WCNF nil :from_string wdimacs) 40) ; ToDo: 40?
      (postprocess-indvs kb)))

(defn pclause2pid-vec
  "Return a vector of the proposition ids for the given pclause."
  [pclause]
  (->> pclause
       :cnf
       (mapv (fn [{:keys [neg? pid]}] (if neg? (- pid) pid)))))

(defn applies-to
  "Return a vector of the prop-ids integers that can be used to check and model's conformance to the pclause.
   Not that pclause.cnf for rules is ordered: the first literal is the head.
   The polarity of the head is correct as is. The polarity of all tail literals needs to be reversed."
  [{:keys [cnf] :as pclause}]
  (letfn [(lit-val [lit] (if (:neg? lit) (-> lit :pid -) (:pid lit)))]
    (if (:rule? pclause)
      (into (-> cnf first lit-val vector)
            (->> cnf rest (map lit-val) (map -)))
      (-> cnf first lit-val vector)))) ; facts, assumptions.

(defn pclause-wdimacs
    "Return a map of information for WDIMACS soft clauses, including a WDIMACS string and commented string.
     WDIMACS-style MAXSAT penalizes instantiations that violate the (disjunctive) clause.
     A clause is violated if the instance disagree with the clause on ALL variables.
     Thus the WDIMACS clause should be viewed as the 'positive' (but disjunctive) form to which the instantiation is tested.
     Also, penalty increases as probability decreases (cost = -log(Prob)).
     The option :fancy-threshold just means that there are spaces in the string where predicates aren't used;
     the idea being when there's room, keep the numbers lined up for pretty formatting."
    [kb pclause & {:keys [fancy-threshold] :or {fancy-threshold 10}}]
    (when (> (:prob pclause) default-max-clause-probability)
      (log/warn "Consider declaring this clause a hard clause (high probability):" pclause))
    (let [cost ((-> kb :params :cost-fn) (:prob pclause))
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

      (cond-> {} ; :applies-to :used-id and maybe some others here are used for post-processing, not WDIMACS generation per se.
        (:rule? pclause)       (assoc  :rule? true)
        (:fact? pclause)       (assoc  :fact? true)
        (:assumption? pclause) (assoc  :assumption? true)
        true                   (assoc  :applies-to (applies-to pclause))
        true                   (assoc  :cost cost)
        true                   (assoc  :str-commented (cl-format nil "~5A~{~5d~} c ~A" cost (conj clause-vals 0) (or (:comment pclause) "")))
        true                   (assoc  :str           (cl-format nil "~5A~{~5d~}" cost (conj clause-vals 0)))
        #_#_true                   (assoc  :cnf           (:cnf pclause))
        true                   (assoc  :prob          (:prob pclause))
        #_#_true                   (assoc  :used-in       (:used-in pclause)))))

(defn z-vars
  "Return a vector of the Tseitin z-vars for the problem.
   They are numbers starting 1 + max prop-id, one for each proof."
  [kb]
  (let [prf-vecs (:proof-vecs kb)
        pids     (:prop-ids kb)]
    (vec (range (inc (count pids)) (inc (+ (count pids) (count prf-vecs)))))))

(defn commented-hclause
  "Add some text to the end for the clause for use with reporting (for debugging)."
  [base-str clause-type clause {:keys [query prop-ids z-var2proof-id]}]
  (let [base-str (clojure.string/trim-newline base-str)
        solution-zvar (apply max (map abs clause))
        min-elem      (apply min (map abs clause))
        index2pred (sets/map-invert prop-ids)]
    (case clause-type
      :type-0 (cl-format nil "~A c Must answer the query ~A.~%" base-str query)
      :type-1 (str base-str " c Require at least one of these solutions (defined by the other hard clauses).\n")
      :type-2 (str base-str (cl-format nil " c Sol ~A (~A) implies ~A is ~A.~%"
                                       solution-zvar
                                       (get z-var2proof-id solution-zvar)
                                       (-> min-elem abs index2pred)
                                       (if (-> clause second pos?) "true" "false"))))))

(defn hard-clause-wdimacs-string
  "Return a map of hard clause information that includes a compact string of the
   hard constraints in wdimacs format.
   Option :fancy-threshold is for nice formatting; it puts spaces things out nicely."
  [{:keys [pclauses params prop-ids] :as kb} clause-vecs {:keys [commented? fancy-threshold] :or {fancy-threshold 10}}]
  (let [cost-fn   (:cost-fn params)
        all-indv? (:all-individuals? params)
        hard-cost (inc (apply + (map #(-> % :prob cost-fn) pclauses)))
        zids      (:z-vars kb)
        wdimacs-string (atom "")]
    (when-not all-indv?
      (if (< (count prop-ids) fancy-threshold)
        (doseq [k (keys clause-vecs)]
          (doseq [clause (get clause-vecs k)]
            (let [tuple (set clause)
                  valus (reduce (fn [vs ix] (cond (tuple ix)     (conj vs ix)
                                                  (tuple (- ix)) (conj vs (- ix))
                                                  :else (conj vs " ")))
                                []
                                (range 1 (inc (last zids))))
                  base-str  (cl-format nil "~7A~{~5d~}~%" hard-cost (conj valus 0))]
              (swap! wdimacs-string str
                     (if commented?
                       (commented-hclause base-str k clause kb)
                       base-str)))))
        (doseq [clause clause-vecs] ; don't bother to pretty print it.
          (swap! wdimacs-string str (cl-format nil "~7A~{~5d~}~%" hard-cost (conj (vec (sort-by #(Math/abs %) clause)) 0))))))
    {:h-wdimacs @wdimacs-string
     :hard-cost hard-cost
     :n-hclauses (if all-indv? 0 (count clause-vecs))
     :n-vars     (if all-indv? (->> prop-ids vals (apply max)) (last zids))}))

(defn hard-clause-wdimacs
  "Create the wdimacs string for hard clauses using a Tseitin-like transformation
   to avoid an exponential number of clauses.
  1   Specificaly, there are 2*num-props + (num-solutions)(num-solutions-1)/2 + 1 clauses
   divided among several types as follows:
     - type-0: optionally, where :all-individuals? is false (the default) the query must be true.
     - type-1: :all-individuals?=false, 1 clause with all the Z variables, requiring at least one of the solutions.
     - type-2: :all-individuals?=false, implications for rules that have as their head the query; this DEFINES the z-vars.
               z-var => <a top-level rule RHS pred>, written as NOT z-var OR <the top-level rule RHS pred>
               for every pred in every rule that is top level (has the query var as its head)."
  [{:keys [params prop-ids proof-vecs z-vars query] :as kb} commented?]
  (let [prf-vecs  (->> proof-vecs vals (map :pvec-props))
        z2props   (zipmap z-vars prf-vecs) ; These DEFINE the Zs: index is a z-var; value is the rule RHS (vector of preds) that solved it.
        all-indv? (:all-individuals? params)
        query-int (get prop-ids query)
        type-0    (if all-indv? [] (-> query-int vector vector))
        type-1    (if all-indv? [] (vector z-vars))
        type-2    (if all-indv? []
                      (->> (reduce-kv (fn [res z-var props]
                                        (into res
                                              (mapv (fn [prop]
                                                      (let [fnot? (fact-not? prop)]
                                                        (conj [(- z-var)]
                                                              (if fnot?
                                                                (- (get prop-ids fnot?))
                                                                (get prop-ids prop)))))
                                                    props)))
                                      []
                                      z2props)
                           (mapv (fn [vec] (sort vec))) ; pprint order the predicates in the clause.
                           (sort-by #(apply max (map abs %)))))]  ; pprint order the clause by rule they address.
    (hard-clause-wdimacs-string kb
                                {:type-0 type-0 :type-1 type-1 :type-2 type-2}
                                {:commented? commented?})))

(defn wdimacs-string
  "Create the wdimacs problem (string) from the pclauses and the hard-conjunction.
   How to read the string: instances that are exact opposites acquire the penalty."
  [{:keys [soft-clauses] :as kb} & {:keys [commented?]}]
  (let [{:keys [h-wdimacs
                hard-cost
                n-hclauses
                n-vars]} (hard-clause-wdimacs kb commented?)
        p-wdimacs (if commented?
                    (->> soft-clauses
                         (map :str-commented)
                         (map (fn [num line] (cl-format nil "~2A: ~A" num line)) (range 1 (-> soft-clauses count inc))))
                    (map :str soft-clauses))]
    (cl-format nil "p wcnf ~A ~A ~A~%~A~%~{~A~^~%~}"
               n-vars                               ; number of variables in the problem
               (+ (count soft-clauses) n-hclauses)  ; number of equations in the problem
               hard-cost
               h-wdimacs    ; all the hard clauses concatenated
               p-wdimacs))) ; all the soft clauses individually

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
  "Produce a kb-like object that is a projection of the kb for the list of proof-ids given the the argument game.
   Add game-specific properties such as prop-ids, z-var,  and wdimacs."
  [kb game]
  (as-> {}  ?game-kb
    (assoc  ?game-kb :game game)
    (assoc  ?game-kb :vars (:vars kb))
    (assoc  ?game-kb :params (:params kb))
    (assoc  ?game-kb :query (:query kb))
    (assoc  ?game-kb :rules (:rules kb))
    (assoc  ?game-kb :facts (:facts kb))
    ;; Assumptions are created by proofs, so they are found in pclauses. Like rules and facts, they need :form.
    (assoc  ?game-kb :assumptions (reduce (fn [res a] (assoc res (:id a) a))
                                         {}
                                         (->> kb :pclauses (filter :assumption?) (remove #(-> % :cnf first :neg?)))))
    (assoc  ?game-kb :proof-vecs
            (reduce (fn [res pf-id] (assoc res pf-id (-> kb :proof-vecs pf-id)))
                    {}
                    game))
    (assoc  ?game-kb :prop-ids (make-prop-ids-map ?game-kb))
    (update ?game-kb :proof-vecs #(update-proof-vecs-with-prop-ids % (:prop-ids ?game-kb)))
    (assoc  ?game-kb :pclauses
            (-> (reduce (fn [res pf-id]
                          (into res (filter #((:used-in %) pf-id)) (:pclauses kb)))
                        #{} ; A set or you will get one copy for every proof in which the clause is used.
                        game)
                util/reapply-fnot-meta))
    (update ?game-kb :pclauses (fn [pcs] (mapv #(set-pclause-prop-ids
                                                 % (:prop-ids ?game-kb) game)
                                               pcs)))
    (assoc  ?game-kb :z-vars (z-vars ?game-kb))
    (assoc  ?game-kb :z-var2proof-id (zipmap (:z-vars ?game-kb) (-> ?game-kb :proof-vecs keys)))
    (update ?game-kb :pclauses #(->> % (remove :remove?) (sort-by :id) vec)) ; ToDo: Remove not necessary?
    (assoc  ?game-kb :soft-clauses (mapv #(pclause-wdimacs ?game-kb %) (:pclauses ?game-kb)))
    (update ?game-kb :soft-clauses (fn [clauses]
                                     (mapv (fn [sc id] (assoc sc :id id))
                                           clauses
                                           (map #(str "clause-" %) (range 1 (-> clauses count inc))))))
    (assoc  ?game-kb :wdimacs (wdimacs-string ?game-kb))
    (if (s/valid? ::specs/game-ready-obj ?game-kb)
        ?game-kb
        (do
          (s/explain ::specs/game-ready-obj ?game-kb)
          (throw (ex-info "Problem generating a game-ready object." {}))))
    (reset! diag ?game-kb))) ; Might be good to keep this one around.

(def ngames-played (atom 0))

(defn run-one
  ":pclauses has been prepared to run the MAXSAT problem.
   Create the wdimacs and run python-maxsat, setting :mpe."
  [kb game]
  (swap! ngames-played inc)
  (let [kb (info-for-game kb game)]
    {:mpe (python-maxsat kb)
     :soft-clauses (:soft-clauses kb)
     :z-var2proof-id (:z-var2proof-id kb)
     :z-vars  (:z-vars kb)
     :pclauses (:pclauses kb)
     :wdimacs (:wdimacs kb)
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
                 (let [res (:mpe (run-one kb game))
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
      (merge kb (run-one kb game)))
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

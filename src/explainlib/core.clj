(ns explainlib.core
  (:require
   [clojure.core.unify           :as uni]
   [clojure.math.combinatorics   :as combo]
   [clojure.pprint               :refer (cl-format)]
   [clojure.set                  :as sets]
   [clojure.walk                 :as walk]
   [clojure.spec.alpha           :as s]
   [libpython-clj2.require :refer [require-python]]
   [libpython-clj2.python :as py :refer [py. #_#_py.. py.-]]
   [mount.core                   :refer [defstate]]
   [explainlib.util               :as util]
   [taoensso.timbre              :as log]))

(require-python '[pysat.examples.rc2 :as rc2])
(require-python '[pysat.formula :as wcnf])

(def maxsat-timeout 20000) ; 20 seconds!
(def num-skolems (atom 0))

(defn cvar?      [x] (-> x meta :cvar?))
(defn logical?   [x] (-> x meta :logical?))
(defn skolem?    [x] (-> x meta :skolem?))

(def diag2 (atom {}))
(def diag  (atom {}))

;;; POD ToDo: kb should disallow cycles in rules.
(s/def ::neg?    boolean?)
(s/def ::pred    (s/and seq? #(-> % first symbol?) #(>= (count %) 2)))
(s/def ::literal (s/keys :req-un [::pred ::neg?]))
(s/def ::clause  (s/and vector? (s/coll-of ::literal)))
;;; BTW, the empty clause is false. (It is the identity in the monoid ({T,F} V).)
(s/def ::non-empty-clause  (s/and vector? (s/coll-of ::literal :min-size 1)))
(s/def ::horn-clause     (s/and ::non-empty-clause #(<= (->> % (remove :neg?) count) 1)))
(s/def ::definite-clause (s/and ::non-empty-clause #(== (->> % (remove :neg?) count) 1)))
(s/def ::falsifiable     (s/and #(s/valid? ::non-empty-clause (:cnf %))
                                 (s/keys :req-un [::cnf]) ; recalled-facts (from proofs) are like this.
                                #(== (-> % :cnf count) 1)))

;; POD Non-positional CNF will need some thought. See defn hard-clauses
(s/def ::fact        (s/and ::falsifiable #(-> % :cnf first :neg? false?)))
(s/def ::ground-fact (s/and ::fact (fn [f] (not-any? #(cvar? %) (-> f :cnf first :pred)))))
(s/def ::observation ::ground-fact)
(s/def ::assumption  ::ground-fact)
(s/def ::head    ::pred)
(s/def ::tail    (s/and vector? (s/coll-of ::pred :min-count 1)))
(s/def ::prob    (s/double-in :min 0.0 :max 1.0))
(s/def ::id      keyword?)
(s/def ::rule    (s/and (s/keys :req-un [::head ::tail ::prob ::id])
                        #(s/valid? ::horn-clause (:cnf %))))
(s/def ::pclause (s/or :typical (s/keys :req-un [::cnf ::prob])
                       :empty  #(-> % :cnf empty?)))
(s/def ::bindings (s/and map? #(every? cvar? (keys %))))
(s/def ::binding-stack (s/and vector? (s/coll-of ::bindings :min-count 0)))

(defn varize
  "Add :var? metadata to variables of obj."
  ([obj] (varize obj ""))
  ([obj suffix]
   (walk/postwalk (fn [x]
                    (cond (and (symbol? x) (= \? (-> x name first)))
                          (with-meta (-> x name (str suffix) symbol) {:cvar? true}),
                          (= x 'not)
                          (with-meta x {:logical? true}),
                          :else
                          x))
                  obj)))

(defn collect-vars
  "Return a set of all the vars in a argument form"
  [obj]
  (let [accum (atom #{})]
    (walk/postwalk (fn [x](when (cvar? x) (swap! accum conj x))) obj)
    @accum))

(defn collect-skolems
  "Return a set of all the vars in a argument form"
  [obj]
  (let [accum (atom #{})]
    (walk/postwalk (fn [x](when (skolem? x) (swap! accum conj x))) obj)
    @accum))

(defn ground?
  [form]
  (and (seq? form)
       (empty? (collect-vars form))))

(defn comp-lit
  "Complement the argument literal."
  [lit]
  (update lit :neg? not))

(defn comp-lits?
  "Return true if the two literals are complements."
  [lit1 lit2]
  (and (uni/unify (:pred lit1) (:pred lit2))
       (not= (:neg? lit1) (:neg? lit2))))

(defn form2lit
  "Return a literal. It looks like {:pred (some form) :neg? true|false}.
   Handles only predicates and negated predicates."
  [form]
  (if (= (first form) 'not)
    {:pred (-> form second varize) :neg? true}
    {:pred (varize form) :neg? false}))

(defn lit2form
  "Return the literal list form for the argument literal map."
  [lit]
  (varize
   (if (:neg? lit)
     (list 'not (:pred lit))
     (:pred lit))))

(defn rule2cnf ; This ought to be called rule2horn!
  "Return the CNF corresponding to the rule, a vector of literal MAPS."
  [rule]
  (reset! diag rule)
  (into (vector (form2lit (:head rule)))
        (mapv #(-> % form2lit comp-lit) (:tail rule))))

;;; This if not negating pclause in MAX-SAT.
(defn neg-log-cost
  "Cost is 100 * -log(1- P) rounded, where P in [0, 0.99]."
  [prob]
  (let [prob (min prob 0.99)]
    (Math/round (- (* 100.0 (Math/log (- 1.0 prob)))))))

;;; This if not negating pclause in MAX-SAT.
(defn neg-log-cost-1
  "inverse of neg-log-cost"
  [cost]
  (- 1.0 (Math/exp (/ (- cost) 100.0))))

(defn cost2prob ; July experiment
  [cost]
    (Math/exp (/ (- cost) 100.0)))

(defn skol-var
  "'Skolemize' the argument variable."
  [kb var]
  (let [num-skolems (-> kb :vars :num-skolems)]
    (with-meta
      (symbol (str "$" (subs (name var) 1) "-skolem-" (swap! num-skolems inc)))
      {:skolem? true})))

(defn skolemize
  "Replace free variables in the form with skolem constants."
  ([kb form] (skolemize kb form {}))
  ([kb form subs] ; Not sure what value this has any more.
   (let [{:keys [pred neg?]} (form2lit form)
         subs (if (empty? subs) {} subs)
         pred (uni/subst pred subs)
         vars (collect-vars pred)
         subs (zipmap vars (map #(skol-var kb %) vars))]
     {:form
       (lit2form {:pred (uni/subst pred subs) :neg? neg?})
      :subs subs})))

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

(defn name2suffix
  "Return a suffix good for use with the argument name (a keyword)"
  [id]
  (let [[_ let num] (re-matches #"^(\w)\w+\-(\d+)$" (name id))]
    (str "-" let num)))

(defn warn-rule-rhs-ordering
  "Rule RHSs are currently bound in the order they appear.
   Things can get goofed up if the 'data' ones are executed first, since
   useful data binding will be shadowed by an arbitrary rule RHS binding.
   This issues warnings for where data isn't first. Returns the argument."
  [rules]
  (let [rs (vals rules)
        lhs-sym? (->> rs (map :head) (map first) set)
        #_data #_(->> rs (mapcat :tail) (map first) (remove #(lhs-sym? %)))]
    (doseq [rule rs]
      (let [rhs  (map #(-> {:pos %1} (assoc :lhs-sym? (lhs-sym? %2)))
                      (range (count (:tail rule)))
                      (map first (:tail rule)))
            first-data-pos (as-> rhs ?pos
                             (remove :lhs-sym? ?pos)
                             (when (not-empty ?pos) (apply min (map :pos ?pos))))]
        (when (some #(and first-data-pos (< (:pos %) first-data-pos)) rhs)
          (log/warn "Rule" (:id rule) "has rule-rhs before rule data.")))))
  rules)

(defn finalize-rules
  "Augment the argument vector of rules with additional properties,
   returning a map indexed by a sequential name given to each rule."
  [rules]
  (-> (reduce-kv (fn [rs k v]
                   (let [suffix (name2suffix k)
                         rule (as-> v ?r
                                (assoc  ?r :id   k)
                                (update ?r :head #(varize % suffix))
                                (update ?r :tail #(varize % suffix))
                                (assoc  ?r :cnf   (rule2cnf ?r)))]
                     (s/valid? ::rule rule)
                     (assoc rs (:id rule) rule)))
                 {}
                 (zipmap (map #(-> (str "rule-" %) keyword) (range 1 (-> rules count inc)))
                         rules))
      warn-rule-rhs-ordering))

(defn finalize-facts
  "Augment the argument vector of fact with additional properties,
   returning a map indexed by a sequential name given to each rule."
  [facts]
  (reduce-kv (fn [fs k v]
               (let [suffix   (name2suffix k)
                     fact (-> v
                              (assoc  :id  k)
                              (assoc  :cnf (-> v :fact form2lit vector))
                              (update :cnf #(varize % suffix))
                              (dissoc :fact))]
                 (s/valid? ::fact fact)
                 (-> fs
                     (assoc k fact))))
             {}
             (zipmap (map #(-> (str "fact-" %) keyword) (range 1 (-> facts count inc)))
                     facts)))

(defn finalize-kb [kb query]
  (as-> kb ?kb
    (assoc  ?kb :query query)
    (update ?kb :rules finalize-rules)
    (update ?kb :facts finalize-facts)))

(defmacro defkb
  "A defkb structure is a knowledgebase used in BALP. Thus it isn't yet a BN; that
   will be generated afterwards. Its facts are observations. Each observation is a ground
   literal that will be processed through BALP to generate all proof trees."
  [name & {:keys [rules facts observations cost-fn inv-cost-fn eliminate-assumptions elimination-priority elimination-threshold]
                         :or {rules []
                              facts []
                              observations []
                              eliminate-assumptions []
                              elimination-threshold 400
                              elimination-priority []
                              cost-fn     neg-log-cost
                              inv-cost-fn neg-log-cost-1}}]
  `(do
     (def ~name (identity  {:vars {:assumption-count (atom 0)
                                   :pclause-count (atom 0)
                                   :num-skolems (atom 0)
                                   :cost-fn ~cost-fn,
                                   :inv-cost-fn ~inv-cost-fn}
                            :rules '~rules
                            :facts '~facts
                            :assumptions-used (atom {})
                            :observations '~observations
                            :eliminate-assumptions '~eliminate-assumptions
                            :elimination-threshold ~elimination-threshold
                            :elimination-priority '~elimination-priority}))))

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

(declare reset-scope-stack)
(defn clear!
  "Put things back the way they are after evaluating defkb."
  [kb]
  (reset-scope-stack)
  (reset! diag2 {})
  (reset! (:assumptions-used kb) {})
  (reset! (-> kb :vars :assumption-count) 0)
  (reset! (-> kb :vars :pclause-count) 0)
  (reset! (-> kb :vars :num-skolems) 0)
  (-> kb
      (dissoc :raw-proofs :cnf-proofs :pclauses)))

(defn pred=
  "Return true if the predicate symbols match."
  [lit1 lit2]
  (= (-> lit1 :pred first)
     (-> lit2 :pred first)))

(defn sign=
  [lit1 lit2]
  (= (:neg? lit1) (:neg? lit2)))

(defn pred-names-a-rule?
  "Pred syms that name rules are not intended to be assumptions."
  [pred-sym kb]
  (let [head-syms (->> kb :rules vals (map :head) (map first) distinct)]
    (some #(= pred-sym %) head-syms)))

;;; POD KB is now an arg to assumption-prob. Get rid of these!
(def default-assumption-probability 0.40)
(def default-black-list-probability 0.001)
(def default-similarity-assumption-probability 0.001)
;;; I think these are a good idea even once I've implemented elimination order.
;;; However, some such as black-listed ta/isType might not be useful because the reasoner doesn't assume
;;; in places where some value exists.
(def not-yet-implemented? '#{py/traceVar})
(def black-list-pred?     '#{ta/isType ta/simMatchVar ta/simMatchExcelSheet ta/simMatchColName})
(def requires-evidence?   '#{mz/indexedBy mz/indexedBy-1 mz/indexedBy-2 py/linkBack})

(defn assumption-prob
  "Return an assumption probability for the argument."
  [pred-sym kb]
  (cond (not-yet-implemented? pred-sym)               0.001  ;default-black-list-probability
        (black-list-pred? pred-sym)                   0.001  ;default-black-list-probability
        (requires-evidence? pred-sym)                 0.01  ;default-similarity-assumption-probability ; 0.001
        (pred-names-a-rule? pred-sym kb)              0.001
        :else                                         0.400))

(defn pclause-for-non-rule
  "Create pclauses for non-rule proof-vec steps."
  [kb proof-id step]
  (let [ground-atom (:step step)
        facts (-> kb :facts vals)]
    (as-> {:using-proof proof-id} ?pc
      (cond (:observation? step)
            (-> ?pc
                (assoc :observation? true)
                (assoc :form ground-atom)
                (assoc :remove? true)
                (assoc :prob 1.0)
                (assoc :comment (cl-format nil "OB ~A" (:step step))))
          (:fact? step) ; POD no negative facts.
          (let [fact (some #(when (uni/unify  ground-atom (-> % :cnf first :pred)) %) facts)]
            ;#p fact
            (-> fact
                (assoc :fact? true)
                (assoc :cnf (vector {:pred ground-atom :neg? false})) ; want the ground atom
                (assoc :using-proof (:using-proof ?pc))
                (assoc :comment (cl-format nil "~A" ground-atom))))
          (:assumption? step)
          (-> ?pc
              (assoc :assumption? true)
              (assoc :prob (assumption-prob (first ground-atom) kb))
              (assoc :cnf (vector {:pred ground-atom :neg? false}))
              (assoc :comment (cl-format nil "~A" ground-atom)))))))

(defn pclauses-for-rule
  "Return
    (1) a pclauses for the rule, showing all bindings used and the proof from which it is being derived
    (2) the pvec with the head and non-rule steps consumed removed."
  [kb steps proof-id]
  (let [heads (->> kb :rules vals (map :head))
        rule-id (-> steps first :rule-id)
        rule (-> kb :rules rule-id)
        rule-preds (into (vector (:head rule)) (:tail rule))
        ;; POD This isn't perfect (mutually recursive rules might screw it up), but I'm avoiding those.
        ground-atoms (reduce (fn [res rule-pred]
                               (conj res (some #(when (uni/unify rule-pred (:step %)) (:step %)) steps)))
                             []
                             rule-preds)
        bindings (reduce (fn [binds [pred fact]] (merge binds (uni/unify pred fact)))
                         {}
                         (map #(vector %1 %2) rule-preds ground-atoms))
        rule-pclause (-> rule
                         (assoc :rule? true)
                         (assoc :using-proof proof-id)
                         (assoc :bindings bindings) ; POD I don't know that it is useful, but bindings have been such a problem...
                         (dissoc :head :tail :id)
                         (assoc :from-rule rule-id)
                         (update :cnf (fn [cnf] (mapv (fn [term] (update term :pred #(uni/subst % bindings))) cnf)))
                         (assoc :comment (str rule-id " "  bindings  " " (uni/subst (:head rule) bindings))))
        non-rule-steps-used (reduce (fn [res g-rhs]
                                      (conj res (some #(when (= g-rhs (:step %)) %) steps)))
                                    []
                                    (remove (fn [atm] (some #(uni/unify atm %) heads)) (rest ground-atoms)))]
    {:pclauses
     (into (vector rule-pclause)
           (mapv #(pclause-for-non-rule kb proof-id %) non-rule-steps-used))
     :steps
     (if (empty? non-rule-steps-used)
       (-> steps rest vec)
       (let [remaining (atom (-> steps rest vec))] ; POD there is probably a better way to 'remove-first'
         (doseq [rem non-rule-steps-used]
           (let [pos (reduce (fn [pos ix]
                               (cond pos pos
                                     (= (:step rem) (-> remaining deref (nth ix) :step)) ix
                                     :else nil))
                             nil
                             (->> remaining deref count range))]
             ;(when-not pos (reset! diag {:rem rem :remaining @remaining}))
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
  (let [pclause-count (-> kb :vars :pclause-count)
        pclauses-by-cnf
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
         (mapv #(cond (:rule? %) (assoc % :id (-> (str "pc-" (swap! pclause-count inc) "-ru") keyword))
                      (:fact? %) (assoc % :id (-> (str "pc-" (swap! pclause-count inc) "-fa") keyword))
                      (:assumption? %) (assoc % :id (-> (str "pc-" (swap! pclause-count inc) "-as") keyword)))))))

(defn reduce-pclause
  "Reduce the pclause's :cnf by applying evidence (See J.D. Park, 2002):
      (1) Set :remove? true if :cnf is true based on an observation.
      (2) Remove false from :cnf based evidence."
  [pclause observation-lits]
  (let [used-ev (atom [])]
    (as-> pclause ?pc
      (update ?pc :cnf (fn [cnf]
                         (reduce (fn [c lit]
                                   (if-let [e (some #(when (comp-lits? lit %) %) observation-lits)]
                                     (do (swap! used-ev conj e)
                                         c)
                                     (conj c lit)))
                                 []
                                 cnf)))
      (update ?pc :comment #(cl-format nil "~A~{ | REDU ~A~}" % (map lit2form @used-ev)))
      (assoc  ?pc :remove? (-> ?pc :cnf empty?))
      (s/assert ::pclause ?pc))))

;;; Questionable to use unique-clauses above because
;;;  (1) I don't see why the same clause arrived at through different means might still be applied.
;;;      (But does RC2 maxsat allow that? Should I add up the cost of these?)
;;;  (2) It actually removes rather than sets :remove? true.
;;;  HOWEVER: I have seen it remove actual duplicates.
(defn reduce-pclauses-using-observations
  "Return a vector of maps {:prob <probability> :cnf <clause> corresponding
   to the clauses used in the proofs and their complements reduced by the evidence."
  [kb]
  (let [observations (conj (conj (:observations kb)
                                 (:query kb))
                           (list 'not (:query kb)))]
    (->> (:pclauses kb)
         (remove :remove?)
         (mapv #(reduce-pclause % (map form2lit observations)))
         (remove :remove?)
         (mapv #(dissoc % :remove?)))))

(defn compare-lists
  "Return a compare value looking at corresponding values of two lists of symbols."
  [x y]
  (loop [x x
         y y]
    (cond
      (and (empty? x) (empty? y)) 0,
      (empty? x) -1
      (empty? y) +1
      (not= (first x) (first y)) (compare (-> x first name) (-> y first name)),
      :else (recur (rest x) (rest y)))))

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
                    (let [id (get prop-ids (:pred lit))]
                      (if id
                        (assoc lit :pos id)
                        (throw (ex-info "Literal from pclause CNF not in prop-ids:"
                                        {:game game :pred (:pred lit)
                                         :pclause pclause :prop-ids prop-ids})))))
                  cnf))))

(defn get-prop-ids
  "Return map of proposition IDs to be used in MAXSAT."
  [proof-vecs]
  (let [lits (->> proof-vecs
                  vals
                  (map :pvec)
                  (reduce into #{})
                  (sort compare-lists))]
    (zipmap lits (range 1 (-> lits count inc)))))

;;; This is useful for unifying the tail of a rule with (1) kb, or
;;; (2) propositions from proofs used in the cnf of 'NOT rules'."
(defn match-form-to-facts
  "Return a vector of substitutions of all ground-facts (predicate forms)
   into the argument that (completely) unifies the form"
  [form facts]
  (reduce (fn [subs gf]
            (if-let [s (uni/unify form gf)]
              (conj subs s)
              subs))
          []
          facts))

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

;;; POD This approach means no need to create the inverse rules in defkb!
(defn inverse-rules
  "Return a vector inverses of the assumptions and facts used."
  [kb]
  (letfn [(pinv [pc]
            (-> pc
                (update-in [:cnf 0 :neg?] not)
                (update :prob #(- 1.0 %))
                (update :id #(-> % name (str "-inv") keyword))
                (update :comment #(str % " | INV"))))]
    (map pinv (->> kb
                   :pclauses
                   (filter :rule?)
                   (remove :no-inv?)))))

(defn model2proof-id
  "Return the proof-id that corresponds to the model.
  (A model the set of prop-ids (integers) indicating the truth (pos? i) of each proposition."
  [indv prop-ids proof-vecs]
  (let [prop-inv    (sets/map-invert prop-ids)
        model-props (->> indv (filter pos?) (map #(get prop-inv %)) set)
        matching    (reduce-kv (fn [res proof-id pvec]
                                 (if (= (-> pvec :pvec set) model-props)
                                   (conj res proof-id)
                                   res))
                               []
                               proof-vecs)]
    (when-not (= 1 (count matching))
      ;(reset! diag {:indv indv :psets psets :true-props true-props :pvec proof-vecs})
      (throw (ex-info "Zero or 2 or more matching solutions in proof-prop-vecs." {:matching matching :indv indv})))
    (first matching)))

;;; =================== For performing Python-based RC2 weighted partial MAXSAT analysis
;;; POD ToDo: change "request" to say "cmd" and the error you get will require (user/restart).
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
  "Query any active app-gateway to run an RC2 MAXSAT problem. Return the :result."
  [{:keys [wdimacs z-vars prop-ids proof-vecs]}]
  (try
    (let [results (run-rc2-problem (wcnf/WCNF nil :from_string wdimacs) 40)
          z-set (set (into z-vars (map - z-vars)))]
      (mapv (fn [indv]
              (as-> indv ?i
                (assoc ?i :proof-id (model2proof-id (remove #(z-set %) (:model indv)) prop-ids proof-vecs))
                (assoc ?i :pvec (-> (get proof-vecs (:proof-id ?i)) :pvec))
                (dissoc ?i :model))) ; pvec has all the info of model
            results))
    (catch Throwable _ (log/error "Problem running MAXSAT."))))

(defn pclause2pid-vec
  "Return a vector of the proposition ids for the given pclause."
  [pclause]
  (swap! diag2 #(assoc % :pclause-pos-error? pclause))
    (->> pclause
       :cnf
       (mapv (fn [{:keys [neg? pos]}] (if neg? (- pos) pos)))))

(defn one-clause-wdimacs
  "Return the argument pclause with :wdimacs set.
   WDIMACS-style MAXSAT penalizes instantiations that violate the
   (disjunctive) clause. The instance must disagree on ALL variables
   in the MAXSAT clause. Thus the WDIMACS clause should be viewed as
   the 'positive' (but disjunctive) form to which the instantiation is tested.
   Also, penalty increases as probability decreases (cost = -log(Prob))."
  [kb pclause & {:keys [commented? data-only? fancy-threshold] :or {fancy-threshold 10}}]
  (let [cost ((-> kb :vars :cost-fn) (:prob pclause))
        pid-vec (pclause2pid-vec pclause)
        used?   (set pid-vec)
        vals (if (< (-> kb :prop-ids count) fancy-threshold)
               (reduce (fn [vs ix]
                         (cond (used? ix)     (conj vs    ix)
                               (used? (- ix)) (conj vs (- ix))
                               :else          (conj vs " ")))
                       []
                       (range 1 (-> kb :prop-ids count inc)))
               (let [largest (apply max (map #(-> % :cnf count) (:pclauses kb)))]
                 (into pid-vec (repeat (- largest (count pid-vec)) " "))))]
    (cond
      commented? (cl-format nil "~5A~{~5d~} c ~A" cost (conj vals 0) (or (:comment pclause) ""))
      data-only? {:cost cost :pids (filter number? vals)}
      :else (cl-format nil "~5A~{~5d~}" cost (conj vals 0)))))

(defn z-vars
  "Return a vector of the Tseitin z-vars for the problem."
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

(defn z-not-using
  "Return a vector of Z vals that do not use the argument proposition."
  [prop prop2z]
  (let [zs (set (reduce into [] (vals prop2z)))]
    (vec (sets/difference zs (set (z-using prop prop2z))))))

(defn hard-clause-wdimacs
  "Return a map of hard clause information that includes a compact string of the
   hard constraints in wdimacs format."
  [kb clause-vecs & {:keys [fancy-threshold] :or {fancy-threshold 10}}]
  (let [pclauses  (remove :remove? (:pclauses kb))
        cost-fn   (-> kb :vars :cost-fn)
        hard-cost (inc (apply + (map #(-> % :prob cost-fn) pclauses)))
        zids      (:z-vars kb)
        wdimacs-string (atom "")]
    (if (< (-> kb :prop-ids count) fancy-threshold)
      (doseq [clause clause-vecs]
        (let [tuple (set clause)
              valus (reduce (fn [vs ix] (cond (tuple ix)     (conj vs ix)
                                              (tuple (- ix)) (conj vs (- ix))
                                              :else (conj vs " ")))
                            []
                            (range 1 (inc (last zids))))]
          (swap! wdimacs-string str (cl-format nil "~7A~{~5d~}~%" hard-cost (conj valus 0)))))
      (doseq [clause clause-vecs]
        (swap! wdimacs-string str (cl-format nil "~7A~{~5d~}~%" hard-cost (conj (vec (sort-by #(Math/abs %) clause)) 0)))))
    {:h-wdimacs @wdimacs-string
     :hard-cost hard-cost
     :n-hclauses (count clause-vecs)
     :n-vars (last zids)}))

;;; (proof-vec-hard-one-clause-wdimacs bbb) ; BTW, provide a proof of this approach.
(defn proof-vec-hard-clause-wdimacs
  "Create the wdimacs string for hard clauses using a Tseitin-like transformation
   to avoid an exponential number of clauses.
   Specificaly, there are 2*num-props + (num-solutions)(num-solutions-1)/2 + 1 clauses
   divided among four types. The types are as follows:
     (1) 1 clause with all the Z variables, requiring at least one of the solutions.
     (2) (num-solutions)(num-solutions-1)/2 (combinations of 2) clauses with with pairs of Z variables,
         requiring no more than one solution to be true.
     (3) num-props clauses that require either the proposition to be false or some solution not containing
         the proposition to be true. (Encoded as an IF statement. Thus PROP OR any Z not containing prop.)
     (4) roughly num-props clauses that require that if the proposition is true, then so is every solutions using it.
         ('IF prop then Z' written as -prop V Z) "
  [kb]
  (let [pids      (:prop-ids kb)
        pids-1    (sets/map-invert pids)
        prop-ids  (vals pids)
        prf-vecs  (->> kb :proof-vecs vals (map :pvec))
        zids      (:z-vars kb)
        z2prop    (zipmap zids prf-vecs) ; These 'define' the Zs.
        prop2z    (reduce (fn [m prop]
                            (let [res (reduce-kv (fn [res z v] (if (some #(= % prop) v) (conj res z) res)) [] z2prop)]
                              (if (not-empty res)
                                (assoc m prop res)
                                m)))
                          {}
                          (reduce into [] prf-vecs))
        type-1    zids
        type-2    (mapv   (fn [[x y]] (vector (- x) (- y))) (combo/combinations zids 2))
        type-3    (->> (mapv (fn [prop-id] (conj (z-not-using (pids-1 prop-id) prop2z) prop-id))  prop-ids)
                       (mapv (fn [vec] (sort vec)))
                       (sort-by first))
        type-4    (->> (map (fn [prop-id] (conj (z-using (pids-1 prop-id) prop2z) (- prop-id))) prop-ids)
                       (mapv (fn [vec] (sort-by #(Math/abs %) vec)))
                       (sort-by #(-> % first Math/abs)))
        clause-vecs (-> (vector type-1) (into type-2) (into type-3) (into type-4))]
    (hard-clause-wdimacs kb clause-vecs)))

(defn wdimacs-string
  "Create the wdimacs problem (string) from the pclauses and the hard-conjunction.
   How to read the string: instances that are exact opposites acquire the penalty."
  [kb & {:keys [commented?]}]
  (let [pclauses  (remove :remove? (:pclauses kb))
        {:keys [h-wdimacs
                hard-cost
                n-hclauses
                n-vars]} (proof-vec-hard-clause-wdimacs kb)
        p-wdimacs (cond->> (map #(one-clause-wdimacs kb % :commented? commented?) pclauses)
                    commented? (map (fn [num line] (cl-format nil "~2A: ~A" num line))
                                    (range 1 (-> pclauses count inc))))
        result (cl-format nil "p wcnf ~A ~A ~A~%~A~%~{~A~^~%~}"
                          n-vars                           ; number of variables in the problem
                          (+ (count pclauses) n-hclauses)  ; number of equations in the problem
                          hard-cost
                          h-wdimacs
                          p-wdimacs)]
    (swap! diag2 #(assoc % :wdimacs result))
    result))

(defn make-not-head-pclauses
  "Create all the pclauses (maps) for the argument rule and ground facts
   where these facts are the proposition forms of prop-id."
  [kb nhrule gfacts]
  (let [subs (query-cform (:tail nhrule) gfacts)]
    (->> subs
         (reduce (fn [pcs sub]
                   (let [cnf (uni/subst (:cnf nhrule) sub)]
                     (conj pcs
                           {:cnf cnf
                            :prob (:prob nhrule)
                            :type :rule
                            :id (-> (str "pc-" (swap! (-> kb :vars :pclause-count) inc) "-nh"))
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
   Purposes of these rules include (1) enforcing disjointed types of individuals,
   and (2) enforcing anti-symmetric relations. The latter cannot be done with ordinary
   rules because inference won't stop."
  [kb]
  (let [not-heads (filter #(-> % :head form2lit :neg?) (->> kb :rules vals))
        ground-facts (->> kb :pclauses unique-preds)]
    (mapcat #(make-not-head-pclauses kb % ground-facts) not-heads)))

(defn walk-rules
  "Return vectors of vectors of 'path-maps' that result from navigating each proof and collecting what is asserted.
   Each path-map has a :step that describes one step in the naviatation.
   [[{:step <a ground atom> :rule? true}...],...,[{:step <a ground atom>...}...]]

   When, in the naviagation, a 'role' can be achieved by multiple assertions, the path is duplicated,
   one for each role-filler, and navigation continues for each new path individually.
   The nodes (:step) navigated are 'heads' 'observations' 'facts' and 'assumptions'."
  [proofs]
  (letfn [(pick-key [form]
            (cond (:rule-used? form) :rule?
                  (:observation-used? form) :observation?
                  (:fact-used? form) :fact?
                  (:assumption-used? form) :assumption?))
          (walk-rule [rule path]
            (let [rule-id (:rule-used rule)
                  lhs (:proving rule)]
              #_(when-not (ground? lhs) ; 2023-11-25 commented out. core_test (explain/walk-rules tiny)
                (throw (ex-info "Predicate is not ground (1)" {:rule rule :path path})))
              (loop [roles (:decomp rule)
                     new-paths (vector (conj path {:step lhs :rule? true :rule-id rule-id}))]
                (if (empty? roles)
                  new-paths
                  (recur
                   (rest roles)
                   (let [result (atom [])]
                     (doseq [rhs-proof (-> roles first :proofs)
                             old-path new-paths]
                       (if (:rule-used? rhs-proof)
                         (swap! result into (walk-rule rhs-proof old-path))
                         (do
                           (when-not (ground? (:prvn rhs-proof))
                             ;(reset! diag {:prvn (:prvn rhs-proof)})
                             (throw (ex-info "Predicate is not ground (2)" {:prvn (:prvn rhs-proof) :rhs-proof rhs-proof})))
                           (swap! result conj (conj old-path (-> {}
                                                                 (assoc :step (:prvn rhs-proof))
                                                                 (assoc (pick-key rhs-proof) true)
                                                                 (assoc :rule-id rule-id)))))))
                     @result))))))]
     (mapcat #(if (:rule-used? %) (walk-rule % []) (vector (:prv %))) proofs)))

(defn winnow-regardless
  "Remove all proofs containing predicate symbols on (:eliminate-assumptions kb) that
   are used as assumptions."
  [kb pvecs]
  (if-let [elim (not-empty (-> kb :eliminate-assumptions))]
    (let [start-count (count pvecs)
          eliminate? (set elim)
          result (remove (fn [pvec] (some #(and (:assumption? %) (eliminate? (-> % :step first))) pvec)) pvecs)]
      (log/info "Removed" (- start-count (count result)) "proofs with assumptions" elim)
      result)
    pvecs))

;;;   The set is winnowed down to the
;;;   kb's :elimination-threshold by selectively removing members that contains
;;;   assumptions from the :elimination-order. :no-kb-tasks is for debugging.
(defn winnow-by-priority
  "If there are more than :elimination-threshold proofs, remove those that
   include assumptions that involve predicate symbols in :elimination-order
   until the theshold is met or you run out of symbols on :elimination-order."
  [kb pvecs]
  (let [threshold (:elimination-threshold kb)]
    (loop [order (:elimination-priority kb)
           pvecs pvecs]
      (let [cnt (count pvecs)]
        (if (or (empty? order) (< cnt threshold)) pvecs
            (let [pred-sym (first order)
                  smaller (remove (fn [pvec] (some #(and (:assumption? %) (= pred-sym (-> % :step first))) pvec)) pvecs)]
              (when-not (zero? (- cnt (count smaller)))
                (log/info "Removed" (- cnt (count smaller)) "proofs containing assumption" pred-sym))
              (recur (rest order) smaller)))))))

(defn distinct-proof-vecs
  "Filter out duplicates in the sense of two or more have the same :pvec.
   This is possible owing to using different rules towards the same end
   (e.g. rules about symmetric arguments)."
  [pvecs]
  (let [by-pvec (group-by :pvec (vals pvecs))]
    (->> (reduce-kv (fn [res _ pv] (conj res (first pv))) [] by-pvec)
         (reduce (fn [res pv] (assoc res (:proof-id pv) pv)) {}))))

(defn collect-proof-vecs
  "Collect vectors describing how each proof navigates :raw-proofs to some collection of
   grounded LHSs, facts and assumptions.
   The :steps is a depth-first navigation of the proof: each form of the rhs of the of a rule
   is expanded completely onto :steps before moving expanding the next form of the rhs."
  [kb]
  (let [observations (conj (:observations kb) (:query kb))
        result (as-> (walk-rules (-> kb :raw-proofs :proofs)) ?pvecs
                 (winnow-regardless kb ?pvecs)
                 (winnow-by-priority kb ?pvecs)
                 (zipmap (map #(keyword (str "proof-" %)) (range 1 (inc (count ?pvecs)))) ?pvecs)
                 (reduce-kv (fn [res id pvec] (assoc res id {:proof-id id :steps pvec})) {} ?pvecs)
                 ;; This one makes the 'pvec proper' used for prop-ids and MaxSAT generally.
                 (reduce-kv (fn [res proof-id pvec-map]
                              (assoc res proof-id
                                     (assoc pvec-map :pvec
                                            (-> (remove (fn [pred] (some #(= pred %) observations))
                                                        (->> pvec-map :steps (map :step)))
                                                distinct))))
                            {} ?pvecs)
                 (distinct-proof-vecs ?pvecs))]
    (when (empty? result)
      (throw (ex-info "No proof vecs remaining." {})))
    (swap! diag2 #(assoc % :proof-vecs result))
    result))

;;;=================================================================================================
;;;======================  Proof Generation  =======================================================
;;;=================================================================================================
;;; Starting at the top-level :prv (the :query) :
;;;   1) Use the query and bindings from the LHS to create tailtab.
;;;   2) Create the cartesian product of the relevant data.
;;;   3) Loop through:
;;;       a) Create the transducer (for a rule).
;;;       b) Run it on its rule-product.
;;;   4) post-process (e.g. generate a subtree with rule use, facts, assumptions)
(defn bindings+
  "Unify each of form in the fact-set against the tail (they are in the same order).
   If the form has a cvars return them as binding to themselves."
  [fact-set tail]
  (doall (map (fn [form fact]
                (let [cvars (collect-vars form)
                      binds (uni/unify form fact)
                      bkeys (keys binds)]
                  (reduce (fn [res cvar]
                            (if (some #(= cvar %) bkeys)
                              res
                              (assoc res cvar cvar)))
                          binds
                          cvars)))
                  fact-set tail)))

;;; (consistent-bindings? '((p-1 x-1) (p-2 y-1) (p-3 x-1 z-2)   (p-4 y-1 z-bogo)) (-> ppp :rules vals first :tail)) ; false
;;; (consistent-bindings? '((p-1 x-1) (p-2 y-1) (p-3 x-1 z-2)   (p-4 y-1 ?z-r1))  (-> ppp :rules vals first :tail)) ; true
;;; (consistent-bindings?  (varize '((py/sheetName ?x-r3) (ta/isType ta/DemandType) (ta/simMatchExcelSheet workers_on_ws ta/DemandType))
;;;                        (varize '[(py/sheetName ?x-r3) (ta/isType ?type-r3) (ta/simMatchExcelSheet ?x-r3 ?type-r3)]) ; fails because incomplete substitution.
(defn consistent-bindings?
  "The inside of the rule product transducer it filters inconsistent bindings AND incomplete bindings.
   An incomplete binding is where a variable is bound in one form and not in another."
  [fact-set tail]
  (let [binds+ (bindings+ fact-set tail)
        combos (combo/combinations binds+ 2)]
    (and (reduce (fn [still-true? [m1 m2]]
                   (if (not still-true?) false
                       (let [common-keys (filter #(contains? m2 %) (keys m1))]
                         (every? #(let [m1-val (get m1 %)
                                        m2-val (get m2 %)]
                                    (or #_(cvar? m1-val)
                                        #_(cvar? m2-val)
                                        (= m1-val m2-val))) ; incomplete means even cvars must match
                                 common-keys))))
                 true
                 combos))))

;;; (filter-rule-product-transducer (-> ppp :rules vals first :tail))
(defn filter-rule-product-transducer
  "If not provided with data, return a transducer that can be run on a lazy-seq etc.
   to filter out tuples that don't consistently bind to the rule's RHS.
   With data (for debugging), it runs that filter."
  [tail & {:keys [data]}] ; data for debugging.
  (if data
    (filter #(consistent-bindings? % tail) data)
    (filter #(consistent-bindings? % tail))))

(defn tailtab
  "For each rule in which the head binds with the query, create a map indexed by the predicate symbols
   of tails of rules whose head unifies with the argument query. The map values substitute bindings of
   the unification into the predicates of the tail."
  [kb query]
  (let [cnt (atom 0)]
    (reduce (fn [res rule]
              (reset! cnt 0)
              (if-let [binds (uni/unify query (:head rule))]
                (reduce (fn [r pred]
                          (update-in r (list (:id rule) (vector (swap! cnt inc) (first pred)))
                                     #(conj % (uni/subst pred binds))))
                        res
                        (:tail rule))
                res))
            {}
            (-> kb :rules vals))))

;;; There is a good test of this in explain_test.clj
(defn consistent-cvar-naming
  "The naming of cvars in facts can be whatever. It needs to be uniform for rule-product.
   This takes a vector of 'data' for a particular predicate (which because facts can have
   cvars isn't exactly data) and applies the rule's cvar naming convention."
  [kb rule-id ix pred-data]
  (let [rule-form (-> kb :rules rule-id :tail (nth (dec ix)))]
    (reduce (fn [res form]
              (conj res (map #(if (cvar? %1) %2 %1) form rule-form)))
            []
            pred-data)))

;;; POD I think I might already have something like this!
(defn complete-bindings
  "The Cartesian product created by rule-product can produce binding setst that are not complete. For example:
   ((py/linkBack demand Demand) (ta/conceptRefScheme ta/DemandType demand) (ta/conceptVar ta/DemandType demand) (ta/conceptDF ta/DemandType ?y-r2))
   Where the first predicate here binds ?y-r2 to demand. This function returns these predictes (a RHS) with all variables bound."
  [tail preds]
  (let [bindings (uni/unify preds tail)]
    (if bindings
      (uni/subst preds bindings)
      ;; otherwise inconsistent and will be caught later.
      preds)))

;;; POD I think this needs to handle NOT.
;;; (rule-product eee :rule-4 (:rule-4 (tailtab eee '(ta/conceptType ta/DemandType demand))))
;;; (rule-product eee :rule-2 (:rule-2 (tailtab eee '(ta/conceptType ta/DemandType demand))))
(defn rule-product
  "Return a lazy sequence that is the Cartesian product of literals relevant to the query and rule.
   Literals are relevant to the query if
    (1) they are values in the rule's tailtab, or
    (2) they are datatab elements that unify with (non-ground) value in the tailtab.
  rule-tailtabe is the tailtab map for one rule (the one corresponding to :rule-id."
  [kb rule-id rule-tailtab]
  (let [tail (-> kb :rules rule-id :tail)
        datatab (:datatab kb)
        sets (reduce (fn [plustab rt-key]
                       (let [[ix _] rt-key]
                         ;;#p pred-sym
                         (->> (update plustab rt-key
                                      into
                                      (reduce (fn [res lit] ; lit is really a predicate form.
                                                (if (ground? lit)
                                                  res
                                                  (into res
                                                        (filter #(uni/unify lit %)
                                                                (consistent-cvar-naming
                                                                 kb rule-id ix (get datatab (first lit)))))))
                                              []
                                              (get rule-tailtab rt-key)))
                              (reduce-kv (fn [m k v] (assoc m k (distinct v))) {}))))
                     rule-tailtab
                     (keys rule-tailtab))]
    ;; There WAS a lazy sequence here (for transducer below)
    (->> (apply combo/cartesian-product (vals sets))
         (map #(complete-bindings tail %)))))

;;; (rhs-binding-infos ppp '(p-lhs x-1 y-1))
;;; (rhs-binding-infos eee '(ta/conceptType ta/DemandType demand))
;;; (rhs-binding-infos eee '(ta/conceptSheet ta/DemandType ?y-r2))
(defn rhs-binding-infos
  "This is called when prv is the LHS of at least one rule.
   It returns the RHSs that match it and the data, where those RHSs
   could require further expansion of rules or terminate in facts and assumptions.
   Thus it provides 'one step' of a proof." ; POD I don't think prv needs to be ground
  [kb prv]
  (let [tailtab (tailtab kb prv)]
    (as-> (reduce (fn [res rule-id]
                    (let [tail (-> kb :rules rule-id :tail)]
                      (assoc res rule-id
                             (into [] (filter-rule-product-transducer tail)
                                   (rule-product kb rule-id (rule-id tailtab))))))
                  {}
                  (keys tailtab)) ?pset-maps
      ?pset-maps
      ;; If the RHSs include an instance that is all ground, the non-ground ones must go.  POD right?
      (reduce-kv (fn [res rule-id psets]
                   (if (some ground? psets)
                     (assoc res rule-id (filter ground? psets))
                     (assoc res rule-id psets)))
                 {}
                 ?pset-maps)
      ;; Update the maps to show bindings
      (reduce-kv (fn [res rule-id psets]
                   (let [tail (-> kb :rules rule-id :tail)]
                     (assoc res rule-id
                            (mapv #(-> {}
                                       (assoc :rhs %)
                                       (assoc :bindings (uni/unify tail %)))
                                  psets))))
                 {}
                 ?pset-maps))))

(def scope-debugging? false)
(def binding-stack (atom '()))
(defn reset-scope-stack [] (reset! binding-stack '()))

(defmacro dbg-scope
  [& args]
  `(when scope-debugging?
     (println (util/nspaces (* 4 (dec (count @binding-stack)))) ~@args)))

(defn push-scope
  "Push the bindings on the top of the stack. Returns the argument."
  [bindings]
  (swap! binding-stack conj bindings)
  (dbg-scope "Push scope: level=" (count @binding-stack) "top scope now=" (first @binding-stack))
  (let [cnt (atom (count @binding-stack))]
    ;(println "binding-stack = " @binding-stack)
    (doseq [binds @binding-stack]
      (dbg-scope "Stack level" @cnt ":" binds)
      (swap! cnt dec)))
  (first @binding-stack))

(defn pop-scope
  "Pop from scope, return the new top scope."
  []
  (let [level (count @binding-stack)]
    (dbg-scope "Popping scope level" level "discarding bindings" (first @binding-stack) "top scope now="
               (second @binding-stack))
    (swap! binding-stack rest)
    (let [cnt (atom (count @binding-stack))]
      ;(println "binding-stack = " @binding-stack)
      (doseq [binds @binding-stack]
        (dbg-scope "Stack level" @cnt ":" binds)
        (swap! cnt dec)))
    (first @binding-stack)))

(defn merge-bindings
  "Add argument bindings to the top of stack, return this augmented top of stack.
   This one gets called by all add-assumption, observation-solve?, fact-solve? "
  [bindings & {:keys [source]}]
  (swap! binding-stack #(conj (rest %) (merge (first %) bindings)))
  (dbg-scope "merged bindings(" source "), level" (count @binding-stack) "top scope now=" (-> binding-stack deref first))
  (first @binding-stack))

(defn progressive-bind
  "This is just uni/subst with dbg-scope so that I can see what's going on."
  [prv bindings]
  (let [result (uni/subst prv bindings)]
    (dbg-scope "Progressive bind" result "level" (count @binding-stack) "prv=" prv "bindings=" bindings)
    result))

(defn top-scope [] (first @binding-stack))

(defn observation-solve?
  [kb prv]
  (->> kb
       :observations
       (map #(when-let [subs (uni/unify prv %)]
               (when-not (empty? subs) (merge-bindings subs :source "OBS"))
               (cond->  {:prvn (uni/subst prv subs)}
                 (not-empty subs) (assoc :bindings subs))))
       (remove empty?)
       not-empty))

(defn fact-solve?
  "Return a list of facts if the argument can be proved by reference to a fact."
  [kb prv]
  (->> kb
       :facts
       vals
       (map #(-> % :cnf first lit2form))
       (map #(when-let [subs (uni/unify prv %)]
               (when-not (empty? subs) (merge-bindings subs :source "FACT"))
               (cond->  {:prvn (uni/subst prv subs)}
                 (not-empty subs) (assoc :bindings subs)))) ; Bindings need to go into scope, but not here!
       (remove empty?)
       not-empty))

(defn add-assumption
  "Find a kb assumption that will unify with form, or create a new one
   and add it to the (:assumptions-used kb) atom."
  [kb form]
  (if-let [subs (some #(uni/unify form %) (-> kb :assumptions-used deref vals))]
    (do (when-not (empty? subs) (merge-bindings subs :source "ASSUM"))
        {:form form :subs subs})
    (let [name (keyword (str "assume-" (swap! (-> kb :vars :assumption-count) inc)))
          skol (skolemize kb form)]
      (when-not (empty? (:subs skol)) (merge-bindings (:subs skol) :source "ASSUM"))
      (swap! (:assumptions-used kb) #(assoc % name (:form skol)))
      skol)))

(defn prv-with-rule-vars
  "Return prv (the current goal in the proof) with var names as
   required by the rule to be applied and values undisturbed."
  [prv rule sol]
  (when-not (= (first prv) (-> rule :head first))
    (throw (ex-info "prv-with-caller-binds" {})))
  ;{:pre [(= (first prv) (-> rule :head first))]}
  (let [{:keys [head tail]} rule
        lhs (map (fn [l h] (if (cvar? l) h l)) prv head)
        subs (uni/unify tail (:rhs sol))]
    (uni/subst lhs subs)))

(defn consistent-call?
  "RHS of caller could have multiple calls to the same predicate. One should have bindings
   tht match the bindings of the called."
  [call-info]
  ;(swap! diag conj call-info) ; very useful!
  (if (:caller call-info)
    (let [caller-binds (-> call-info :caller :bindings)
          called-binds (-> call-info :called :bindings)
          ;; {} is a perfect match on ground, not a failure!
          equiv-var-map (->> (uni/unify (-> call-info :caller :sol) (-> call-info :called :lhs))
                             (reduce-kv (fn [res k v] (if (cvar? v) (assoc res k v) res)) {}))]
      ;; Bindings must match if both are bound.
      (every? (fn [[caller-var called-var]]
                (if (and (contains? caller-binds caller-var)
                         (contains? called-binds called-var)) ; POD need I check that the called has more bindings?
                  (= (get caller-binds caller-var)
                     (get called-binds called-var))
                  true))
              equiv-var-map))
    true))

(defn consistent-calls?
  "Run consistent-call filtering on solutions.
   It has fancy map args for easier debugging."
  [sols caller rule]
  (filter #(consistent-call? {:caller caller
                              :called {:rule-id (:id rule)
                                       :lhs (:head rule)
                                       :bindings (:bindings %)}})
          sols))

(defn prove-fact
  "Recursively develop a tree that can be interpreted to one or more proofs of the argument. "
  [kb {:keys [prv caller] :as proof}]
  (dbg-scope "PROOF FOR" prv "caller=" caller)
  (let [proof (assoc proof :proofs [])
        heads (->> kb :rules vals (map :head))
        bound (atom nil)]
    (cond (reset! bound (observation-solve? kb prv))
          (update proof :proofs into (map #(assoc % :observation-used? true) @bound))
          (reset! bound (fact-solve? kb prv))
          (update proof :proofs into (map #(assoc % :fact-used? true) @bound)),
          (some (fn [head] (uni/unify head prv)) heads)
          (let [result (update proof :proofs into
                               (reduce-kv
                                (fn [res rule-id sols]
                                  (let [rule (-> kb :rules rule-id)
                                        real-sols (consistent-calls? sols caller rule)]
                                    (into res
                                          (doall
                                           ;; A few challenges here:
                                           ;; (1) Some rhs-binding-infos won't be legit given the bindings. Thus caller and consistent-calls? above.
                                           ;; (2) prv will have the caller's variable naming; needs this rule's var names. (See prv-with-rule-vars.)
                                           ;; (3) Progressive binding: the bindings from RHSs on the left need to be substituted into RHSs on the right.
                                           (map (fn [sol]
                                                  (dbg-scope "Enter rule" rule-id)
                                                  (push-scope (merge (top-scope) (:bindings caller)))
                                                  (merge-bindings (:bindings sol) :source rule-id)
                                                  (let [prv-renamed (prv-with-rule-vars prv rule sol)
                                                        rule-result (as-> {} ?r
                                                                        (assoc ?r :rule-used? true)
                                                                        (assoc ?r :rule-used rule-id)
                                                                        (assoc ?r :proving prv-renamed)
                                                                        (assoc ?r :rhs-queries sol) ; POD problem here that each component might be in a
                                                                        (assoc ?r :decomp
                                                                               (doall (mapv (fn [prv]
                                                                                              (let [prv (progressive-bind prv (top-scope))]
                                                                                                (merge-bindings (merge (:bindings sol) (:bindings caller)) :source prv)
                                                                                                (prove-fact kb {:prv prv ; top-scope is thereby progressively updated..., I think!
                                                                                                                :caller {:rule-id rule-id :sol prv :bindings (merge (top-scope) (:bindings sol))}})))
                                                                                            (:rhs sol))))
                                                                        (update-in ?r [:rhs-queries :bindings] #(merge % (top-scope))))]
                                                    (pop-scope)
                                                    (dbg-scope "Exit rule" rule-id)
                                                    rule-result))
                                                real-sols)))))
                                []
                                (rhs-binding-infos kb prv)))] ; These are 'proof-vecs steps' with binding information
            result)
          :else
          (let [{:keys [subs form]} (add-assumption kb prv)]
            (update proof :proofs conj {:assumption-used? true :prvn (uni/subst form subs)})))))

;;; POD This might not be sufficient; might need to search deep for bindings???
(defn find-binding-sets
  "Return a vector of cvar binding maps."
  [proof]
  (let [raw-maps (loop [rhsides (:decomp proof)
                        bindings []]
                   (if (empty? rhsides)
                     bindings
                     (let [rhs (first rhsides)]
                       (recur (rest rhsides)
                              (into bindings (map #(if % (uni/unify (:prv rhs) %) {})
                                                  (map :prvn (:proofs rhs))))))))]
    (->> raw-maps
         (filter not-empty)
         distinct)))

;;; POD This might be used in grounding :proving, or :prvn, or it might be a waste of time!
(defn set-binding-sets
  "If the argument is a proof with a non-ground :proving,
   find bindings deeper in the proof and set :binding-sets."
  [proof]
  (if-let [cvars (-> proof :proving collect-vars not-empty)]
    (let [binding-sets (find-binding-sets proof)]
      (when-not (every? #(= cvars (-> % keys set)) binding-sets)
        (log/error "Incomplete binding set on " (:rule-used proof) (:proving proof)))
      (assoc proof :binding-sets binding-sets))
    proof))

;;; POD does this need to look at cartesian product of bindings??? I think so.
;;; (expand-proof-bindings expand-test)
(defn add-proof-binding-sets
  "Walk through the proof adding a :binding-sets property"
  [raw-proofs]
  (letfn [(apbs-aux [proof]
            (if (:rule-used? proof)
              (-> (set-binding-sets proof)
                  (update :decomp (fn [dcmp]
                                    (mapv (fn [comp]
                                            (update comp :proofs #(mapv (fn [pf] (apbs-aux pf)) %)))
                                            dcmp))))
              proof))]
    (update raw-proofs :proofs #(mapv apbs-aux %))))

(defn datatab
  "Group-by observations and facts by their predicate-symbol"
  [kb]
  (let [data (-> []
                 (into (:observations kb))
                 (into (map #(-> % :cnf first :pred) (vals (:facts kb)))))]
    (group-by first data)))

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

(defn info-for-game
  "Produce a map of properties to merge into the kb to adjust it for a game.
   A game is a collection of proof-ids."
  [kb game & {:keys [pretty-analysis?]}]
  (reset! diag kb)
  (as-> {} ?game-kb
    (assoc ?game-kb :game game)
    (assoc ?game-kb :vars (:vars kb))
    (assoc ?game-kb :proof-vecs
           (reduce (fn [res pf-id] (assoc res pf-id (-> kb :proof-vecs pf-id)))
                   {}
                   game))
    (assoc ?game-kb :prop-ids (get-prop-ids (:proof-vecs ?game-kb)))
    (assoc ?game-kb :pclauses
           (reduce (fn [res pf-id]
                     (into res (filter #((:used-in %) pf-id)) (:pclauses kb)))
                   #{} ; A set or you will get one copy for every proof in which the clause is used.
                   game))
    (update ?game-kb :pclauses (fn [pcs] (mapv #(set-pclause-prop-ids
                                                 % (:prop-ids ?game-kb) game)
                                               pcs)))
    (assoc  ?game-kb :z-vars (z-vars ?game-kb))
    (assoc  ?game-kb :wdimacs (wdimacs-string ?game-kb))
    (if pretty-analysis?
      (as-> ?game-kb ?g2
        (update ?g2 :pclauses (fn [pcs] (mapv (fn [pc] ; POD This sorting for pretty wdimacs?
                                                (update pc :cnf
                                                        (fn [cnf] (vec (sort-by #(-> % :pred :pos) cnf))))) pcs)))
        (update ?g2 :pclauses sort-clauses)
        (assoc  ?g2 :wdimacsc (wdimacs-string ?g2 :commented? true)))
      ?game-kb)))

(def ngames-played (atom 0))

(defn run-one
  ":pclauses has been prepared to run the MAXSAT problem (except for setting pids and :cnf).
   Create the wdimacs and run python-maxsat, setting :mpe."
  [kb game & {:keys [pretty-analysis?]}]
  (swap! ngames-played inc)
  (let [kb (info-for-game kb game :pretty-analysis? pretty-analysis?)]
    (swap! diag2 #(-> %
                     (assoc :prop-ids (:prop-ids kb))
                     (assoc :run-one-kb kb)))
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
              kb (info-for-game kb game)] ; POD was (merge kb (info-for-game kb game))
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
                   ;; POD not exactly the right place to pick up losers, but okay, I think.
                   (update :losers (fn [loo]
                                     (into loo
                                           (if (> (count losers) 2)
                                             (subvec (filterv #(loser-fn (-> kb :proof-vecs % :pvec)) losers) 0 2)
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

(defn add-id-to-comments
  "Each pclause has an id and a comment string; put the id at the front of the comment string."
  [pclauses]
  (mapv (fn [pc] (update pc :comment #(str (name (:id pc)) " " %)))
        pclauses))

;;; (explain '(p-lhs x-1 y-1) ptest)
;;;======================================= Toplevel =========================================
(defn explain
  "Toplevel function to adduce proof trees, generate the MAXSAT problem,
   run it, and translate the result back to predicates."
  [query kb & {:keys[loser-fn max-together] :or {loser-fn identity max-together 10}}]
  (log/info "Starting explanation of" query)
    (as->  kb ?kb
      (finalize-kb ?kb query)
      (clear! ?kb)
      (assoc  ?kb :datatab         (datatab ?kb))
      (assoc  ?kb :raw-proofs      (prove-fact ?kb {:prv query :top? true :caller {:bindings {}}}))
      (update ?kb :raw-proofs     #(add-proof-binding-sets %)) ; not tested much!
      (assoc  ?kb :proof-vecs      (collect-proof-vecs ?kb))
      (assoc  ?kb :pclauses        (collect-pclauses ?kb))
      (update ?kb :pclauses       #(into % (inverse-assumptions ?kb)))
      (update ?kb :pclauses       #(into % (inverse-facts ?kb)))
      (update ?kb :pclauses       #(into % (inverse-rules ?kb)))
      (update ?kb :pclauses       #(into % (add-not-head-pclauses ?kb)))
      (assoc  ?kb :pclauses        (reduce-pclauses-using-observations ?kb))
      (update ?kb :pclauses       #(add-id-to-comments %))
      (assoc  ?kb :save-pclauses   (:pclauses ?kb))
      (run-problem ?kb :loser-fn loser-fn :max-together max-together)))

;;;======================================= Reporting ====================================
(defn report-problem
  "Print the WDIMACS problem with pclause comments."
  [kb stream & {:keys [comments? print-threshold] :or {comments? true print-threshold 100}}]
  (let [num-zvars (-> kb :z-vars count)
        size      (/ (* num-zvars (dec num-zvars)) 2)]
    (if (> size print-threshold)
      (cl-format stream "~%Printing of WDIMACS suppressed owing to the problem being large.~%")
      (if comments?
        (cl-format stream "~A" (or (:wdimacsc kb) (:wdimacs kb)))
        (cl-format stream "~A" (:wdimacs  kb))))))

(defn report-solutions
  "Print an interpretation of the solutions."
  [kb stream & {:keys [solution-number] :or {solution-number 0}}]
  (reset! diag kb)
  (if (> (-> kb :mpe count) solution-number)
    (doseq [sol (:mbe kb)]
      (cl-format stream "~%Cost ~3d: ~A~%" (:pvec sol)))
      ;; No solutions, so just show p-inv
    (cl-format stream "No solution.~2%~{~A~%~}"
               (->> :prop-ids clojure.set/map-invert vec (sort-by first))))
  true)

#_(defn report-solution
  "Print an interpretation of the solutions."
  [kb stream & {:keys [solution-number] :or {solution-number 0}}]
  (if (> (-> kb :mpe count) solution-number)
    (let [sol (-> kb :mpe (nth solution-number))
          p-inv (-> kb :prop-ids clojure.set/map-invert)]
      (cl-format stream "~2%Cost: ~A~%" (:cost sol))
      (doseq [s (:model sol)] ; No more model
         (cl-format stream "~3d ~5A ~A~%" n (pos? n) (get p-inv (Math/abs n))))
      ;; No solutions, so just show p-inv
      (cl-format stream "~2%~{~A~%~}" (->> p-inv vec (sort-by first))))
  true))


(defn report-prop-ids
  [kb stream]
  (cl-format stream "~2%~{~A~%~}" (sort-by second (:prop-ids kb))))

(defn report-scores
  [kb stream]
  (doseq [sol (:mpe kb)]
    (let [;fail-info (fail-list kb (:model sol))
          #_info-strings #_(map #(cl-format nil "~A:[~{~A~^ ~}]" (:cid %) (:pids %)) fail-info)]
      (cl-format stream "~%:cost ~5d :true ~A"
                 (:cost  sol)
                 (->> sol :proof-set (sort-by first))))))

(defn name2num
  "Return the number n of :fact-n or :rule-n."
  [id]
  (when-let [[_ nstr] (re-matches #"^\w+\-(\d+)$" (name id))]
    (read-string nstr)))

(defn report-kb
  [kb stream]
  (doseq [rule (->> kb :rules vals (sort-by #(name2num (:id %))))]
    (cl-format stream "~%~5,3f ~8A :: ~A :- ~{~A ~}"
               (:prob rule) (:id rule) (:head rule) (:tail rule)))
  (doseq [fact (->> kb :facts vals (sort-by #(name2num (:id %))))]
    (cl-format stream "~%~5,3f ~9A :: ~A"
               (:prob fact) (:id fact) (-> fact :cnf first lit2form)))
  ;; ToDo: Bug here on (report-results (explain '(blocked-road plaza) et/blocked-road-kb))
  #_(doseq [assum (->> (-> kb :assumptions-used deref) (sort-by #(name2num (:id %))))]
      (cl-format stream "~%~5,3f ~9A :: ~A"
                 (:prob assum) (:id assum) (-> assum :cnf first lit2form)))
  (cl-format *out* "~{~%~A~}" (:observations kb))
  true)

;;; POD, this is a good candidate for sending to the SPA log!
(defn report-results
  "Print commented WDIMACS, prop-ids and best scores for diagnostics."
  [kb & {:keys [stream] :or {stream *out*}}]
  (if (-> kb :mpe keyword?)
    (:mpe kb)
    (do
      (report-problem   kb stream)
      (report-solutions kb stream)
      (report-prop-ids  kb stream)
      (report-scores    kb stream)
      (report-kb        kb stream))))

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

(defn start-explainlib
  "Call to py/initialize! and whatever else..."
  []
  (py/initialize!))

(defstate explainlib
  :start (start-explainlib))

;;; Temporary testing stuff
;;;(report-results (explain-observation '(alarm plaza) test/alarm-kb))
;;;(report-results (explain-observation '(blocked-road plaza) test/blocked-road-kb))
;;;(report-results (explain-observation '(groupby Table-1 COLA COLB) test/job-kb))
;;;(report-results (explain-observation '(objectiveFnVal CostTable) rule/r1))
;;;(report-results (explain-observation '(objectiveFnVal ActualEffort) rule/r1))

(ns explainlib.core
  (:require
   [clojure.core.unify           :as uni]
   [clojure.math.combinatorics   :as combo]
   [clojure.pprint               :refer (cl-format)]
   [clojure.set                  :as sets]
   [clojure.string]
   [clojure.walk                 :as walk]
   [clojure.spec.alpha           :as s]
   [libpython-clj2.require       :refer [require-python]]
   [libpython-clj2.python        :as py :refer [py.]]
   [mount.core                   :refer [defstate]]
   [explainlib.util               :as util]
   [taoensso.timbre              :as log]))

;;; ToDo:
;;;  1) Refactor pclause generation so that much of it can be done one proof at a time.
;;;  2) Reconsider use of both lits and forms. (Choose one, use meta for the other???)

(require-python '[pysat.examples.rc2 :as rc2])
(require-python '[pysat.formula :as wcnf])

;;; ToDo: All of these need definition
(def default-elimination-threshold       "Remove certain proofs when there are more than this number. See fn winnow-by-priority" 400)
(def default-black-listed-preds          "Gives a warning when used as an assumption; uses default probability."                 #{}) ; ToDo: Useful?
(def default-black-list-probability      "Probability for black-listed assumptions"                                            0.001) ; ToDo: Useful?
(def default-assumption-probability      "Assumptions should have their own probability. Warns when this is used."             0.100)
(def default-requires-evidence?          "A set of predicates symbols for which there is a warning if using an assumption."      #{})
(def default-all-individuals?            "Compute all individuals, not just those that have the query form true."              false)
;;; ToDo: This next one is temporary until I translates such clauses to hard clauses.
(def default-max-clause-probability      "Any clause probability larger than this value gets this value and a warning."     0.999999)

(defn cvar?      [x] (-> x meta :cvar?))

;;; For debugging
(def diag  (atom {}))
(defn break-here [obj]  (reset! diag obj))

;;; facts            = Predicates with associated probability.
;;; observations     = Predicates without associated probability. These are used to simply pclauses. See use of :remove? in several places.
;;; assumptions      = Predicates with associated probability that will be generated to complete the RHS of a rule in the absence of suitable facts or observations.
;;; skolem           = A predicate role that is generated where the a does not otherwise have a binding; it has existential quantification.
;;; ground fact      = A fact that has no unbound roles, skolems allowed.
;;; literal          = A predicate or its negative (not).
;;;                    N.B. currently in the code 'lit' often refers to a CNF-style {:pred (psym r1...rn) :neg? true}, whereas 'form' means (not (psym r1...rn)).
;;; non-empty clause = A clause containint at least one literal
;;; horn clause      = A non-empty disjunctive clause with at most one positive literal.
;;; definite clause  = A non-empty disjunctive clause with exactly one positive literal.
;;; pclause          = A disjunctive clause resulting from the use of a fact, assumption, or rule in a proof or its inverse.
;;;                    The pclause represents the intent of the clause and is used directly to define a weighted MAXSAT constraint, it is not inverted for this purpose.
;;;                    A pclause has CNF, probability and (for debugging) provenance information.
;;;                    The probability of the inverse is 1 - P, where P is the probability of the original clause.
;;; query-form       = A positive literal which is the subject of a probabilistic 'explanation'.
;;; raw proof        = A (typically deeply) nested structure describing use of facts, assumptions and inference to 'explain' the query form.
;;; proof-vec        = A flattened version of a raw proof. It contains :steps and :pvec-props.
;;; game             = A collection of proofs used in a MAXSAT analysis. When a query results in many proofs, subsets of all games compete in a tournament.
;;; factual-not      = A rule can have 'nots' in them; either
;;;                       RHS: (not (bigger-set ?y ?x)) := (bigger-set ?x ?y) or
;;;                       LHS: (alarm ?loc) := (not (burglary ?loc)) (earthquake ?loc)
;;;                    Idea of a factual not is to maintain the fact as a simple list by simply adding :fact/not before the predicate, e.g. (:fact/not bigger-set ?y ?x).
;;;                    To these forms is added meta {:factual-not? true}. These measures are to distinguish such predicates from generated negative literals e.g. in pclauses.
;;;                    Note that (:fact/not ...)-style propositions are also used in pclauses as are their :neg? (Their ordinary form is the positive (:neg? false) and
;;;                    {:cnf [{:pred (:fact/not pred-sym...) :neg? true}]} is allowed and is the double negative of the base proposition (pred-sym ...).
;;;                    Use of :neg? is restricted to pclauses for CNF, not a thing for generation of proofs.

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

(defn varize
  "Respectively, add :cvar? and :factual-not? metadata to variables and :fact/not predicates of obj."
  ([obj] (varize obj ""))
  ([obj suffix]
   (letfn [(vize [obj]
             (cond (and (list? obj) (= (first obj) ':fact/not))       (with-meta (conj (map vize (rest obj)) :fact/not) {:factual-not? true}),
                   (and (symbol? obj) (= \? (-> obj name first)))     (with-meta (-> obj name (str suffix) symbol) {:cvar? true})
                   (list? obj)                                        (map vize obj)
                   (vector? obj)                                      (mapv vize obj)
                   (map? obj)                                         (reduce-kv (fn [m k v] (assoc m (vize k) (vize v))) {} obj)
                   :else                                              obj))]
     (vize obj))))

(defn fact-not?
  "Return the rest of the proposition (the part without the not) the fact is a factual-not."
  [fact]
  (when (and (seq? fact) (-> fact meta :factual-not?))
    (rest fact)))

(defn good-fnot-meta? ; ToDo: Move to env/dev?
  "Walk through a structure and return it untouched if the the fnot propositions have the necessary metadata."
  ([obj] (good-fnot-meta? obj nil))
  ([obj tag]
   (letfn [(c4fn [x]
             (cond (map? x)                                    (reduce-kv (fn [m k v] (assoc m (c4fn k) (c4fn v))) {} x)
                   (vector? x)                                 (mapv c4fn x)
                   (and (seq? x) (= :fact/not (first x)))      (if (s/valid? ::proposition x)
                                                                 x
                                                                 (throw (ex-info "fnot proposition does not have meta:" {:tag tag :specific x :part-of obj})))
                   (seq? x)                                   (map c4fn x)
                   :else                                       x))]
     (doall (c4fn obj)))))

;;; ToDo: I'm not quite happy with this design. Metadata on proposition other than :factual-not? could be lost.
;;;       The conundrum is that propositions are simple objects and I'd like to keep them this way.
;;;       Of course, I could search out all the places this is used and store the metadata before the new object is created.
;;;       There are currently 4 places where this is needed.
(defn reapply-fnot-meta
  "meta on fnot propositions is lost when new propositions are made from old ones. This adds it back."
  [obj]
  (letfn [(mb [x]
             (cond (map? x)                                  (reduce-kv (fn [m k v] (assoc m (mb k) (mb v))) {} x)
                   (vector? x)                               (mapv mb x)
                   (and (seq? x) (= :fact/not (first x)))    (with-meta x (assoc (meta x) :factual-not? true))
                   (seq? x)                                  (map mb x)
                   :else                                      x))]
    (mb obj)))

(defn unify*
  "uni/unify but with additional provisions when :fact/not."
  [x y]
  (s/assert ::proposition x) ; ToDo: only propositions here, right?
  (s/assert ::proposition y)
  (let [x* (if (fact-not? x) (rest x) x)
        y* (if (fact-not? y) (rest y) y)]
    (when (or (= :fact/not (first x*)) (= :fact/not (first y*))) ; ToDo: This check is just for development?
      (log/error ":fact/not without proper metadata: x =" x "y =" y)
      (throw (ex-info ":fact/not without proper metadata:" {:x x :y y})))
    (uni/unify x* y*)))

(defn collect-vars
  "Return a set of all the vars in a argument form"
  [obj]
  (let [accum (atom #{})]
    (walk/postwalk (fn [x] (when (cvar? x) (swap! accum conj x))) obj)
    @accum))

(defn ground?
  [form]
  (and (seq? form)
       (empty? (collect-vars form))))

(defn complement-lit
  "Complement the argument literal."
  [lit]
  (update lit :neg? not))

(defn opposite-lits?
  "Return true if the two literals are complements."
  [lit1 lit2]
  (and (unify* (:pred lit1) (:pred lit2))
       (not= (:neg? lit1) (:neg? lit2))))

(defn form2lit
  "Return a literal. It looks like {:pred (some form) :neg? true|false}.
   Handles only predicates and negated predicates."
  [form]
  (s/assert ::proposition form)
  (let [form (varize form)]  ; BTW varize preserves fnot meta.
    (if (-> form meta :factual-not?)
      {:pred form :neg? false} ; factual-not polarity untouched. (See definition of factual-not above.)
      {:pred form :neg? false})))

#_(defn lit2form
  "Return the literal list form for the argument literal map."
  [lit]
  (varize
   (if (:neg? lit)
     (with-meta (list :fact/not (:pred lit)) {:factual-not? true})
     (:pred lit))))

(defn lit2form
  "Return the literal list form for the argument literal map.
   Note that this doesn't care about polarity. :neg? is a pclause thing."
  [lit]
  (let [pred (:pred lit)]
    (if (= :fact/not (first pred))
      (with-meta pred {:factual-not? true})
      pred)))

(defn rule2cnf ; This ought to be called rule2horn!
  "Return the CNF corresponding to the rule, a vector of literal MAPS."
  [rule]
  (into (vector (form2lit (:head rule)))
        (mapv #(-> % form2lit complement-lit) (:tail rule))))

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

(defn neg-log-cost-fn
  [prob]
  (Math/round (- (* 100.0 (Math/log prob))))) ; ToDo: More significant digits.

(defn neg-log-cost-fn-inv
  "Inverse of neg-log-cost-fn"
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

(defn rewrite-rule-factual-nots
  "This is called by defkb.
   A NOT can be used in the RHS of a rule (See park-kb testcase.)
   (not (pred ?x ?y)) is rewritten as (:fact/not pred ?x ?y) with metadata {:factual-not? true}"
  [rule]
  (update rule :tail
          (fn [tail] (mapv #(if (= 'not (first %))
                              (with-meta
                                (conj (second %) :fact/not)
                                {:factual-not? true
                                 :parent-fact (second %)})
                              %)
                           tail))))

;;; ToDo: This assumes there is a :parent-fact. More work needed if an assumption or observation is being used.
(defn add-facts-for-factual-nots
  "Rule tails can use (not <some predicate>). These are treated as facts in themselves
   In the current implementation there must be a parent fact must exist."
  [facts rules]
  (let [fact-atm (atom (set facts))]
    (doseq [rule rules]
      (doseq [rhs-elem (:tail rule)]
        (when-let [parent (-> rhs-elem meta :parent-fact)]
          (if-let [fmap (some #(when (unify* parent (:fact %)) %) facts)]
            (swap! fact-atm conj {:prob (- 1.0 (:prob fmap)) :fact rhs-elem})
            (log/warn "Factual not (not in RHS of a rule) without corresponding fact:" rhs-elem)))))
    ;; ToDo: Would be nice were they to keep the order in they originally had.
    (-> fact-atm deref vec)))

(def valid-kb-keys "Keys allowed in a defkb declaration."
  #{:rules :facts :observations :eliminate-by-assumptions :elimination-priority :elimination-threshold :cost-fn :inv-cost-fn
    :black-listed-preds :black-list-prob :default-assume-prob :global-disjoint? :requires-evidence? :all-individuals?})

(defmacro defkb
  "A defkb structure is a knowledgebase used in BALP. Thus it isn't yet a BN; that
   will be generated afterwards. Its facts are observations. Each observation is a ground
   literal that will be processed through BALP to generate all proof trees."
  [name doc-string & {:keys [rules facts observations eliminate-by-assumptions elimination-priority elimination-threshold cost-fn inv-cost-fn
                             black-listed-preds black-list-prob default-assume-prob global-disjoint? requires-evidence? all-individuals?]
           :or {rules                      []
                facts                      []
                observations               []
                eliminate-by-assumptions   #{}
                elimination-priority       []
                global-disjoint?           false ; Say this explicitly for default-params map.
                cost-fn                    rc2-cost-fn #_neg-log-cost-fn
                inv-cost-fn                rc2-cost-fn-inv #_neg-log-cost-fn-inv
                all-individuals?           default-all-individuals?
                requires-evidence?         default-requires-evidence?
                elimination-threshold      default-elimination-threshold
                black-listed-preds         default-black-listed-preds
                black-list-prob            default-black-list-probability
                default-assume-prob        default-assumption-probability} :as args}]
  (let [invalid-keys (clojure.set/difference (-> args keys set) valid-kb-keys)]
    (if (not-empty invalid-keys)
      (throw (ex-info (str "Invalid keys in defkb: " invalid-keys) {:invalid invalid-keys}))
      (let [rw-rules (mapv rewrite-rule-factual-nots rules)]
        `(def ~name (identity  {:doc-string ~doc-string
                                :vars {:assumption-count (atom 0)
                                       :num-skolems (atom 0)
                                       :cost-fn ~cost-fn,
                                       :inv-cost-fn ~inv-cost-fn}
                                :params {:all-individuals?           ~all-individuals?
                                         :global-disjoint?           ~global-disjoint?
                                         :black-listed-preds         ~black-listed-preds
                                         :black-list-prob            ~black-list-prob
                                         :default-assume-prob        ~default-assume-prob
                                         :requires-evidence?         ~requires-evidence?
                                         :elimination-threshold      ~elimination-threshold
                                         :elimination-priority       '~elimination-priority
                                         :eliminate-by-assumptions   '~eliminate-by-assumptions}
                                :rules '~rw-rules
                                :facts '~(add-facts-for-factual-nots facts rw-rules)
                                :assumptions-used (atom {})
                                :observations '~observations}))))))


(defkb _blank-kb "This KB is used to define the following default- vars.")
(def default-params (-> _blank-kb :params))
(def default-vars   (-> _blank-kb :vars))

(declare reset-scope-stack)
(defn clear!
  "Put things back the way they are after evaluating defkb."
  [kb]
  (reset-scope-stack)
  (reset! (:assumptions-used kb) {})
  (reset! (-> kb :vars :assumption-count) 0)
  (reset! (-> kb :vars :num-skolems) 0)
  (dissoc kb :raw-proofs :cnf-proofs :pclauses))

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
            (:fact? step)                 (if-let [fact (some #(when (unify* ground-atom (-> % :cnf first :pred)) %) facts)]
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
                                              (assoc ?a :cnf (vector {:pred ground-atom :neg? false}))
                                              (assoc ?a :comment (cl-format nil "~A" ground-atom)))))))

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
      (s/assert ::pclause ?pc))))

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
                    (let [id (get prop-ids (:pred lit))]
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

(defn fact-probability
  "Unify the argument form with the facts and return the probability.
   Truthy is merge of kb :facts :rules and :assumptions."
  [form facts]
  (let [unifies-with (reduce (fn [res f]
                               (if (unify* form (-> f :cnf first :pred))
                                 (conj res (:id f))
                                 res))
                             []
                             (vals facts))]
    (if (== 1 (count unifies-with))
      (-> (get facts (first unifies-with)) :prob)
      (log/warn "Not exactly one  unifier for" form "unifiers:" unifies-with)))) ; ToDo: Fix this.

(defn prop-id2prob
  "Return a map from prop-id integers to probabilities for facts and rules used in a proof.
   This has both polarities of the literal and it has +/- z-vars set to 1.0.
   This is computed for each proof-id because the proofs get to the propositions in the prop-ids through different rules.
   Where a proposition isn't used by the proof (it is a fact and) it is unified with a KB fact."
  [{:keys [proof-vecs prop-ids rules facts assumptions z-vars] :as kb} proof-id]
  (letfn [(get-prob [step]
             (cond (:rule? step)       (-> (get rules (:rule-id step)) :prob)
                   (:fact? step)       (-> (get facts (:fact-id step)) :prob)
                   (:assumption? step) (-> (get assumptions (:assume-id step)) :prob)))]
    (let [truthy (-> facts (merge assumptions) (merge rules))
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
                                  pid (get prop-ids form)]
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

(defn z-not-using
  "Return a vector of Z vals that do not use the argument proposition."
  [prop prop2z]
  (let [zs (set (reduce into [] (vals prop2z)))]
    (vec (sets/difference zs (set (z-using prop prop2z))))))

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
    (mapcat #(make-not-head-pclauses kb % ground-facts) not-heads)))

(defn pick-key [form]
  (cond (:rule-used? form) :rule?
        (:observation-used? form) :observation?
        (:fact-used? form) :fact?
        (:assumption-used? form) :assumption?))

(defn flatten-proof
  "Return a 'path-maps' that result from navigating each proof and collecting what is asserted.
   Each path-map has a :form that describes one step in the naviatation.
   {:form <a ground atom> :rule? true}...],...,[{:form <a ground atom>...}...]

   When, in the naviagation, a 'role' can be achieved by multiple assertions, the path is duplicated,
   one for each role-filler, and navigation continues for each new path individually.
   The nodes (:form) navigated are 'heads' 'observations' 'facts' and 'assumptions'."
  ([proof] (if (:rule-used? proof) ; Typically called at top-level with just the raw-proof like this.
             (flatten-proof proof [])
             (vector (:prv proof))))
  ([rule path]
   (let [rule-id (:rule-used rule)
         lhs (:proving rule)]
     (loop [roles (:decomp rule)
            new-paths (vector (conj path {:form lhs :rule? true :rule-id rule-id}))]
       (if (empty? roles)
         new-paths
         (recur
          (rest roles)
          (let [result (atom [])]
            (doseq [rhs-proof (-> roles first :proofs)
                    old-path new-paths]
              (if (:rule-used? rhs-proof)
                (swap! result into (flatten-proof rhs-proof old-path))
                (swap! result conj (conj old-path (cond-> {} ; It is not using a rule.
                                                    true                   (assoc :form (:prvn rhs-proof))
                                                    true                   (assoc (pick-key rhs-proof) true)
                                                    (:fact-id rhs-proof)   (assoc :fact-id (:fact-id rhs-proof))
                                                    (:assume-id rhs-proof) (assoc :assume-id (:assume-id rhs-proof))
                                                    true                   (assoc :rule-id rule-id)
                                                    true                   (reapply-fnot-meta))))))
            @result)))))))

;;; ToDo: Maybe move the body of this into explain. Thing is, the comment seems nice!
(defn flatten-proofs
  "Collect vectors describing how each proof navigates :raw-proofs to some collection of
   grounded LHSs, facts and assumptions.
   The :steps is a depth-first navigation of the proof: each form of the rhs of the of a rule
   is expanded completely onto :steps before moving expanding the next form of the rhs."
  [raw-proofs]
  (mapcat flatten-proof (:proofs raw-proofs)))

;;; ToDo: Is this reflective of a flaw in the user's KB? Unnecessary?
(defn winnow-by-assumption
  "Remove all proofs containing predicate symbols in (:eliminate-by-assumptions kb) that are used as assumptions."
  [pvecs assume-set]
  (good-fnot-meta? pvecs "winnow-by-assumption (1)")
  (if-let [elim (not-empty assume-set)]
    (let [start-count (count pvecs)
          eliminate? (set elim)
          result (remove (fn [pvec] (some #(and (:assumption? %) (eliminate? (-> % :form first))) pvec)) pvecs)]
      (log/info "Removed" (- start-count (count result)) "proofs with assumptions" elim)
      result)
    pvecs))

;;;   The set is winnowed down to the
;;;   kb's :elimination-threshold by selectively removing members that contains  assumptions from the :elimination-order.
(defn winnow-by-priority
  "If there are more than :elimination-threshold proofs, remove those that
   include assumptions that involve predicate symbols in :elimination-priority
   until the theshold is met or you run out of symbols on :elimination-priority."
  [pvecs threshold priority]
  (loop [order priority
         pvecs pvecs]
      (let [cnt (count pvecs)]
        (if (or (empty? order) (< cnt threshold)) pvecs
            (let [pred-sym (first order)
                  smaller (remove (fn [pvec] (some #(and (:assumption? %) (= pred-sym (-> % :form first))) pvec)) pvecs)]
              (when-not (zero? (- cnt (count smaller)))
                (log/info "Removed" (- cnt (count smaller)) "proofs containing assumption" pred-sym))
              (recur (rest order) smaller))))))

(defn winnow-proofs
  "Process the simple proof-vecs eliminating some proofs according to parameters.
   Add :pvec-props, which lists the propositions used in the proof.
   Return a map keyed by a newly created name for the proof, for example, :proof-1, etc."
  [proof-vecs observations+ {:keys [elimination-threshold elimination-priority eliminate-by-assumptions]}]
  (good-fnot-meta? proof-vecs "winnow-proofs (1)")
  (let [result (as-> proof-vecs ?pvecs
                 (winnow-by-assumption ?pvecs eliminate-by-assumptions)
                 (good-fnot-meta? ?pvecs "winnow-proofs (1.1)")
                 (winnow-by-priority ?pvecs elimination-threshold elimination-priority)
                 (zipmap (map #(keyword (str "proof-" %)) (range 1 (inc (count ?pvecs)))) ?pvecs)
                 (reduce-kv (fn [res id pvec] (assoc res id {:proof-id id :steps pvec})) {} ?pvecs)
                 ;; This one makes the pvec-lits used for prop-ids and MaxSAT generally.
                 (reduce-kv (fn [res proof-id pvec-map]
                              (assoc res proof-id
                                     (assoc pvec-map :pvec-props
                                            (-> (remove (fn [pred] (some #(= pred %) observations+))
                                                        (->> pvec-map :steps (map :form)))
                                                distinct
                                                vec))))
                            {} ?pvecs))]
    (when (empty? result)
      (throw (ex-info "No proof vecs remaining." {})))
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
  ;(good-fnot-meta? fact-set "bindings+ fact-set")
  ;(good-fnot-meta? tail "bindings+ tail")
  (map (fn [form fact]
         (let [cvars (collect-vars form)
               binds (unify* form fact)
               bkeys (keys binds)]
           (reduce (fn [res cvar]
                     (if (some #(= cvar %) bkeys)
                       res
                       (assoc res cvar cvar)))
                   binds
                   cvars)))
       fact-set tail))

;;; (consistent-bindings? '((p-1 x-1) (p-2 y-1) (p-3 x-1 z-2)   (p-4 y-1 z-bogo)) (-> ppp :rules vals first :tail)) ; false
;;; (consistent-bindings? '((p-1 x-1) (p-2 y-1) (p-3 x-1 z-2)   (p-4 y-1 ?z-r1))  (-> ppp :rules vals first :tail)) ; true
;;; (consistent-bindings?  (varize '((py/sheetName ?x-r3) (ta/isType ta/DemandType) (ta/simMatchExcelSheet workers_on_ws ta/DemandType))
;;;                        (varize '[(py/sheetName ?x-r3) (ta/isType ?type-r3) (ta/simMatchExcelSheet ?x-r3 ?type-r3)]) ; fails because incomplete substitution.
(defn consistent-bindings?
  "The inside of the rule product transducer it filters inconsistent bindings AND incomplete bindings.
   An incomplete binding is where a variable is bound in one form and not in another."
  [fact-set tail]
  (let [fact-set (reapply-fnot-meta fact-set)
        binds+ (bindings+ fact-set tail)
        combos (combo/combinations binds+ 2)]
    (reduce (fn [still-true? [m1 m2]]
              (if (not still-true?)
                false
                (let [common-keys (filter #(contains? m2 %) (keys m1))]
                  (every? #(let [m1-val (get m1 %)
                                 m2-val (get m2 %)]
                             (or #_(cvar? m1-val)
                                 #_(cvar? m2-val)
                                 (= m1-val m2-val))) ; incomplete means even cvars must match
                          common-keys))))
            true
            combos)))

;;; (filter-rule-product-transducer (-> ppp :rules vals first :tail))
(defn filter-rule-product-transducer
  "If not provided with data, return a transducer that can be run on a lazy-seq etc.
   to filter out tuples that don't consistently bind to the rule's RHS.
   With data (for debugging), it runs that filter."
  [tail & {:keys [data]}] ; data for debugging.
  ;(good-fnot-meta? tail "frpt tail")
  ;(good-fnot-meta? data "frpt data")
  (if data
    (filter #(consistent-bindings? % tail) data)
    (filter #(consistent-bindings? % tail))))

(defn tailtab
  "For each rule in which the head binds with the query, create a map keyed by [rhs#, predicate-symbol]
   of tails of rules whose head unifies with the argument query.
   The map values substitute bindings of the unification into the predicates of the tail.
   Return, for example, {:rule-1 {[1 burglary] ((burglary plaza)), [2 earthquake] ((earthquake plaza))},...}"
  [kb query]
  (let [cnt (atom 0)]
    (reduce (fn [res rule]
              (reset! cnt 0)
              (if-let [binds (unify* query (:head rule))]
                (reduce (fn [res1 rhs-prop]
                          (let [bare-prop  (or (fact-not? rhs-prop) rhs-prop)
                                bound (uni/subst bare-prop binds)
                                bound (if (fact-not? rhs-prop) (conj bound :fact/not) bound)
                                bound (with-meta bound (meta rhs-prop))]
                            (update-in res1 ; ToDo: Is indexing with (first bare-prop) what I want?
                                       (list (:id rule) (vector (swap! cnt inc) (first bare-prop)))
                                       #(conj % bound))))
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

;;; ToDo: I think I might already have something like this!
(defn complete-bindings
  "The Cartesian product created by rule-product can produce binding setst that are not complete. For example:
   ((py/linkBack demand Demand) (ta/conceptRefScheme ta/DemandType demand) (ta/conceptVar ta/DemandType demand) (ta/conceptDF ta/DemandType ?y-r2))
   Where the first predicate here binds ?y-r2 to demand. This function returns these predictes (a RHS) with all variables bound."
  [tail preds]
  (let [bindings (unify* preds tail)]
    (if bindings
      (uni/subst preds bindings)
      ;; otherwise inconsistent and will be caught later.
      preds)))

;;; ToDo: I think this needs to handle NOT.
;;; (rule-product eee :rule-4 (:rule-4 (tailtab eee '(ta/conceptType ta/DemandType demand))))
;;; (rule-product eee :rule-2 (:rule-2 (tailtab eee '(ta/conceptType ta/DemandType demand))))
(defn rule-product
  "Return a lazy sequence that is the Cartesian product of forms relevant to the query and rule.
   Forms are relevant to the query if
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
                                      (reduce (fn [res form]
                                                (if (ground? form)
                                                  res
                                                  (into res
                                                        (filter #(unify* form %)
                                                                (consistent-cvar-naming
                                                                 kb rule-id ix (get datatab (first form)))))))
                                              []
                                              (get rule-tailtab rt-key)))
                              (reduce-kv (fn [m k v] (assoc m k (distinct v))) {}))))
                     rule-tailtab
                     (keys rule-tailtab))]
    ;; There WAS a lazy sequence here (for transducer below)
    (->> (apply combo/cartesian-product (vals sets))
         (map #(complete-bindings tail %)))))

(defn rhs-binding-infos
  "This is called when prv is the LHS of at least one rule.
   It returns the RHSs that match it and the data, where those RHSs
   could require further expansion of rules or terminate in facts and assumptions.
   Thus it provides 'one step' of a proof." ; ToDo: I don't think prv needs to be ground.
  [kb prv]
  (good-fnot-meta? prv "rhs-binding-infos (1)")
  (let [tailtab (tailtab kb prv)]
    (as-> (reduce (fn [res rule-id]
                    (let [tail (-> kb :rules rule-id :tail)]
                      (assoc res rule-id
                             (into [] (filter-rule-product-transducer tail)
                                   (rule-product kb rule-id (rule-id tailtab))))))
                  {}
                  (keys tailtab)) ?pset-maps
      (reapply-fnot-meta ?pset-maps)
      (good-fnot-meta? ?pset-maps "rhs-binding-infos (1.1)")
      ;; If the RHSs include an instance that is all ground, the non-ground ones must go.  ToDo: right?
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
                                       (assoc :bindings (unify* tail %)))
                                  psets))))
                 {}
                 ?pset-maps)
      (good-fnot-meta? ?pset-maps "rhs-binding-infos (2)"))))

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

(defn merge-bindings!
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
       (map #(when-let [subs (unify* prv %)]
               (when-not (empty? subs) (merge-bindings! subs :source "OBS"))
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
       (reduce (fn [res fact]
                 ;(log/info "fact=" fact "pred meta:" (-> fact :cnf first :pred meta))
                 (conj res
                       (-> {:id (:id fact)}
                           (assoc :form (-> fact :cnf first lit2form)))))
               [])
       (map (fn [fact] (when-let [subs (unify* prv (:form fact))]
                         (when-not (empty? subs) (merge-bindings! subs :source "FACT"))
                         (cond-> (assoc fact :prvn (uni/subst prv subs))
                           (not-empty subs) (assoc :bindings subs))))) ; Bindings need to go into scope, but not here!
       (remove #(-> % :form empty?))
       not-empty))

(defn add-assumption
  "Find a kb assumption that will unify with form, or create a new one
   and add it to the (:assumptions-used kb) atom."
  [kb form]
  (if-let [subs (some #(unify* form %) (-> kb :assumptions-used deref vals))]
    (do (when-not (empty? subs) (merge-bindings! subs :source "ASSUM"))
        {:form form :subs subs})
    (let [name (-> "assume-" (str (swap! (-> kb :vars :assumption-count) inc)) keyword)
          assume (-> (skolemize kb form)
                     (assoc :id name))]
      (when-not (empty? (:subs assume))  (merge-bindings! (:subs assume) :source "ASSUM"))
      (swap! (:assumptions-used kb) #(assoc % name assume))
      assume)))

(defn prv-with-rule-vars
  "Return prv (the current goal in the proof) with var names as
   required by the rule to be applied and values undisturbed."
  [prv rule sol]
  (when-not (= (first prv) (-> rule :head first))
    (throw (ex-info "prv-with-caller-binds" {})))
  ;{:pre [(= (first prv) (-> rule :head first))]}
  (let [{:keys [head tail]} rule
        lhs (map (fn [l h] (if (cvar? l) h l)) prv head)
        subs (unify* tail (:rhs sol))]
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
          equiv-var-map (->> (unify* (-> call-info :caller :sol) (-> call-info :called :lhs))
                             (reduce-kv (fn [res k v] (if (cvar? v) (assoc res k v) res)) {}))]
      ;; Bindings must match if both are bound.
      (every? (fn [[caller-var called-var]]
                (if (and (contains? caller-binds caller-var)
                         (contains? called-binds called-var)) ; ToDo: Check that the called has more bindings?
                  (= (get caller-binds caller-var)
                     (get called-binds called-var))
                  true))
              equiv-var-map))
    true))

(defn consistent-calls?
  "Run consistent-call filtering on solutions.
   It has fancy map args for easier debugging."
  [sols caller rule]
  (-> (filter #(consistent-call? {:caller caller
                                  :called {:rule-id (:id rule)
                                           :lhs (:head rule)
                                           :bindings (:bindings %)}})
              sols)
      distinct))

(declare prove-fact)

(defn rule-solve
  "Prove prv using a rule. This is mutually recursive with prove-fact."
  [kb prv caller]
  (good-fnot-meta? prv "rule-solve")
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
                     (merge-bindings! (:bindings sol) :source rule-id)
                     (let [prv-renamed (prv-with-rule-vars prv rule sol)
                           rule-result (as-> {} ?r
                                         (assoc ?r :rule-used? true)
                                         (assoc ?r :rule-used rule-id)
                                         (assoc ?r :proving prv-renamed)
                                         (assoc ?r :rhs-queries sol) ; ToDo: Problem here that each component might be...??? (lost it)
                                         (assoc ?r :decomp
                                                (doall (mapv (fn [prv]
                                                               ;(log/info "rule-solve: prv=" prv "meta =" (meta prv))
                                                               (let [prv (progressive-bind prv (top-scope))]
                                                                 (merge-bindings! (merge (:bindings sol) (:bindings caller)) :source prv)
                                                                 (prove-fact kb {:prv prv ; top-scope is thereby progressively updated..., I think!
                                                                                 :caller {:rule-id rule-id :sol prv :bindings (merge (top-scope) (:bindings sol))}})))
                                                             (:rhs sol))))
                                         (update-in ?r [:rhs-queries :bindings] #(merge % (top-scope))))]
                       (pop-scope)
                       (dbg-scope "Exit rule" rule-id)
                       rule-result))
                   real-sols)))))
   []
    ;; These are 'proof-vecs steps' with binding information.
    (rhs-binding-infos kb prv)))

(defn prove-fact
  "Used in creating a raw proof, this recursively develop (this is mutually recursive with rule-solve) a tree that
   can be interpreted to one or more proofs of the argument.
   Where suitable rules, observations, and facts aren't found, this adds assumptions."
  [kb {:keys [prv caller] :as proof}]
  (dbg-scope "PROOF FOR" prv "caller=" caller)
  (let [prv (reapply-fnot-meta prv)
        proof (assoc proof :proofs [])
        heads (->> kb :rules vals (map :head))
        bound (atom nil)]
    (good-fnot-meta? prv "prove-fact")
    (cond (reset! bound (observation-solve? kb prv))       (update proof :proofs into (map #(assoc % :observation-used? true) @bound)),
          (reset! bound (fact-solve? kb prv))              (update proof :proofs into (map #(-> %
                                                                                                (assoc :fact-used? true)
                                                                                                (assoc :fact-id (:id %)))
                                                                                           @bound)),
          (some (fn [head] (unify* head prv)) heads)    (update proof :proofs into (rule-solve kb prv caller))
          :else                                            (let [{:keys [subs form id]} (add-assumption kb prv)]
                                                             (update proof :proofs conj (-> {:assumption-used? true}
                                                                                            (assoc :assume-id id)
                                                                                            (assoc :prvn (uni/subst form subs))))))))

;;; ToDo: This might not be sufficient; might need to search deep for bindings???
(defn find-binding-sets
  "Return a vector of cvar binding maps."
  [proof]
  (let [raw-maps (loop [rhsides (:decomp proof)
                        bindings []]
                   (if (empty? rhsides)
                     bindings
                     (let [rhs (first rhsides)]
                       (recur (rest rhsides)
                              (into bindings (map #(if % (unify* (:prv rhs) %) {})
                                                  (map :prvn (:proofs rhs))))))))]
    (->> raw-maps
         (filter not-empty)
         distinct)))

;;; ToDo: This might be used in grounding :proving, or :prvn, or it might be a waste of time!
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

;;; ToDo: Does this need to look at cartesian product of bindings??? I think so.
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
                 (into (->> kb :facts vals (map #(-> % :cnf first :pred)))))]
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
           (reduce (fn [res pf-id]
                     (into res (filter #((:used-in %) pf-id)) (:pclauses kb)))
                   #{} ; A set or you will get one copy for every proof in which the clause is used.
                   game))
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
  [query kb & {:keys[loser-fn max-together observations params] :or {loser-fn identity max-together 10}}]
  (let [observations+ (conj observations query kb)]
    (as->  kb ?kb
      (finalize-kb ?kb query)
      (clear! ?kb)
      (assoc  ?kb :datatab         (datatab ?kb))
      (assoc  ?kb :raw-proofs      (prove-fact ?kb {:prv query :top? true :caller {:bindings {}}}))
      (update ?kb :raw-proofs     #(add-proof-binding-sets %)) ; not tested much!
      (assoc  ?kb :proof-vecs      (flatten-proofs (:raw-proofs ?kb)))
      (update ?kb :proof-vecs     #(winnow-proofs % observations+ params))
      (assoc  ?kb :pclauses        (collect-pclauses ?kb))
      (update ?kb :pclauses       #(into % (inverse-assumptions ?kb)))
      (update ?kb :pclauses       #(into % (inverse-facts ?kb)))
      (update ?kb :pclauses       #(into % (inverse-rules ?kb)))
      (update ?kb :pclauses       #(into % (add-not-head-pclauses ?kb)))
      (assoc  ?kb :pclauses        (reduce-pclauses ?kb))
      (break-here ?kb)
      (update ?kb :pclauses       #(add-id-to-comments %))
      (run-problem ?kb :loser-fn loser-fn :max-together max-together))))

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

(defn solution-props
  "Return a vector of propositions corresponding to the individual's model (a vector of PIDs)."
  [indv prop-ids query]
  (let [pid2prop (-> prop-ids (dissoc query) sets/map-invert)]
    (reduce (fn [res pid]
              (if-let [prop (get pid2prop pid)] (conj res prop) res))
            []
            (:model indv))))

(defn report-solutions
  "Print an interpretation of the solutions."
  [kb stream & {:keys [solution-number] :or {solution-number 0}}]
  (let [num-sols (-> kb :mpe :solutions count)]
    (if (> num-sols solution-number)
      (do (cl-format stream "~%")
          (doseq [sol (-> kb :mpe :solutions)]
            (cl-format stream "~%cost:  ~4d, model: ~A,  satisfies: ~A,  :pvec-props ~A"
                       (:cost sol) (:model sol) (:satisfies-proofs sol)
                       (solution-props sol (:prop-ids kb) (:query kb)))))
      ;; No solutions, so just show p-inv
      (cl-format stream "No solution.~2%~{~A~%~}"
                 (->> kb :prop-ids clojure.set/map-invert vec (sort-by first))))
    true))

(defn report-prop-ids
  [kb stream]
  (let [query (:query kb)]
    (cl-format stream "~%")
    (doseq [prop-id (sort-by second (:prop-ids kb))]
      (if (= query (first prop-id))
        (cl-format stream "~%~A  (The query)" prop-id)
        (cl-format stream "~%~A" prop-id)))
    (cl-format stream "~%")))

(defn name2num
  "Return the number n of :fact-n or :rule-n."
  [id]
  (when-let [[_ nstr] (re-matches #"^\w+\-(\d+)$" (name id))]
    (read-string nstr)))

(defn report-kb
  [kb stream]
  (doseq [rule (->> kb :rules vals (sort-by #(name2num (:id %))))]
    (cl-format stream "~%~5,3f ~9A :: ~A :- ~{~A ~}"
               (:prob rule) (:id rule) (:head rule) (:tail rule)))
  (doseq [fact (->> kb :facts vals (sort-by #(name2num (:id %))))]
    (cl-format stream "~%~5,3f ~9A :: ~A"
               (:prob fact) (:id fact) (-> fact :cnf first lit2form)))
  (doseq [assum (->>  kb :pclauses (filter :assumption?))]
    (cl-format stream "~%~5,3f ~9A :: ~A"
               (:prob assum) (:id assum) (-> assum :cnf first lit2form)))
  (cl-format *out* "~{~%~A~}" (:observations kb))
  true)

(defn really!
  "After saturating the code with doall around :form and getting nowhere, I try this."
  [obj]
  (if (= (type obj) clojure.lang.LazySeq)
    (let [res (cl-format nil "~A" (doall obj))]
      ;(log/info "Really!:" obj "returning res = " res)
      res)
    obj))

(defn report-summary
  [kb stream]
  (letfn [(proof-str [proof-id]
            (let [res (atom "")]
              (doseq [step (-> kb :proof-vecs proof-id :steps)]
                (cond (:rule? step) (swap! res #(str % " " (-> step :rule-id name) ": " (-> step :form really!) " := "))
                      (:fact? step) (swap! res #(str % " " (-> step :form doall) " "))
                      (:assumption? step) (swap! res #(str % " " (-> step :form doall) " "))))
              @res))]
    (cl-format stream "~%")
    (doseq [[proof-id prob] (->> kb :mpe :summary seq (sort-by #(-> % second)) reverse)]
      (cl-format stream "~%~9A : ~8,6f ~A" proof-id prob (proof-str proof-id)))))

(defn report-results
  "Print commented WDIMACS, prop-ids and best scores for diagnostics."
  [kb & {:keys [stream] :or {stream *out*}}]
  (if (-> kb :mpe keyword?)
    (:mpe kb)
    (do
      (report-problem   kb stream)
      (report-solutions kb stream)
      (report-summary kb stream)
      (report-prop-ids  kb stream)
      (report-kb        kb stream))))

(defn start-explainlib
  "Call to py/initialize! and whatever else..."
  []
  (py/initialize!))

(defstate explainlib
  :start (start-explainlib))

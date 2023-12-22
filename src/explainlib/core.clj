(ns explainlib.core
  (:require
   [clojure.core.unify           :as uni]
   [clojure.math.combinatorics   :as combo]
   [clojure.pprint               :refer (cl-format)]
   [clojure.set                  :as sets]
   [clojure.spec.alpha           :as s]
   [clojure.string]
   [explainlib.extra             :as dev] ; ToDo: How do we make this present only in dev environment?
   [explainlib.maxsat            :as maxsat]
   [explainlib.specs             :as specs]
   [explainlib.util              :as util :refer [unify* fact-not? varize collect-vars ground? cvar? reapply-fnot-meta]]
   [taoensso.timbre              :as log]))

;;; ToDo:
;;;  1) Implement :protected.
;;;  2) Remove pclause.id, they aren't unique and we don't need them.
;;;  3) Check if query can be answered by facts.

(def default-elimination-threshold       "Remove certain proofs when there are more than this number. See fn winnow-by-priority" 400)
(def default-black-listed-preds          "Gives a warning when used as an assumption; uses default probability."                 #{}) ; ToDo: Useful?
(def default-black-list-probability      "Probability for black-listed assumptions"                                            0.001) ; ToDo: Useful?
(def default-assumption-probability      "Assumptions should have their own probability. Warns when this is used."             0.100)
(def default-requires-evidence?          "A set of predicates symbols for which there is a warning if using an assumption."      #{})
(def default-all-individuals?            "Compute all individuals, not just those that have the query form true."              false)

;;; For debugging
(def diag  (atom {}))
(defn break-here [obj]  (reset! diag obj))

;;; =========================== Definitions. See also specs.clj ====================================================================================================
;;; facts               = Predicates with associated probability.
;;; observations        = Predicates without associated probability. These are used to simply pclauses. See use of :remove? in several places.
;;; assumptions         = Predicates with associated probability that will be generated to complete the RHS of a rule in the absence of suitable facts or observations.
;;; skolem              = A predicate role that is generated where the a does not otherwise have a binding; it has existential quantification.
;;; ground fact         = A fact that has no unbound roles, skolems allowed.
;;; literal             = A predicate or its negative (not).
;;;                       N.B. currently in the code 'lit' often refers to a CNF-style {:pred (psym r1...rn) :neg? true}, whereas 'form' means (not (psym r1...rn)).
;;; non-empty clause    = A clause containint at least one literal
;;; horn clause         = A non-empty disjunctive clause with at most one positive literal.
;;; definite clause     = A non-empty disjunctive clause with exactly one positive literal.
;;; prop-id             = An non-zero integer representing a proposition or its negation.
;;; props-ids           = a map keyed by every proposition in a proof relating it to a positive integer, the prop-id.
;;; CNF                 = clause normal form (or conjunctive normal form) where the conjunction referred to is of all over all the disjunctive clauses that are 1-1 with rules and facts.
;;;                       Note that a pclause's :cnf is ordered: If the :cnf represents a rule, the rule head is the first map in the vector. (See example below).
;;; pclause             = A disjunctive clause (CNF) resulting from the use of a fact, assumption, or rule in a proof or its inverse.
;;;                       The pclause represents the intent of CNF and the CNF is used directly to define a weighted MAXSAT constraint, it is not inverted for this purpose.
;;;                       For example, with prop-ids = {(cee foo) 1, (dee foo) 2}:
;;;                            (1) a fact (cee ?x), with p=0.300 may be instantiated as (cee foo) in a proof.
;;;                                -- has pclause: {:prob 0.3, :fact? true,  :cnf [{:pred (cee foo), :neg? false, :pos 1}], :comment "fact-1 (cee foo)", :used-in #{:proof-1}}
;;;                                -- has wdimacs: "36       1         0 c fact-1 (cee foo)"
;;;                            (2) a rule (dee ?x-r1) :- (cee ?x-r1)  with p=0.200 means "(cee whatever) implies (dee whatever)."
;;;                                -- has pclause:  {:prob 0.2 :cnf [{:pred (dee foo), :neg? false, :pos 2} {:pred (cee foo), :neg? true, :pos 1}],   :comment "rule-1 :rule-1 {?x-r1 foo} (dee foo)",}
;;;                                -- has wdimacs:  "22      -1    2    0 c rule-1 :rule-1 {?x-r1 foo} (dee foo)"
;;;                                   which means that if an individual violates this rule by having [1 -2] (cee is true but not dee) it picks up the small penalty of 22.
;;;                                   The penalty is small because the the rule only holds p=0.200 of the time.
;;;                       In addition to what is shown here a pclause has proof provenance information and variable binding information.
;;;                       The probability of the inverse is 1 - P, where P is the probability of the original clause.
;;; pclause.applies-to  = A pclause has property :applies-to, which is a vector of the prop-ids for which fact or rule holds.
;;;                       For example, the rule above, (dee ?x-r1) :- (cee ?x-r1) applies to an individual with [1 2] in its model and therefore the probability
;;;                       of an individual
;;; query-form          = A positive literal which is the subject of a probabilistic 'explanation'.
;;; raw proof           = A (typically deeply) nested structure describing use of facts, assumptions and inference to 'explain' the query form.
;;; proof-vec           = A flattened version of a raw proof. It contains :steps and :pvec-props.
;;; game                = A collection of proofs used in a MAXSAT analysis. When a query results in many proofs, subsets of all games compete in a tournament.
;;; factual-not         = A rule can have 'nots' in them; either
;;;                          RHS: (not (bigger-set ?y ?x)) := (bigger-set ?x ?y) or
;;;                          LHS: (alarm ?loc) := (not (burglary ?loc)) (earthquake ?loc)
;;;                       Idea of a factual not is to maintain the fact as a simple list by simply adding :fact/not before the predicate, e.g. (:fact/not bigger-set ?y ?x).
;;;                       To these forms is added meta {:factual-not? true}. These measures are to distinguish such predicates from generated negative literals e.g. in pclauses.
;;;                       Note that (:fact/not ...)-style propositions are also used in pclauses as are their :neg? (Their ordinary form is the positive (:neg? false) and
;;;                       {:cnf [{:pred (:fact/not pred-sym...) :neg? true}]} is allowed and is the double negative of the base proposition (pred-sym ...).
;;;                       Use of :neg? is restricted to pclauses for CNF, not a thing for generation of proofs.


(defn skol-var!
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
   (let [form (uni/subst form subs)
         vars (collect-vars form)
         subs (merge (zipmap vars (doall (map #(skol-var! kb %) vars))) subs)
         form (uni/subst form subs)]
     {:form form :subs subs})))

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
                                #_(assoc  ?r :cnf   (rule2cnf ?r)))]
                     (s/valid? ::specs/rule rule)
                     (assoc rs (:id rule) rule)))
                 {}
                 (zipmap (map #(-> (str "rule-" %) keyword) (range 1 (-> rules count inc)))
                         rules)) ; ToDo: Can we sort rules? See warn-rule-rhs-ordering.
      warn-rule-rhs-ordering))

(defn finalize-facts
  "Augment the argument vector of fact with additional properties,
   returning a map indexed by a sequential name given to each rule."
  [facts]
  (reduce-kv (fn [fs k v]
               (let [fact (assoc v :id  k)]
                 (s/valid? ::specs/fact fact)
                 (-> fs (assoc k fact))))
             {}
             (zipmap (map #(-> (str "fact-" %) keyword) (range 1 (-> facts count inc)))
                     (sort-by #(-> % :form first name) facts))))

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

(def valid-kb-keys "Keys allowed in a defkb declaration."
  #{:rules :facts :observations :eliminate-by-assumptions :elimination-priority :elimination-threshold :cost-fn :inv-cost-fn
    :black-listed-preds :black-list-prob :default-assume-prob :requires-evidence? :all-individuals?})

(defmacro defkb
  "A defkb structure is a knowledgebase used in BALP. Thus it isn't yet a BN; that
   will be generated afterwards. Its facts are observations. Each observation is a ground
   literal that will be processed through BALP to generate all proof trees."
  [name doc-string & {:keys [rules facts observations eliminate-by-assumptions elimination-priority elimination-threshold cost-fn inv-cost-fn
                             black-listed-preds black-list-prob default-assume-prob requires-evidence? all-individuals?]
           :or {rules                      []
                facts                      []
                observations               []
                eliminate-by-assumptions   #{}
                elimination-priority       []
                cost-fn                    maxsat/rc2-cost-fn
                inv-cost-fn                maxsat/rc2-cost-fn-inv
                all-individuals?           default-all-individuals?
                requires-evidence?         default-requires-evidence?
                elimination-threshold      default-elimination-threshold
                black-listed-preds         default-black-listed-preds
                black-list-prob            default-black-list-probability
                default-assume-prob        default-assumption-probability} :as args}]
  (let [invalid-keys (clojure.set/difference (-> args keys set) valid-kb-keys)]
    (if (not-empty invalid-keys)
      (throw (ex-info (str "Invalid keys in defkb: " invalid-keys) {:invalid invalid-keys}))
      (let [rw-rules (mapv rewrite-rule-factual-nots rules)] ; ToDo: Still needed. Why?
        `(def ~name (identity  {:doc-string ~doc-string
                                :vars {:assumption-count (atom 0)
                                       :num-skolems (atom 0)}
                                :params {:cost-fn                    ~cost-fn,
                                         :inv-cost-fn                ~inv-cost-fn
                                         :all-individuals?           ~all-individuals?
                                         :black-listed-preds         ~black-listed-preds
                                         :black-list-prob            ~black-list-prob
                                         :default-assume-prob        ~default-assume-prob
                                         :requires-evidence?         ~requires-evidence?
                                         :elimination-threshold      ~elimination-threshold
                                         :elimination-priority       '~elimination-priority
                                         :eliminate-by-assumptions   '~eliminate-by-assumptions}
                                :rules '~rw-rules
                                :facts '~facts
                                :assumptions-used (atom {})
                                :observations '~observations}))))))

(declare reset-scope-stack)
(defn clear!
  "Put things back the way they are after evaluating defkb."
  [kb]
  (reset-scope-stack)
  (reset! (:assumptions-used kb) {})
  (reset! (-> kb :vars :assumption-count) 0)
  (reset! (-> kb :vars :num-skolems) 0)
  (dissoc kb :raw-proofs :pclauses))

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

;;; We didn't factor this out because it is a good place to stop for debugging.
(defn flatten-proofs
  "Collect vectors describing how each proof navigates :raw-proofs to some collection of
   grounded LHSs, facts and assumptions.
   The :steps is a depth-first navigation of the proof: each form of the rhs of the of a rule
   is expanded completely onto :steps before moving expanding the next form of the rhs."
  [raw-proofs]
  (mapcat flatten-proof (:proofs raw-proofs)))

(defn winnow-by-assumption
  "Remove all proofs containing predicate symbols in (:eliminate-by-assumptions kb) that are used as assumptions."
  [pvecs assume-set]
  ;;(dev/good-fnot-meta? pvecs "winnow-by-assumption (1)")
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
  ;;(dev/good-fnot-meta? proof-vecs "winnow-proofs (1)")
  (let [result (as-> proof-vecs ?pvecs
                 (winnow-by-assumption ?pvecs eliminate-by-assumptions)
                 ;;(dev/good-fnot-meta? ?pvecs "winnow-proofs (1.1)")
                 (winnow-by-priority ?pvecs elimination-threshold elimination-priority)
                 (zipmap (map #(keyword (str "proof-" %)) (range 1 (inc (count ?pvecs)))) ?pvecs)
                 (reduce-kv (fn [res id pvec] (assoc res id {:proof-id id :steps pvec})) {} ?pvecs)
                 ;; This one makes the pvec-lits used for prop-ids and MaxSAT generally.
                 (reduce-kv (fn [res proof-id pvec-map]
                              (assoc res proof-id
                                     (assoc pvec-map :pvec-props
                                            (->> (remove (fn [pred] (some #(= pred %) observations+))
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
  ;;(dev/good-fnot-meta? fact-set "bindings+ fact-set")
  ;;(dev/good-fnot-meta? tail "bindings+ tail")
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
                  (every? #(= (get m1 %) (get m2 %)) common-keys))))
            true
            combos)))

;;; (filter-rule-product-transducer (-> ppp :rules vals first :tail))
(defn filter-rule-product-transducer
  "If not provided with data, return a transducer that can be run on a lazy-seq etc.
   to filter out tuples that don't consistently bind to the rule's RHS.
   With data (for debugging), it runs that filter."
  [tail & {:keys [data]}] ; data for debugging.
  ;;(dev/good-fnot-meta? tail "frpt tail")
  ;;(dev/good-fnot-meta? data "frpt data")
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
  ;;(dev/good-fnot-meta? prv "rhs-binding-infos (1)")
  (let [tailtab (tailtab kb prv)]
    (as-> (reduce (fn [res rule-id]
                    (let [tail (-> kb :rules rule-id :tail)]
                      (assoc res rule-id
                             (into [] (filter-rule-product-transducer tail)
                                   (rule-product kb rule-id (rule-id tailtab))))))
                  {}
                  (keys tailtab)) ?pset-maps
      (reapply-fnot-meta ?pset-maps)
      ;;(dev/good-fnot-meta? ?pset-maps "rhs-binding-infos (1.1)")
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
  ;;(dev/good-fnot-meta? prv "rule-solve")
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
    ;;(dev/good-fnot-meta? prv "prove-fact")
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
                 (into (->> kb :facts vals (map #(:form %)))))]
    (group-by first data)))

;;;======================================= Toplevel =========================================
;;; (-> '(alarm plaza) (explain alarm-kb) :mpe :summary)
(defn explain
  "Toplevel function to generate proof trees and MAXSAT problems, run them, and post-processe results."
  [query kb & {:keys[loser-fn max-together observations params] :or {loser-fn identity max-together 10}}]
  (let [observations+ (conj observations query)]
    (as->  kb ?kb
      (finalize-kb ?kb query)
      (clear! ?kb)
      (assoc  ?kb :datatab         (datatab ?kb))
      (assoc  ?kb :raw-proofs      (prove-fact ?kb {:prv query :top? true :caller {:bindings {}}}))
      (update ?kb :raw-proofs     #(add-proof-binding-sets %)) ; not tested much!
      (assoc  ?kb :proof-vecs      (flatten-proofs (:raw-proofs ?kb)))
      (update ?kb :proof-vecs     #(winnow-proofs % observations+ params))
      (assoc  ?kb :pclauses        (mapcat #(maxsat/generate-pclauses-from-pvec ?kb %) (-> ?kb :proof-vecs vals)))
      (update ?kb :pclauses       #(maxsat/dedupe-pclauses %))
      (update ?kb :pclauses       #(maxsat/add-inverse-pclauses %))
      (assoc  ?kb :pclauses        (maxsat/reduce-pclauses ?kb))
      (update ?kb :pclauses       #(maxsat/add-id-to-comments %))
      (break-here ?kb)
      (maxsat/run-problem ?kb :loser-fn loser-fn :max-together max-together))))

;;;======================================= Reporting ====================================
(defn report-problem
  "Print the WDIMACS problem with pclause comments."
  [kb stream & {:keys [print-threshold] :or {print-threshold 100}}]
  (let [num-zvars (-> kb :z-vars count)
        size      (/ (* num-zvars (dec num-zvars)) 2)]
    (if (> size print-threshold)
      (cl-format stream "~%Printing of WDIMACS suppressed owing to the problem being large.~%")
      (cl-format stream "~A" (maxsat/wdimacs-string kb :commented? true)))))

(defn solution-props
  "Return a vector of propositions corresponding to the model (a vector of PIDs)."
  [model prop-ids query]
  (let [prop-ids-inv (-> prop-ids (dissoc query) sets/map-invert)
        prop-id? (-> prop-ids-inv keys set)]
    (reduce (fn [res pid]
              (if (or (prop-id? pid) (prop-id? (- pid))) ; Ignore z-vars.
                (if (pos? pid)
                  (conj res (get prop-ids-inv pid))
                  (conj res (with-meta (conj (get prop-ids-inv (abs pid)) :fact/not) {:factual-not? true})))
                res))
            []
            model)))

(defn report-solutions
  "Print an interpretation of the solutions."
  [{:keys [mpe params prop-ids query] :as kb} stream]
  (reset! diag kb)
  (cl-format stream "~%")
  (if (:all-individuals? params)
    (do (doseq [{:keys [prob model]} mpe]
          (cl-format stream "~%prob:  ~,5f, model: [~{~3d~^,~}]" prob model))
        (cl-format stream "~% Total probability: ~A" (->> mpe (map :prob) (apply +))))
    (doseq [{:keys [prob model satisfies]} mpe]
      (cl-format stream "~%prob:  ~,5f, model: [~{~3d~^,~}],  satisfies: ~A,  :pvec-props ~A"
                 prob
                 model
                 satisfies
                 (solution-props model prop-ids query))))
  (when (empty? mpe)  (cl-format stream "~%No solution."))
  true)

(defn report-prop-ids
  [kb stream]
  (let [query (:query kb)]
    (cl-format stream "~%")
    (doseq [prop-id (sort-by second (:prop-ids kb))]
      (if (= query (first prop-id))
        (cl-format stream "~%~A  (The query)" prop-id)
        (cl-format stream "~%~A" prop-id)))
    (cl-format stream "~%")))

;;; ToDo: Of course, an objective is to eliminate this!
(defn really!
  "After saturating the code with doall around :form and getting nowhere, I try this."
  [obj]
  (if (= (type obj) clojure.lang.LazySeq)
    (let [res (cl-format nil "~A" (doall obj))]
      ;(log/info "Really!:" obj "returning res = " res)
      res)
    obj))

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
               (:prob fact) (:id fact) (:form fact)))
  (doseq [assum (->>  kb :pclauses (filter :assumption?))]
    (cl-format stream "~%~5,3f ~9A :: ~A"
               (:prob assum) (:id assum) (:form assum)))
  (cl-format *out* "~{~%~A~}" (:observations kb))
  true)

(defn report-summary
  [kb stream]
  (letfn [(proof-str [proof-id]
            (let [res (atom "")]
              (doseq [step (-> kb :proof-vecs proof-id :steps)]
                (cond (:rule? step) (swap! res #(str % " " (-> step :rule-id name) ": " (-> step :form really!) " := "))
                      (:fact? step) (swap! res #(str % " " (-> step :form really!) " "))
                      (:assumption? step) (swap! res #(str % " " (-> step :form doall) " "))))
              @res))]
    (cl-format stream "~%")
    (doseq [[proof-id prob] (->> kb :mpe :summary seq (sort-by #(-> % second)) reverse doall)]
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

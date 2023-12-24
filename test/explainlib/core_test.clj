(ns explainlib.core-test
  "Tests, demonstration and explanation for aspects of the explainlib algorithms."
  (:require
   [clojure.core.unify          :as uni]
   [clojure.set                 :as sets]
   [clojure.spec.alpha          :as s] ; for debugging.
   [clojure.test                :refer [deftest is testing]]
   [explainlib.core             :as core :refer [defkb explain report-results probability-by-proof]]
   [explainlib.maxsat           :as maxsat]
   [explainlib.specs            :as specs] ; for debugging
   [explainlib.util             :as util :refer [varize]] ; for debugging
   [taoensso.timbre             :as log]))

(defn filter-to-simple-mpe
  "Pull out of an executed problem (a kb + execution results) its model and cost (for use in a test)."
  [problem]
  (->> problem :mpe (map #(dissoc % :proof-id)) (sort-by :cost) vec))

(defkb park-kb
  "A KB for testing the problem from Park (2002) 'Using Weighted MAX-SAT engines to solve MPE'. (D is unlikely, C helps a little)."
  :rules [{:prob 0.2 :head (dee ?x)   :tail [(cee ?x)]}               ; 0.200 :rule-1  :: (dee ?x-r1) :- (cee ?x-r1)
          {:prob 0.1 :head (dee ?x)   :tail [(not (cee ?x))]}]        ; 0.100 :rule-2  :: (dee ?x-r2) :- (not (cee ?x-r2))
  :facts [{:prob 0.3 :form (cee ?x)}])                                ; 0.300 :fact-1  :: (cee ?x-f1)

(deftest simple-complete-test
  (testing "Testing a simple complete MPE calculation."
    (let [park-all-kb (-> park-kb (assoc-in [:params :all-individuals?] true))]
      (testing "Testing that park-kb matches hand-calculated values."
        (is (= [{:model [-1, -2], :cost 47,  :prob 0.63}
                {:model [ 1, -2], :cost 142, :prob 0.24}
                {:model [-1,  2], :cost 266, :prob 0.06999999999999999}
                {:model [ 1,  2], :cost 281, :prob 0.06}]
               (-> '(dee foo) (explain  park-all-kb) :mpe)))))))

;;;   C |  P(C)                       C    D   |  P(D|C)                       Probabilities of the individuals
;;;  ---+------                      ----------+----------                          ------
;;;   c |  0.3                        c    d   |   0.2         c ->  d                0.06
;;;  -c |  0.7                        c   -d   |   0.8    INV  c ->  d                0.24
;;;                                  -c    d   |   0.1        -c ->  d                0.07
;;;                                  -c   -d   |   0.9    INV -c ->  d                0.63 (Since these are all possible individuals, the sum is 1.0.)
;;;
;;; Note that the things you get back from MAXSAT are the costs of clauses you violated; lowest cost is the most likely explanation but to
;;; get a probability back you'd have to plug the answer back into the Bayes net.
;;; In this example (park-all-indv below) we use parameter :all-individuals?=true which is useful for validation of small tests like this.
;;; It doesn't provide explanations for D (dee) specifically though.
;;; It is useful in cases where you want something other than the sort of model counting we do when :all-individuals?=false.

;;; Of course, this is sensitive to changes in the reporting code, so don't be surprised if it is commented out.
(deftest park-concept
  (testing "Demonstrating the concept of using a MAXSAT solver for MPE. Demonstrating reporting."
    (testing "The presentation of WDIMACS using report-problem as shown has end comments, which isn't legal syntax."
      (is (= (->> ["p wcnf 4 9 581" ; There are 4 variables, 9 clauses and the sum of the costs + 1 = 581.
                   "581             2              0 c Must answer the query (dee foo)."
                   "581                  3    4    0 c Require at least one of these solutions (defined by the other hard clauses)."
                   "581        1        -3         0 c Sol 3 (:proof-1) implies (cee foo) is true."
                   "581       -1             -4    0 c Sol 4 (:proof-2) implies (cee foo) is false."
                   ""
                   "1 : 120     -1         0 c fact-1 (:fact/not cee foo)"
                   "2 : 36       1         0 c fact-1 (cee foo)"
                   "3 : 22      -1    2    0 c rule-1 :rule-1 {?x-r1 foo} (dee foo)"
                   "4 : 161     -1   -2    0 c rule-1-inv :rule-1 {?x-r1 foo} (dee foo) | INV"
                   "5 : 11       1    2    0 c rule-2 :rule-2 {?x-r2 foo} (dee foo)"
                   "6 : 230      1   -2    0 c rule-2-inv :rule-2 {?x-r2 foo} (dee foo) | INV"
                   ""
                   "prob:  0.070, model: [ -1,  2, -3,  4],  satisfies: [:proof-2],  :pvec-props [(:fact/not cee foo)]"
                   "prob:  0.060, model: [  1,  2,  3, -4],  satisfies: [:proof-1],  :pvec-props [(cee foo)]"
                   "Proof: :proof-2 Probability: 0.070 Propositions: [(:fact/not cee foo)]"
                   "Proof: :proof-1 Probability: 0.060 Propositions: [(cee foo)]"
                   ""
                   "[(cee foo) 1]"
                   "[(dee foo) 2]  (The query)"
                   ""
                   "0.200 :rule-1   :: (dee ?x-r1) :- (cee ?x-r1) "
                   "0.100 :rule-2   :: (dee ?x-r2) :- (:fact/not cee ?x-r2) "
                   "0.300 :fact-1   :: (cee ?x)"]
                  (interpose "\n")
                  (apply str))
             (let [log-vec (atom [])]
               (binding [log/*config* (assoc log/*config* :appenders {:println {:enabled? true :fn #(swap! log-vec conj (-> % :vargs first))}})]
                 (with-out-str (-> (explain '(dee foo) park-kb) (core/report-results *out*))))))))))

;;;==================================== Simple end-to-end MPE =====================================
;;; My interpretation is the ProbLog interpretation.
;;; The ProbLog reading of these is CAUSAL: If +b ^ +e, this  causes an alarm to be true with probabiility 0.9.
;;; Further, the CPT entries that aren't stated are assumed to be zero.
;;; This makes sense from the causal perspective if you assume that you've accounted for all causes.
(defkb alarm-kb
  "A KB for a problem in the ProbLog documentation."
  :rules [{:prob 0.9
           :head  (alarm ?loc)
           :tail  [(burglary ?loc) (earthquake ?loc)]}
          {:prob 0.8
           :head  (alarm ?loc)
           :tail  [(burglary ?loc) (not (earthquake ?loc))]}
          {:prob 0.1
           :head  (alarm ?loc)
           :tail  [(not (burglary ?loc)) (earthquake ?loc)]}]
  :facts [{:prob 0.7 :form (burglary ?loc)}
          {:prob 0.2 :form (earthquake ?loc)}])

(defkb road-is-slow-even-kb
  "The ProbLog blocked road KB. Everything is equal, thus heavy-snow is just as likely as accident."
  :rules  [{:prob 0.5
            :head (road-is-slow ?loc)
            :tail [(heavy-snow ?loc) (bad-road-for-snow ?loc)]}
           {:prob 0.5
            :head (road-is-slow ?loc)
            :tail [(accident ?loc) (clearing-wreck ?crew ?loc)]}]
  :facts [{:prob 0.2 :form (heavy-snow mt-pass)}
          {:prob 0.2 :form (bad-road-for-snow ?x)}
          {:prob 0.2 :form (accident ?x)}
          {:prob 0.2 :form (clearing-wreck ?x ?y)}])

(defkb road-is-slow-kb
  "The blocked road KB. From a ProbLog example, I think."
  :rules  [{:prob 0.8 ; Thus it is the more reliable rule.
            :head (road-is-slow ?loc)
            :tail [(heavy-snow ?loc) (bad-road-for-snow ?loc)]}
           {:prob 0.5
            :head (road-is-slow ?loc)
            :tail [(accident ?loc) (clearing-wreck ?crew ?loc)]}]
  :facts [{:prob 0.2 :form (heavy-snow mt-pass)}
          {:prob 0.2 :form (bad-road-for-snow ?x)}
          {:prob 0.2 :form (accident ?x)}
          {:prob 0.2 :form (clearing-wreck ?x ?y)}])

(defkb road-is-slow-assumption-kb
  "blocked road with (clearing-wreck $crew-r2-skolem-1 mt-pass) (default assumption prob is 0.10) thus heavy-snow should be favored."
  :rules  [{:prob 0.5
            :head (road-is-slow ?loc)
            :tail [(heavy-snow ?loc) (bad-road-for-snow ?loc)]}
           {:prob 0.5
            :head (road-is-slow ?loc)
            :tail [(accident ?loc) (clearing-wreck ?crew ?loc)]}]
  :facts [{:prob 0.2 :form (heavy-snow mt-pass)}
          {:prob 0.2 :form (bad-road-for-snow ?x)}
          {:prob 0.2 :form (accident ?x)}]) ; Dropped clearing-wreck.

(defkb job-kb ; ToDo: Write a test that uses this KB.
  "This KB is from a problem described in my thesis: find columns that together describe a job."
  :rules [{:prob 0.70 :head (concatKey ?tab ?x ?y)      :tail [(jobID ?tab ?x ?y)]}
          {:prob 0.70 :head (jobID ?tab ?x ?y)          :tail [(date ?tab ?x) (productDesc ?tab ?y)]}
          {:prob 0.05 :head (productDesc ?tab ?x)       :tail [(date ?tab ?x)]}
          {:prob 0.40 :head (groupby ?tab ?col1  ?col2) :tail [(concatKey  ?tab ?col1 ?col2)]}
          {:prob 0.40 :head (groupby ?tab ?col1  ?col2) :tail [(concatKey  ?tab ?col2 ?col1)]}]
  :facts [{:prob 0.01 :form (jobID ?tab ?x ?x)}]
  :observations [(date Table-1 COLA)
                 (productDesc Table-1 COLB)])

(defkb job-kb-facts-kb ; ToDo: Write a test that uses this KB.
  "Like job-kb but with more facts."
  :rules [{:prob 0.70 :head (concatKey ?tab ?x ?y)      :tail [(jobID ?tab ?x ?y)]}
          {:prob 0.70 :head (jobID ?tab ?x ?y)          :tail [(date ?tab ?x) (productDesc ?tab ?y)]}
          {:prob 0.05 :head (productDesc ?tab ?x)       :tail [(date ?tab ?x)]}
          {:prob 0.40 :head (groupby ?tab ?col1  ?col2) :tail [(concatKey  ?tab ?col1 ?col2)]}
          {:prob 0.40 :head (groupby ?tab ?col1  ?col2) :tail [(concatKey  ?tab ?col2 ?col1)]}]
  :facts [{:prob 0.01 :form (jobID ?tab ?x ?x)}
          {:prob 0.90 :form (date Table-1 COLA)}
          {:prob 0.90 :form (productDesc Table-1 COLB)}])

;;; Following ProbLog semantics, the lack of a rule means the corresponding entry in the CPT is 0.
;;; This is probably a ProbLog problem, but I can't find it. tuber=tuberculosis.
#_(defkb shortness-kb ; 'dyspnea' ; ToDo: Write a test that uses this KB.
  "This KB is probably a ProbLog example."
  :rules [{:prob 0.01 :head (tuber  ?x) :tail [(visit  ?x)]}
          {:prob 0.31 :head (abnorm ?x) :tail [(tuber  ?x) (not (lung ?x))]}
          {:prob 0.32 :head (abnorm ?x) :tail [(not (tuber  ?x)) (lung ?x)]}
          {:prob 0.33 :head (abnorm ?x) :tail [(tuber  ?x) (lung ?x)]}
          {:prob 0.90 :head (xray   ?x) :tail [(abnorm ?x)]}
          {:prob 0.10 :head (xray   ?x) :tail [(not (abnorm ?x))]}])

;;; (1) Here rule prob 40/70 (favoring more complex one) infers (decisionVar TeamsOnLine) correctly. But (decisionVar TeamsOnLine) is an easy observation.
;;; (2) Add (decisionVar TeamsOnLine) and it correctly infers that NOT (decisionVar ActualEffort).
;;; (3) Change rule prob to 60/60 and it still gets it right!
;;; (explain '(objectiveFnVal ActualEffort) et/r1)
(defkb concepts1-kb ; ToDo: Write a test that uses this KB.
  "This is a KB for 'inferring concepts' from my thesis."
  :rules [{:prob 0.60 :head (objectiveFnVal ?x) :tail [(designVar ?x)                               (contributesToObj ?x)]}
          {:prob 0.60 :head (objectiveFnVal ?y) :tail [(optLocalVar ?y) (designVar ?x) (func ?x ?y) (contributesToObj ?y)]}]
  :facts [{:prob 0.10 :form (func ?x ?x)}]
  :observations [(optLocalVar ActualEffort)
                 (designVar TeamsOnLine)
                 (func TeamsOnLine ActualEffort)
                 (contributesToObj ActualEffort)])

;;; (def eee (explain '(allDifferent doesJob) et/r2))
;;; It concludes that:
;;;  (1) doesJobs is injective from Workers to Jobs.
;;;  (2) The Workers set MUST NOT BE bigger than the Jobs set.
;;;  (3) The Jobs set CAN BE bigger than the Workers set.
(defkb concepts2-kb ; More stuff for assignment problem: is it legitimately using allDifferent? ; ToDo: Write a test that uses this KB.
    "This is a KB for 'inferring concepts' from my thesis. More observations than concepts1-kb"
  :rules [{:prob 0.90 :head (allDifferent ?f)       :tail [(func1 ?f ?x ?y) (injective ?f)]}
          {:prob 0.90 :head (func1 ?f ?x ?y)        :tail [(decisionVar ?f) (varDomain ?f ?x) (varCodomain ?f ?y)]}
          {:prob 0.01 :head (injective ?f)          :tail [(func1 ?f ?x ?y) (indexSet ?x) (indexSet ?y) (biggerSet ?x ?y)]}
          {:prob 0.60 :head (objectiveFnVal ?x)     :tail [(decisionVar ?x)                               (contributesToObj ?x)]}
          {:prob 0.60 :head (objectiveFnVal ?y)     :tail [(optLocalVar ?y) (decisionVar ?x) (func ?x ?y) (contributesToObj ?y)]}
          ;; ToDo: Make the next a hard clauses. Note that you can't move not to the tail. This is a very special example.
          {:prob 0.99 :head (not (biggerSet ?x ?y)) :tail [(biggerSet ?y ?x)]}]
  :observations [(optLocalVar ActualEffort)
                 (costConcept CostTable)
                 (resourceConcept Workers)
                 (indexSet Workers)
                 (indexSet Jobs)
                 (setCardinality Workers num_workers)
                 (setCardinality Jobs    num_jobs)
                 (decisionVar   doesJob)            ; Because it is declared as such.
                 (varDomain   doesJob Workers)
                 (varCodomain doesJob Jobs)
                 (objectiveVar CostTable)           ; Because it is summed in the minimize statement
                 (objectiveFnVal CostTable)
                 (objectiveFnVal ActualEffort)
                 (func TeamsOnLine ActualEffort)
                 (contributesToObj ActualEffort)])

;;; ToDo: Investigate this:  WARN [explainlib.core:203] - Rule :rule-2 has rule-rhs before rule data.
;;;       This is reported if I switch the order of the predicates in the second rule to
;;;       [(wear ?robot ?joint) (backlash-sim ?robot ?joint)].
;;;       It doesn't change the results in this case, so I wonder whether it is legit test.
;;;       If it is, why not just reorder them automatically?
(defkb mfglet-kb
  "This is the KB used in the 2023 Manufacturing Letters paper with Deo."
  :rules [{:prob 0.4
           :head (wear ?robot ?joint)
           :tail [(stressed ?robot ?joint)]}
          {:prob 0.8
           :head (inaccurate-tcp ?robot)
           :tail [(backlash-sim ?robot ?joint) (wear ?robot ?joint)]}
          {:prob 0.7
           :head (inaccurate-tcp ?robot)
           :tail [(failing-sensor ?robot ?joint)
                  (bad-sensor-processing ?robot)]}]
  ;; Distilled from controller info, process knowledge, and a simulation:
  :facts [{:prob 0.9 :form (stressed robot-8 joint-2)}
          {:prob 0.8 :form (backlash-sim robot-8 joint-2)}
          {:prob 0.1 :form (failing-sensor robot-8 joint-2)}
          {:prob 0.7 :form (bad-sensor-processing robot-8)}])

;;;------ Tests for the above KBs ----------------------------
;;;  For more information about these, use, for example, (-> '(inaccurate-tcp robot-8) (explain mfglet-kb) ex/report-results)
(deftest good-simple-cases
  (testing "That MPE is getting good results."
    (testing "Testing an example from the Park paper. Unfortunately, I don't compute probabilities (ToDo: Model counting?)"
      (is (= '[{:props [(:fact/not cee foo)], :prob 0.06999999999999999, :proof-id :proof-2}
               {:props [(cee foo)],            :prob 0.06,               :proof-id :proof-1}]
             (-> '(dee foo) (explain park-kb) probability-by-proof))))

    (testing "Tesing the alarm-kb, which has :fact/not in some rules."
      (is (= '[{:props [(burglary plaza) (:fact/not earthquake plaza)], :prob 0.44799999999999995,  :proof-id :proof-2}
               {:props [(burglary plaza) (earthquake plaza)],           :prob 0.126,                :proof-id :proof-1}
               {:props [(:fact/not burglary plaza) (earthquake plaza)], :prob 0.006000000000000002, :proof-id :proof-3}]
             (-> '(alarm plaza) (explain alarm-kb) probability-by-proof))))

    (testing "Testing road-is-slow where probabilities are identical."
      (is (= '[{:props [(heavy-snow mt-pass) (bad-road-for-snow mt-pass)], :prob 0.02040000000000001, :proof-id :proof-1}
               {:props [(accident mt-pass) (clearing-wreck ?x mt-pass)],   :prob 0.02040000000000001, :proof-id :proof-2}]
             (-> '(road-is-slow mt-pass) (explain road-is-slow-even-kb) probability-by-proof))))

    (testing "Testing road-is-slow... with reasonable probabilities."
      (is (= '[{:props [(heavy-snow mt-pass) (bad-road-for-snow mt-pass)], :prob 0.032640000000000016, :proof-id :proof-1}
               {:props [(accident mt-pass) (clearing-wreck ?x mt-pass)],   :prob 0.02112000000000001, :proof-id :proof-2}]
             (-> '(road-is-slow mt-pass) (explain road-is-slow-kb) probability-by-proof))))

    (testing "Testing road-is-slow... with a (low-probability) assumption. This should give a warning."
      (is (= '[{:props [(heavy-snow mt-pass) (bad-road-for-snow mt-pass)],              :prob 0.0202, :proof-id :proof-1}
               {:props [(accident mt-pass) (clearing-wreck $crew-r2-skolem-1 mt-pass)], :prob 0.010200000000000004, :proof-id :proof-2}]
             (-> '(road-is-slow mt-pass) (explain road-is-slow-assumption-kb) probability-by-proof))))

    (testing "Testing a slightly bigger problem (still tiny), from the Manufacturing Letters paper."
      (is (= '[{:props [(backlash-sim robot-8 joint-2) (wear robot-8 joint-2) (stressed robot-8 joint-2)], :prob 0.24814080000000008, :proof-id :proof-1}
               {:props [(failing-sensor robot-8 joint-2) (bad-sensor-processing robot-8)],                 :prob 0.07287279999999997, :proof-id :proof-2}]
             (-> '(inaccurate-tcp robot-8) (explain mfglet-kb) probability-by-proof))))))


;;; Here's a good way to get a rather different kind of result:
(def alarm-all-kb (assoc-in alarm-kb [:params :all-individuals?] true))
; Because this one has complete RHS for the query.
(def park-all-kb (-> park-kb
                     (assoc-in [:params :all-individuals?] true)
                     (assoc-in [:params :normalize-probabilties?] false)))

;;; This one is sort of self-fulfilling prophesies, given that probabilties are normalized when :all-individuals?=true.
;;; So far, only park-all-kb doesn't need normalization, and that is because it provides all possible RHSs for the query.
(deftest all-individuals
  (testing "Testing that when :all-individuals?=true, the probability of the population sums to 1.0."
    (testing "Testing alarm-kb for :all-individuals?=true sum."
      (is (<= 0.99999 (->> (explain '(alarm plaza) alarm-all-kb) :mpe (map :prob) (apply +)) 1.00001)))

    ;; ToDo: Currently no way to not normalize.
    (testing "Testing that probability of the individuals sums to 1.0"
      (is (== 1.0 (->> (explain '(dee foo) park-all-kb) :mpe (map :prob) (apply +)))))

    ;; Because this one has complete LHSs for the query:
    (testing "Park example probabilities are same in query case and all-individuals case"
      (let [norm-mpe (->> (explain '(dee foo) park-kb) :mpe)
            all-mpe  (->> (explain '(dee foo) park-all-kb) :mpe)]
        (is (and (= (->> all-mpe   (some #(when (= (:model %) [1 2])))       :prob)
                    (->> norm-mpe  (some #(when (= (:model %) [1 2 3 -4])))  :prob))
                 (= (->> all-mpe   (some #(when (= (:model %) [-1 2])))      :prob)
                    (->> norm-mpe  (some #(when (= (:model %) [-1 2 -3 4]))) :prob))))))))

(deftest proof-steps
  (testing "Testing steps of proofs."
    (let [kb (-> '(alarm plaza) (explain alarm-kb))] ; This "does too much" but it can be redone for the test
      (testing "Testing prove-fact"
        (is (=  '{:prv (burglary plaza),
                  :caller {:bindings {}},
                  :proofs
                  [{:prob 0.7, :form (burglary ?loc), :id :fact-1, :prvn (burglary plaza), :bindings {?loc plaza}, :fact-used? true, :fact-id :fact-1}]}
                (core/prove-fact kb {:prv '(burglary plaza) :caller {:bindings {}}}))))
      (testing "Testing fact-solve"
        (is (= '({:prob 0.7, :form (burglary ?loc), :id :fact-1, :prvn (burglary plaza), :bindings {?loc plaza}})
               (core/fact-solve? kb '(burglary plaza))))))))

(deftest flattening-proofs
  (testing "Testing that proofs are flattened correctly."
    (testing "Testing a simple flattening."
      (let [raw-proof '{:rule-used? true,
                        :rule-used :rule-1,
                        :proving (road-is-slow mt-pass),
                        :rhs-queries {:rhs ((heavy-snow mt-pass) (bad-road-for-snow mt-pass)), :bindings {?loc-r1 mt-pass, ?x mt-pass}},
                        :decomp
                        [{:prv (heavy-snow mt-pass),
                          :caller {:rule-id :rule-1, :sol (heavy-snow mt-pass), :bindings {?loc-r1 mt-pass}},
                          :proofs [{:id :fact-4, :form (heavy-snow mt-pass), :prvn (heavy-snow mt-pass), :fact-used? true, :fact-id :fact-4}]}
                         {:prv (bad-road-for-snow mt-pass),
                          :caller {:rule-id :rule-1, :sol (bad-road-for-snow mt-pass), :bindings {?loc-r1 mt-pass}},
                          :proofs
                          [{:id :fact-2,
                            :form (bad-road-for-snow ?x),
                            :prvn (bad-road-for-snow mt-pass),
                            :bindings {?x mt-pass},
                            :fact-used? true,
                            :fact-id :fact-2}]}]}]
        (is (= '[[{:form (road-is-slow mt-pass), :rule? true, :rule-id :rule-1}
                  {:form (heavy-snow mt-pass), :fact? true, :fact-id :fact-4, :rule-id :rule-1}
                  {:form (bad-road-for-snow mt-pass), :fact? true, :fact-id :fact-2, :rule-id :rule-1}]]
               (core/flatten-proof raw-proof)))))))

;;; I think this will need updating when skolems are inserted correctly.
(deftest proof-generation
  (testing "Testing that abductive logic proofs on a simple example look okay."
    (is (= '{:prv (road-is-slow mt-pass),
             :top? true,
             :caller {:bindings {}},
             :proofs
             [{:rule-used? true,
               :rule-used :rule-1,
               :proving (road-is-slow mt-pass),
               :rhs-queries {:rhs ((heavy-snow mt-pass) (bad-road-for-snow mt-pass)), :bindings {?loc-r1 mt-pass, ?x mt-pass}},
               :decomp
               [{:prv (heavy-snow mt-pass),
                 :caller {:rule-id :rule-1, :sol (heavy-snow mt-pass), :bindings {?loc-r1 mt-pass}},
                 :proofs [{:prob 0.2, :form (heavy-snow mt-pass), :id :fact-4, :prvn (heavy-snow mt-pass), :fact-used? true, :fact-id :fact-4}]}
                {:prv (bad-road-for-snow mt-pass),
                 :caller {:rule-id :rule-1, :sol (bad-road-for-snow mt-pass), :bindings {?loc-r1 mt-pass}},
                 :proofs
                 [{:prob 0.2,
                   :form (bad-road-for-snow ?x),
                   :id :fact-2,
                   :prvn (bad-road-for-snow mt-pass),
                   :bindings {?x mt-pass},
                   :fact-used? true,
                   :fact-id :fact-2}]}]}
              {:rule-used? true,
               :rule-used :rule-2,
               :proving (road-is-slow mt-pass),
               :rhs-queries
               {:rhs ((accident mt-pass) (clearing-wreck ?crew-r2 mt-pass)), :bindings {?loc-r2 mt-pass, ?x mt-pass, ?crew-r2 ?x, ?y mt-pass}},
               :decomp
               [{:prv (accident mt-pass),
                 :caller {:rule-id :rule-2, :sol (accident mt-pass), :bindings {?loc-r2 mt-pass}},
                 :proofs
                 [{:prob 0.2, :form (accident ?x), :id :fact-1, :prvn (accident mt-pass), :bindings {?x mt-pass}, :fact-used? true, :fact-id :fact-1}]}
                {:prv (clearing-wreck ?crew-r2 mt-pass),
                 :caller {:rule-id :rule-2, :sol (clearing-wreck ?crew-r2 mt-pass), :bindings {?loc-r2 mt-pass, ?x mt-pass}},
                 :proofs
                 [{:prob 0.2,
                   :form (clearing-wreck ?x ?y),
                   :id :fact-3,
                   :prvn (clearing-wreck ?x mt-pass),
                   :bindings {?crew-r2 ?x, ?y mt-pass},
                   :fact-used? true,
                   :fact-id :fact-3}]}]}]}
           (-> (explain '(road-is-slow mt-pass) road-is-slow-kb) :raw-proofs)))))

;;; Namespaces meanings:
;;;    py - an identifier (variable or function) in a python jupyter notebook.
;;;    ta - type analysis.
(def pre-example
  '({:steps [{:prv (ta/conceptType ta/DemandType demand),
              :proofs ({:steps
                        [{:prv (ta/conceptVar ta/DemandType demand),
                          :proofs ({:steps
                                    [{:prv (ta/isType ta/DemandType)}
                                     {:prv (ta/simMatchVar demand ta/DemandType)}]})}]}
                       {:steps [{:prv (py/traceVar demand $y-r4-skolem-1)}
                                {:prv (ta/simMatchVar $y-r4-skolem-1 ta/DemandType)}]})}]}
    {:steps [{:prv (ta/conceptType ta/WorkerType demand),
              :proofs ({:steps [{:prv (ta/conceptVar ta/WorkerType demand),
                                 :proofs ({:steps [{:prv (ta/isType ta/WorkerType)}
                                                   {:prv (ta/simMatchVar demand ta/WorkerType)}]})}]}
                       {:steps [{:prv (py/traceVar demand $y-r4-skolem-1)}
                                {:prv (ta/simMatchVar $y-r4-skolem-1 ta/WorkerType)}]})}]}))

(def post-example
  '({:proven [(ta/conceptType ta/DemandType demand)],
     :proofs ({:proven [(ta/conceptVar ta/DemandType demand)]
               :proofs ({:proven [(ta/isType ta/DemandType) (ta/simMatchVar demand ta/DemandType)]})}
              {:proven [(py/traceVar demand $y-r4-skolem-1) (ta/simMatchVar $y-r4-skolem-1 ta/DemandType)]})}
    {:proven [(ta/conceptType ta/WorkerType demand)],
     :proofs ({:proven [(ta/conceptVar ta/WorkerType demand)]
               :proofs ({:proven [(ta/isType ta/WorkerType) (ta/simMatchVar demand ta/WorkerType)]})}
              {:proven [(py/traceVar demand $y-r4-skolem-1) (ta/simMatchVar $y-r4-skolem-1 ta/WorkerType)]})}))

(def post-example-new-wip
  '({:proven [(ta/conceptType ta/DemandType demand)],
     :proofs ({:proven [(ta/conceptVar ta/DemandType demand)],
               :proofs ({:proven  [(ta/isType ta/DemandType) (ta/simMatchVar demand ta/DemandType)]})}
              {:proven [(py/traceVar demand demand) (ta/simMatchVar demand ta/DemandType)]})}
    {:proven [(ta/conceptType ta/WorkerType demand)],
     :proofs ({:proven [(ta/conceptVar ta/WorkerType demand)],
               :proofs ({:proven [(ta/isType ta/WorkerType) (ta/simMatchVar demand ta/WorkerType)]})}
              {:proven [(py/traceVar demand start_time) (ta/simMatchVar start_time ta/WorkerType)]})}))

(def current-bogus
     '{:rule? true,
       :rhss [{:rhs? true
               :proven (py/traceVar demand demand),                                        ; This uses a binding between parts of the RHS.
               :proofs ({:proven (py/traceVar demand $y-r4-skolem-1), :assumption? true})} ; This is an assumption unaware of thing binding
              {:rhs? true                                                                  ; Q: Why did it put the skolem on ?y rather than ?x
               :proven (ta/simMatchVar demand ta/DemandType),                              ; A: The ?x binding came in from the head of the rule.
               :proofs ({:proven (ta/simMatchVar demand ta/DemandType), :fact? true})}]})

;;; Here is the kb I'm using in the above.
(defkb type-kb ; ToDo: Write a test that uses this KB.
  "This is a KB for concept inference, such as used in my thesis."
  :rules [{:prob 0.95 :head (ta/conceptQuery ?x) :tail [(ta/conceptType ta/DemandType          ?x)]}
          {:prob 0.95 :head (ta/conceptQuery ?x) :tail [(ta/conceptType ta/WorkerType          ?x)]}
          {:prob 0.60 :head (ta/conceptType  ?type ?x)        :tail [(ta/conceptVar   ?type ?x)]}
          {:prob 0.60 :head (ta/conceptType  ?type ?x)        :tail [(ta/simMatchVar ?y ?type) ; ToDo: I swapped order. See tests and notes 2020-07-26
                                                                     (py/traceVar ?x ?y)]}     ; This might just end up with e.g. (py/traceVar demand demand)
          {:prob 0.80 :head (ta/conceptVar   ?type  ?x)      :tail [(ta/isType ?type) (ta/simMatchVar ?x ?type)]}
          ;; not-inv? not useful? It is hard to describe. No penalty for not meeting it???
          ]
  :facts [{:prob 0.001 :form (py/traceVar ?x ?x)}] ;
  :observations [(ta/isType ta/DemandType)
                 (ta/isType ta/WorkerType)])


;;; 2023-11-29: Only getting 5; should be getting 11.
;;; Missing is, for example:
;;;  ((p-1 x-1) (p-2 y-1) (p-3 x-1 ?z-r1) (p-4 y-1 z-1))      <--- HUH! NO. ?z binds to z-1.
;;;  ((p-1 x-1) (p-2 y-1) (p-3 x-1 ?z-r1) (p-4 y-1 z-2))      <--- HUH! NO. ?z binds to z-2.
;;;  ((p-1 x-1) (p-2 y-1) (p-3 x-1 ?z-r1) (p-4 y-1 z-bogo))   <--- HUH! NO. ?z binds to z-bogo
;;;  ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-1) (p-4 y-1 ?z-r1))      <--- HUH! NO. ?z binds to z-1    (already above)
;;;  ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-2) (p-4 y-1 ?z-r1))      <--- HUH! NO. ?z binds to z-1    (already above)
;;;  ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-bogo) (p-4 y-1 ?z-r1))}  <--- HUH! NO. ?z binds to z-1    (already above)

;;; ================================== Testing parts of proof-generation process =======================
(defkb proof-gen-kb
  "This is a KB for testing the rule-product-transducer."
  :rules [{:prob 0.90 :head (p-lhs ?x ?y)  :tail [(p-1 ?x) (p-2 ?y) (p-3 ?x ?z) (p-4 ?y ?z)]}
          {:prob 0.90 :head (p-lhs ?x ?y)  :tail [(p-other ?x ?y)]} ; This generates an assumption.
          {:prob 0.01 :head (p-foo ?x)     :tail [(p-1 ?x)]}]
  :facts  [{:prob 0.01 :form (p-1 x-3)}
           {:prob 0.01 :form (p-3 x-1 ?x)}
           {:prob 0.01 :form (p-5 ?x ?x)}]
  :observations [(p-1 x-1)
                 (p-1 x-2)
                 (p-1 x-bogo)

                 (p-2 y-1)
                 (p-2 y-2)
                 (p-2 y-bogo)

                 (p-3 x-1 z-1)
                 (p-3 x-1 z-2)
                 (p-3 x-bogo z-1)
                 (p-3 x-1 z-bogo)

                 (p-4 y-1 z-1)
                 (p-4 y-1 z-2)
                 (p-4 y-bogo z-1)
                 (p-4 y-1 z-bogo)])

(def data-from-datatab-p-3
  (varize (set '[(p-3 x-1 z-1)
                         (p-3 x-1 z-2)
                         (p-3 x-bogo z-1)
                         (p-3 x-1 z-bogo)
                         (p-3 x-1 ?x-f2)]))) ; From a fact; not what is wanted.

(def corrected-data-from-datatab-p-3
  (varize (set '[(p-3 x-1 z-1)
                         (p-3 x-1 z-2)
                         (p-3 x-bogo z-1)
                         (p-3 x-1 z-bogo)
                         (p-3 x-1 ?z-r1)]))) ; Better

(deftest test-consistent-naming
  (testing "That data from datatab (which can get weird naming from facts containing cvars),
            is renamed to the way it appears in rules. You have to know WHERE in the rule (ix)
            you are working because the rule can have the same predicate in the RHS several times."
    (let [query '(p-lhs x-1 y-1)
          kb (as-> (core/finalize-kb proof-gen-kb query) ?kb ; 2023 was ptest
               (assoc ?kb :datatab (core/datatab ?kb)))]
      (is (= data-from-datatab-p-3
             (set (-> kb :datatab (get 'p-3)))))
      (is (= corrected-data-from-datatab-p-3
             (set (core/consistent-cvar-naming kb :rule-1 3 (get (:datatab kb) 'p-3))))))))

(def proof-test-kb-1
  (let [query '(p-lhs x-1 y-1)]
    (as-> (core/finalize-kb proof-gen-kb query) ?kb ; 2023 was ptest
      (assoc ?kb :datatab (core/datatab ?kb)))))

;;;(deftest tailtab-test (is true))
(deftest tailtab-test
  (testing "that core/tailtest works"
    (is (= '{:rule-1
             {[1 p-1] ((p-1 x-1)),
              [2 p-2] ((p-2 y-1)),
              [3 p-3] ((p-3 x-1 ?z-r1)),
              [4 p-4] ((p-4 y-1 ?z-r1))},
             :rule-2
             {[1 p-other] ((p-other x-1 y-1))}}
           (core/tailtab proof-test-kb-1 '(p-lhs x-1 y-1))))))

;;;(deftest rule-product-test (is true))
(deftest rule-product-test
  (testing "that core/rule-product works"
    (let [prv '(p-lhs x-1 y-1)
          tailtab (core/tailtab proof-test-kb-1 prv)]
      (is (= (set '(((p-1 x-1) (p-2 y-1) (p-3 x-1 z-bogo) (p-4 y-1 z-bogo))
                    ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-bogo) (p-4 y-1 z-2))
                    ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-bogo) (p-4 y-1 z-1))
                    ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-2) (p-4 y-1 z-bogo))
                    ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-2) (p-4 y-1 z-2))
                    ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-2) (p-4 y-1 z-1))
                    ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-1) (p-4 y-1 z-bogo))
                    ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-1) (p-4 y-1 z-2))
                    ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-1) (p-4 y-1 z-1))
                    ((p-1 x-1) (p-2 y-1) (p-3 x-1 ?z-r1) (p-4 y-1 ?z-r1))))
             (set (core/rule-product proof-test-kb-1 :rule-1 (:rule-1 tailtab)))))
      (is (= '(((p-other x-1 y-1)))
             (core/rule-product proof-test-kb-1 :rule-2 (:rule-2 tailtab)))))))

(defn proof-one-step
  "Return a collection of tuples that consistently unify the query (:prv)."
  [kb prv]
  (let [tailtab (core/tailtab kb prv)]
    (reduce (fn [res rule-id]
              (let [tail (-> kb :rules rule-id :tail)]
                (into res (into [] (core/filter-rule-product-transducer tail)
                                (core/rule-product kb rule-id (rule-id tailtab))))))
            []
            (keys tailtab))))

;;; Most of the following are just the filtered collection from rule-product-test,
;;; but this include one, (p-other x1 y1), from rule-1.
(deftest one-step-of-proof
  (testing "the execution of the two rules that match on head for the query."
    (is (= (set '[((p-1 x-1) (p-2 y-1) (p-3 x-1 ?z-r1)  (p-4 y-1 ?z-r1))
                  ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-bogo) (p-4 y-1 z-bogo))
                  ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-2)    (p-4 y-1 z-2))
                  ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-1)    (p-4 y-1 z-1))
                  ((p-other x-1 y-1))])
           (set (proof-one-step proof-test-kb-1 '(p-lhs x-1 y-1)))))))

;;; ToDo: There might be more to think about with respect to how I do these.
;;;       For example, should I treat a skolem like a cvar?
;;; 2021-04-27 Commented out because core/get-assumption doesn't seem to exist anymore.
#_(deftest assumptions-are-memoized
  (testing "that you get the same assumption when you call for something similar twice."
    (is (= (core/get-assumption proof-test-kb-1 (varize '(foo ?x)))
           (core/get-assumption proof-test-kb-1 (varize '(foo ?x)))))))

;;;=============================================================================================================
(defkb rule-product-kb ; ToDo: Write a test that uses this KB.
  "This is another KB for testing the rule-product-transducer."
  :rules [{:prob 0.90 :head (p-lhs ?x ?y)  :tail [(p-1 ?x) (p-2 ?y) (p-3 ?x ?z) (p-4 ?y ?z)]}
          {:prob 0.90 :head (p-lhs ?x ?y)  :tail [(p-other ?x ?y)]} ; This generates an assumption.
          {:prob 0.01 :head (p-foo ?x)     :tail [(p-1 ?x)]}]
  :facts  [{:prob 0.01 :form (p-1 x-3)}
           {:prob 0.01 :form (p-3 x-1 ?x)} ;<==================== Is this getting used? Should it be?
           {:prob 0.01 :form (p-5 ?x ?x)}]
  :observations [(p-1 x-1)
                 (p-1 x-2)
                 (p-1 x-bogo)

                 (p-2 y-1)
                 (p-2 y-2)
                 (p-2 y-bogo)

                 (p-3 x-1 z-1)
                 (p-3 x-1 z-2)
                 (p-3 x-bogo z-1)
                 (p-3 x-1 z-bogo)

                 (p-4 y-1 z-1)
                 (p-4 y-1 z-2)
                 (p-4 y-bogo z-1)
                 (p-4 y-1 z-bogo)])

;;;====================== proof-prop-sets testing ==========================================
(def whole
  (varize
   '[{:rule-used? true,
      :rule-used :rule-1,
      :proving (ta/conceptQuery demand),
      :rhs-queries {:rhs ((ta/conceptType ta/DemandType demand)), :bindings {?x-r1 demand}},
      :decomp
      [{:prv (ta/conceptType ta/DemandType demand),
        :caller {:rule-id :rule-1, :sol (ta/conceptType ta/DemandType demand), :bindings {?x-r1 demand}},
        :proofs
        [{:rule-used? true,
          :rule-used :rule-2,
          :proving (ta/conceptType ta/DemandType demand),
          :rhs-queries {:rhs ((ta/conceptRefScheme ta/DemandType ?y-r2) (ta/conceptVar ta/DemandType ?y-r2) (py/link demand ?y-r2) (ta/conceptSheet ta/DemandType demand)), :bindings {?type-r2 ta/DemandType, ?x-r2 demand}},
          :caller {:rule-id :rule-1, :sol (ta/conceptType ta/DemandType demand), :bindings {?x-r1 demand}},
          :decomp
          [{:prv (ta/conceptRefScheme ta/DemandType ?y-r2), :caller {:rule-id :rule-2, :sol (ta/conceptRefScheme ta/DemandType ?y-r2), :bindings {?x-r1 demand, ?type-r2 ta/DemandType, ?x-r2 demand}}, :proofs []} ; <============
           {:prv (ta/conceptVar ta/DemandType ?y-r2), :caller {:rule-id :rule-2, :sol (ta/conceptVar ta/DemandType ?y-r2), :bindings {}}, :proofs []} ; <============
           {:prv (py/link demand ?y-r2), :caller {:rule-id :rule-2, :sol (py/link demand ?y-r2), :bindings {?x-r1 demand}}, :proofs [{:prvn (py/link demand Demand), :bindings {?y-r2 Demand}, :observation-used? true}]}
           {:prv (ta/conceptSheet ta/DemandType demand),
            :caller {:rule-id :rule-2, :sol (ta/conceptSheet ta/DemandType demand), :bindings {?x-r1 demand, ?y-r2 Demand}},
            :proofs
            [{:rule-used? true,
              :rule-used :rule-3,
              :proving (ta/conceptSheet ta/DemandType demand),
              :rhs-queries {:rhs ((py/sheetName demand) (ta/isType ta/DemandType) (ta/simMatchExcelSheet demand ta/DemandType)), :bindings {?x-r3 demand, ?type-r3 ta/DemandType}},
              :caller {:rule-id :rule-2, :sol (ta/conceptSheet ta/DemandType demand), :bindings {?x-r1 demand, ?y-r2 Demand}},
              :decomp
              [{:prv (py/sheetName demand),
                :caller {:rule-id :rule-3, :sol (py/sheetName demand), :bindings {?x-r1 demand, ?y-r2 Demand, ?x-r3 demand, ?type-r3 ta/DemandType}},
                :proofs [{:prvn (py/sheetName demand), :observation-used? true}]}
               {:prv (ta/isType ta/DemandType),
                :caller {:rule-id :rule-3, :sol (ta/isType ta/DemandType), :bindings {?x-r1 demand, ?y-r2 Demand, ?x-r3 demand, ?type-r3 ta/DemandType}},
                :proofs [{:prvn (ta/isType ta/DemandType), :observation-used? true}]}
               {:prv (ta/simMatchExcelSheet demand ta/DemandType),
                :caller {:rule-id :rule-3, :sol (ta/simMatchExcelSheet demand ta/DemandType), :bindings {?x-r1 demand, ?y-r2 Demand, ?x-r3 demand, ?type-r3 ta/DemandType}},
                :proofs [{:prvn (ta/simMatchExcelSheet demand ta/DemandType), :fact-used? true}]}]}]}]}]}]}]))

(def small
  (varize
   '[{:rule-used? true,
      :rule-used :rule-1,
      :proving (top-level 1 2 3)
      :rhs-queries ((a ?x)),
      :decomp [{:prv (a ?x),
                :proofs [{:rule-used? true,
                          :rule-used :rule-2,
                          :proving (second-level foo)
                          :rhs-queries ((b ?y) (k ?y)),
                          :decomp [{:prv (b ?y),
                                    :proofs [{:observation-used? true :prvn (b 0)}
                                             {:rule-used? true,
                                              :rule-used :rule-3,
                                              :proving (third-level bar)
                                              :rhs-queries ((c ?m)),
                                              :decomp [{:prv (c ?m)
                                                        :proofs [{:rule-used? true,
                                                                  :rule-used :rule-4,
                                                                  :proving (fourth-level baz)
                                                                  :rhs-queries ((d ?m) (e ?m) (f ?o)),
                                                                  :decomp [{:prv (d ?m) :proofs [{:observation-used? true, :prvn (d 1)}]}
                                                                           {:prv (e ?m) :proofs [{:fact-used?        true, :prvn (e 2)}]}
                                                                           {:prv (e ?o) :proofs [{:fact-used?        true, :prvn (f 3)}]}]}]}]}]}]}]}]}]))


;;;   "This one isn't used. Don't delete it because the issue with a variable in :proving is not resolved."
(def tiny
  "This one isn't used. Don't delete it because the issue with a variable in :proving is not resolved."
  (varize
   '[{:rule-used? true,
      :rule-used :rule-5,
      :proving (top-level ?a b-1 c-1)    ; This is the only example of this sort with a var in :proving.
      :binding-sets [{?a a-1} {?a a-2}]  ; I think that makes sense because we are going to get two proofs.
      :rhs-queries ((a ?x) (b ?y) (c ?z)),
      :decomp [{:prv (a ?a), :proofs [{:observation-used? true, :prvn (a a-1)}
                                      {:observation-used? true, :prvn (a a-2)}]}
               {:prv (b ?y), :proofs [{:fact-used? true, :prvn (b b-1)}]}
               {:prv (c ?z), :proofs [{:fact-used? true, :prvn (c c-1)}]}]}]))

(def tiny-
  (varize
   '[{:rule-used? true,
      :rule-used :rule-5,
      :proving (top-level a-1 b-1 c-1)
      :binding-sets [{?a a-1} #_{?a a-2}]
      :rhs-queries ((a ?x) (b ?y) (c ?z)),
      :decomp [{:prv (a ?a), :proofs [{:observation-used? true, :prvn (a a-1)}
                                      #_{:observation-used? true, :prvn (a a-2)}]}
               {:prv (b ?y), :proofs [{:fact-used? true, :prvn (b b-1)}]}
               {:prv (c ?z), :proofs [{:fact-used? true, :prvn (c c-1)}]}]}]))

(deftest proof-prop-sets
  (testing "that proof-prop-sets are constructed correctly"
    (is (=  (-> "data/testing/proofs/whole-results.edn" slurp read-string)
            (->> (core/flatten-proofs (-> "data/testing/proofs/whole-proof.edn" slurp read-string varize)) (mapv #(mapv :step %)))))
    (is (= '[[(top-level 1 2 3) (second-level foo) (b 0)] [(top-level 1 2 3) (second-level foo) (third-level bar) (fourth-level baz) (d 1) (e 2) (f 3)]]
           (->> (core/flatten-proofs small) (mapv #(mapv :step %)))))
    (is (= '[[(top-level ?a b-1 c-1) (a a-1) (b b-1) (c c-1)] [(top-level ?a b-1 c-1) (a a-2) (b b-1) (c c-1)]]
             (->> (core/flatten-proofs tiny) (mapv #(mapv :step %)))))
    (is (= '[[(top-level a-1 b-1 c-1) (a a-1) (b b-1) (c c-1)]]
           (->> (core/flatten-proofs tiny-) (mapv #(mapv :step %)))))))

;;;-------------- Medium-sized experiments of complete MPE functionality --------
(defn interesting-loser-fn
  "Return a function that returns true when the fact argument suggests an interesting loser
   The argument is a symbol naming a variable.
   The argument expected-typs is a symbol ta/DemandType, ta/WorkerType, etc.."
  [id expected-type]
  (let [type-query (list 'ta/conceptType '?type id)]
    (fn [proof-vec]
      {:pre [(and (coll? proof-vec) (-> proof-vec first first symbol?))]}
      (when-let [type (some #(when-let [binds (uni/unify type-query %)]
                               (get binds '?type))
                            proof-vec)]
        (not= type expected-type)))))

(defn explain-concept-of-id
  "explain the given ID in the notebook."
  [id-key kb+setup]
  (let [id-sym (-> id-key name symbol)
        expect (-> kb+setup :setup :tests id-key :expect)
        loser (interesting-loser-fn id-sym expect)
        {:keys [mpe loser]}
        (explain (seq (list 'ta/conceptQuery id-sym))
                 (:kb kb+setup)
                 :loser-fn loser)]
    {:mpe mpe :loser loser}))

(defn run-experiment
  "Like an nb-agent run experiment, but doesn't need jupyter because it is reading saved data from the NB analysis"
  [kb+setup]
  (let [result
        (as-> kb+setup ?exp
          (update-in ?exp [:kb :assumptions-used] atom)
          (assoc-in ?exp [:kb :vars]
                    {:cost-fn      maxsat/rc2-cost-fn
                     :inv-cost-fn  maxsat/rc2-cost-fn-inv
                     :assumption-count (atom 0)
                     :pclause-count (atom 0)
                     :num-skolems (atom 0)})
          (assoc  ?exp :explains
                  (reduce-kv (fn [res term-tested _]
                               (assoc res term-tested (explain-concept-of-id term-tested ?exp)))
                             {}
                             (-> ?exp :setup :tests)))
          (update ?exp :setup #(dissoc % :ns-path :notebook))
          (dissoc ?exp :kb :evidence))]
    result))


(defkb _blank-kb "This KB is used to define the following default- vars.")
(def default-params (-> _blank-kb :params))
(def default-vars   (-> _blank-kb :vars))

;;; I think these are a good idea even once I've implemented elimination order.
;;; However, some such as black-listed ta/isType might not be useful because the reasoner doesn't assume
;;; in places where some value exists.
#_(defn bautista-params
  "Excepting 'requires-evidence?' these are probably hacks!" ; ToDo: If not a hack r-e? and b-l-p? then need it in defkb.
  [kb+setup]
  (assoc-in kb+setup [:kb :params]
            (merge default-params
                   {:default-assume-prob       0.400 ; <==== ahem... Also the next two!
                    :not-yet-implemented?      '#{py/traceVar} ; ToDo: This one and next aren't even part of defkb.
                    :requires-evidence?        '#{mz/indexedBy mz/indexedBy-1 mz/indexedBy-2 py/linkBack}
                    :black-listed-preds        '#{ta/isType ta/simMatchVar ta/simMatchExcelSheet ta/simMatchColName}})))

#_(deftest bautista-obvious
  (testing "medium-sized MPE calculation."
    (let [results (->> "data/testing/experiments/work-overload/b-obvious-in.edn"
                       slurp
                       read-string
                       bautista-params
                       run-experiment
                       :explains
                       :demand
                       :mpe
                       (map :proof-id)
                       set)]
      ;; Owing to the randomness of tournaments, and small game size, it is possible that not all of the returned top proofs
      ;; are identical for each run. Almost always, however, the first few are identical
      (is (>= (count (sets/intersection
                      results
                      #{:proof-46 :proof-47 :proof-89 :proof-55 :proof-133 :proof-78 :proof-68 :proof-114 :proof-92 :proof-26 :proof-69 :proof-122}))
              6)))))

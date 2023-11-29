(ns explainlib.core-test
  (:require
   [clojure.core.unify     :as uni]
   [clojure.test           :refer [deftest is testing]]
   [clojure.set             :as sets]
   [libpython-clj2.require :refer [require-python]]
   [libpython-clj2.python :as py :refer [py. py.. py.-]]
   [explainlib.core :as explain :refer [defkb explain report-results]]))

;;; ToDo: deftest these.
;;;(report-results (explain '(alarm plaza) test/alarm-kb))
;;;(report-results (explain '(blocked-road plaza) test/blocked-road-kb))
;;;(report-results (explain '(groupby Table-1 COLA COLB) test/job-kb))
;;;(report-results (explain '(objectiveFnVal CostTable) rule/r1))
;;;(report-results (explain '(objectiveFnVal ActualEffort) rule/r1))


(require-python '[pysat.examples.rc2 :as rc2])
(require-python '[pysat.formula :as wcnf])

;;;================= Test running RC2 MAXSAT =============================
(def basic-problem
  "p wcnf 9 21 2661
2661   1 2                                            0
461 -5 0
461 -8 0
92           -2                                       0
92      -1                                            0
69                 3                                  0
300               -3                                  0
120                               6                   0
36                               -6                   0
5                                                9    0
300                                             -9    0
92      -1             -4                             0
120      1                       -6                   0
36      -1                       -6                   0
92           -2        -4                             0
120           2                       -7              0
36           -2                       -7              0
36                -3                       -8         0
120               -3                   7        -9    0
36                -3                  -7        -9    0
36                          -5                  -9    0")

;;; POD Currently, I'm depending on the ordering of same-cost solutions!
(deftest basic-problem-test
  (is (= [{:model [ 1,-2, -3, -4, -5,  6, -7, -8, -9], :cost 238}
          {:model [-1, 2, -3, -4, -5, -6, -7, -8, -9], :cost 286}
          {:model [ 1,-2, -3, -4, -5, -6, -7, -8, -9], :cost 286}
          {:model [-1, 2, -3, -4, -5,  6, -7, -8, -9], :cost 322}
          {:model [-1, 2, -3, -4, -5, -6,  7, -8, -9], :cost 322}
          {:model [ 1, 2, -3, -4, -5,  6, -7, -8, -9], :cost 330}
          {:model [ 1,-2, -3,  4, -5,  6, -7, -8, -9], :cost 330}
          {:model [ 1,-2, -3, -4, -5,  6,  7, -8, -9], :cost 358}
          {:model [-1, 2, -3, -4, -5,  6,  7, -8, -9], :cost 358}
          {:model [ 1, 2, -3, -4, -5,  6,  7, -8, -9], :cost 366}]
         (explain/run-rc2-problem (wcnf/WCNF nil :from_string basic-problem) 10))))

(def tseitin-2
  "p wcnf 6 15 824
824                          5    6    0
824                         -5   -6    0
824                     4    5         0
824                3         5         0
824               -3         6         0
824                    -4    6         0
824      1                        6    0
824           2                   6    0
824     -1                        5    0
824          -2                   5    0
22       1                   0
161     -1                   0
22            2              0
161          -2              0
22                 3         0
161               -3         0
22                      4    0
161                    -4    0
69      -1   -2              0
22                -3   -4    0 ")

(deftest tseitin-2-test
  (is (= [{:model [-1, -2,  3,  4,-5, 6], :cost 388}
          {:model [ 1,  2, -3, -4, 5,-6], :cost 435}]
         (explain/run-rc2-problem (wcnf/WCNF nil :from_string tseitin-2) 10))))

(def tseitin-4
  "p wcnf 13 52 1989
1989                                                   10   11   12   13    0
1989                                                  -10  -11              0
1989                                                  -10       -12         0
1989                                                  -10            -13    0
1989                                                       -11  -12         0
1989                                                       -11       -13    0
1989                                                            -12  -13    0
1989       1                                                     12   13    0
1989            2                                      10   11              0
1989                 3                                      11   12   13    0
1989                      4                            10   11        13    0
1989                           5                       10        12   13    0
1989                                6                  10   11   12         0
1989                                     7                  11   12   13    0
1989                                          8        10   11        13    0
1989                                               9   10        12         0
1989      -1                                           10 11                  0
1989           -2                                                12 13        0
1989                -3                                 10                   0
1989                     -4                                      12         0
1989                          -5                            11              0
1989                               -6                                 13    0
1989                                    -7             10                   0
1989                                         -8                  12         0
1989                                              -9        11        13      0

461                                    7              0
1                                     -7              0
41                                          8         0
108                                        -8         0
51                           5                        0
92                          -5                        0
51                                6                   0
92                               -6                   0
51                                               9    0
92                                              -9    0
5       -1                                            0
92       1        -3                                  0
51      -1        -3                                  0
92       1                  -5                  -9    0
51      -1                  -5                  -9    0
5            -2                                       0
92            2        -4                             0
51           -2        -4                             0
92            2                  -6             -9    0
51           -2                  -6             -9    0
161                3                  -7              0
22                -3                  -7              0
161                     4                  -8         0
22                     -4                  -8         0 ")

(deftest tseitin-4-test
  (is (= [{:model [1, -2,  3, -4, -5, -6,  7, -8, -9,  10, -11, -12, -13], :cost 273}
          {:model [-1, 2, -3, -4, -5,  6, -7, -8,  9, -10, -11, -12,  13], :cost 793}
          {:model [1, -2, -3, -4,  5, -6, -7, -8,  9, -10,  11, -12, -13], :cost 793}
          {:model [-1, 2, -3,  4, -5, -6, -7,  8, -9, -10, -11,  12, -13], :cost 800}]
         (explain/run-rc2-problem (wcnf/WCNF nil :from_string tseitin-4) 10))))

;;;==================================== Test BALP-based MPE =====================================
;;; No observations. Good for ...calculating probabilities?
;;; (report-results (explain '(dee foo) et/park-kb))
(defkb park-kb
  :rules [{:prob 0.2 :head (dee ?x)   :tail [(cee ?x)]}
          {:prob 0.1 :head (dee ?x)   :tail [(not (cee ?x))]}]
  :facts [{:prob 0.3 :fact (cee ?x)}]
  :observations [])

;;; My interpretation is the ProbLog interpretation.
;;; The ProbLog reading of these is CAUSAL: If +b ^ +e, this  causes an alarm to be true with probabiility 0.9.
;;; Further, the CPT entries that aren't stated are assumed to be zero.
;;; This makes sense from the causal perspective if you assume that you've accounted for all causes.
;;; (def aaa (explain '(alarm plaza) et/alarm-kb))
(defkb alarm-kb
  :rules [{:prob 0.9
           :head  (alarm ?loc)
           :tail  [(burglary ?loc) (earthquake ?loc)]}
          {:prob 0.8
           :head  (alarm ?loc)
           :tail  [(burglary ?loc) (not (earthquake ?loc))]}
          {:prob 0.1
           :head  (alarm ?loc)
           :tail  [(not (burglary ?loc)) (earthquake ?loc)]}]
  :facts [{:prob 0.7 :fact (burglary ?loc)}
          {:prob 0.2 :fact (earthquake ?loc)}])

;;; p wcnf 2 8 603
;;; 603      1    2    0
;;;
;;; 1 : 120      1         0 c FA (burglary plaza)
;;; 2 : 36      -1         0 c FA (not (burglary plaza))
;;; 3 : 22            2    0 c FA (earthquake plaza)
;;; 4 : 161          -2    0 c FA (not (earthquake plaza))
;;; 5 : 230      1   -2    0 c RU :rule-3 {?loc-r3 plaza} | INV | REDU (alarm plaza)
;;; 6 : 22      -1    2    0 c RU :rule-2 {?loc-r2 plaza} | INV | REDU (alarm plaza)
;;; 7 : 11      -1   -2    0 c RU :rule-1 {?loc-r1 plaza} | INV | REDU (alarm plaza)
;;;
;;; Cost: 80
;;;   1 true  (burglary plaza)
;;;  -2 false (earthquake plaza)
;;;
;;; {:model [  1  -2] :cost    80 :prob 0.009}  2:[-1] 3:[2] 6:[-1 2] (+ 36 22 22)
;;; {:model [  1   2] :cost   208 :prob 0.007}  2:[-1] 4:[-2] 7:[-1 -2] (+ 36 161 11)
;;; {:model [ -1   2] :cost   511 :prob 0.002}  1:[1] 4:[-2] 5:[1 -2] (+ 120 161 230)
;;; 0.900 :rule-1  :: (alarm ?loc-r1) :- (burglary ?loc-r1) (earthquake ?loc-r1)
;;; 0.800 :rule-2  :: (alarm ?loc-r2) :- (burglary ?loc-r2) (not (earthquake ?loc-r2))
;;; 0.100 :rule-3  :: (alarm ?loc-r3) :- (not (burglary ?loc-r3)) (earthquake ?loc-r3)
;;; 0.700 :fact-1   :: (burglary ?loc-f1)
;;; 0.200 :fact-2   :: (earthquake ?loc-f2)

;;; This one hasn't really been validated. It has no hard clauses.
;;; That may be reasonable, given that all RHSs are allowed.
(defkb alarm-2-kb
  :rules [{:prob 0.9
           :head  (alarm ?loc)
           :tail  [(burglary ?loc) (earthquake ?loc)]}
          {:prob 0.8
           :head  (alarm ?loc)
           :tail  [(burglary ?loc) (not (earthquake ?loc))]}
          {:prob 0.1
           :head  (alarm ?loc)
           :tail  [(not (burglary ?loc)) (earthquake ?loc)]}
          {:prob 0.01
           :head  (alarm ?loc)
           :tail  [(not (burglary ?loc)) (not (earthquake ?loc))]}]
  :facts [{:prob 0.7 :fact (burglary ?loc)}
          {:prob 0.2 :fact (earthquake ?loc)}])

;;; (def abc (explain '(D foo) et/abcd-kb))
(defkb abcd-kb
  :rules [{:prob 0.9
           :head (D ?x)
           :tail [(A ?x) (B ?x)]}
          {:prob 0.9
           :head (D ?y)
           :tail [(A ?y) (C ?y)]}]
  :facts [{:prob 0.99 :fact (A ?a)}
          {:prob 0.98 :fact (B ?b)}
          {:prob 0.97 :fact (C ?c)}])

(defkb abcd2-kb
  :rules [{:prob 0.9
           :head (D ?x)
           :tail [(A ?x) (B ?x)]}
          {:prob 0.9
           :head (D ?y)
           :tail [(A ?y) (C ?y)]}]
  :facts [{:prob 0.99 :fact (A ?a)}
          {:prob 0.97 :fact (B ?b)}
          {:prob 0.98 :fact (C ?c)}])

(defkb one-rule-kb
  :rules [{:prob 0.9
           :head (D ?x)
           :tail [(A ?x) (B ?x)]}]
  :facts [{:prob 0.99 :fact (A ?a)}
          {:prob 0.97 :fact (B ?b)}
          {:prob 0.98 :fact (C ?c)}])

(deftest simple-fact-probabilities
  (testing "Testing that one rule works. Note antecedent C is not used. Phew!"
    (is (= [{:cost 245, :proof-id :proof-1, :pvec '((A foo) (B foo))}]
           (-> (explain '(D foo) one-rule-kb) :mpe))))
  (testing "Testing that two proofs that only differ by the probability of one antecedent are ordered correctly."
    (testing "Testing one ordering"
    (is (= [{:cost 595, :proof-id :proof-1, :pvec '((A foo) (B foo))}
            {:cost 636, :proof-id :proof-2, :pvec '((A foo) (C foo))}]
           (-> (explain '(D foo) abcd-kb) :mpe))))
    (testing "Testing same two proofs, different ordering."
      (is (= [{:cost 595, :proof-id :proof-2, :pvec '((A foo) (C foo))}
              {:cost 636, :proof-id :proof-1, :pvec '((A foo) (B foo))}]
             (-> (explain '(D foo) abcd2-kb) :mpe))))))

;;; Todo: Investigate this:  WARN [explainlib.core:203] - Rule :rule-2 has rule-rhs before rule data.
;;;       This is reported if I switch the order of the predicates in the second rule to
;;;       [(wear ?robot ?joint) (backlash-sim ?robot ?joint)].
;;;       It doesn't change the results in this case, so I wonder whether it is legit test.
;;;       If it is, why not just reorder them automatically?
;;; (explain '(inaccurate-tcp robot-8) et/mfglet-kb)
(defkb mfglet-kb
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
  :facts [{:prob 0.9 :fact (stressed robot-8 joint-2)}
          {:prob 0.8 :fact (backlash-sim robot-8 joint-2)}
          {:prob 0.1 :fact (failing-sensor robot-8 joint-2)}
          {:prob 0.7 :fact (bad-sensor-processing robot-8)}])


(deftest mfglet-example
  (testing "Testing that the example from the 2023 Manufacturing Letters paper works."
    (is (= [{:cost 439, :proof-id :proof-1, :pvec '((backlash-sim robot-8 joint-2) (wear robot-8 joint-2) (stressed robot-8 joint-2))}
            {:cost 813, :proof-id :proof-2, :pvec '((failing-sensor robot-8 joint-2) (bad-sensor-processing robot-8))}]
           (-> (explain '(inaccurate-tcp robot-8) mfglet-kb) :mpe)))))

;;; Read these as probabilities that the road will be blocked for the reasons that are antecedents.
;;; [(accident plaza) 1]
;;; [(clearing-wreck $crew-r2-skolem-1 plaza) 2]
;;; [(drive-hazard plaza) 3]
;;; [(heavy-snow plaza) 4]
;;; 3,4 should be favored (0.8 vs 0.5).
;;; (report-results (explain '(blocked-road plaza) et/blocked-road-kb))
(defkb blocked-road-kb
  :rules  [{:prob 0.8 ; ASYMMETRIC
            :head (blocked-road ?loc)
            :tail [(heavy-snow ?loc) (drive-hazard ?loc)]}
           {:prob 0.5
            :head (blocked-road ?loc)
            :tail [(accident ?loc) (clearing-wreck ?crew ?loc)]}]
  :facts [{:prob 0.2 :fact (heavy-snow plaza)}
          {:prob 0.2 :fact (drive-hazard ?x)}
          {:prob 0.2 :fact (accident ?x)}
          {:prob 0.2 :fact (clearing-wreck ?x ?y)}])

;;; assume clearing-wreck. default-assumption-probability  is 0.40 thus ASYMMETRIC
;;; I think that is enough to make the top explanation accident/clearing-wreck.
;;; (def bra (explain '(blocked-road plaza) et/bra-kb))
(defkb bra-kb
  :rules  [{:prob 0.5
            :head (blocked-road ?loc)
            :tail [(heavy-snow ?loc) (drive-hazard ?loc)]}
           {:prob 0.5
            :head (blocked-road ?loc)
            :tail [(accident ?loc) (clearing-wreck ?crew ?loc)]}]
  :facts [{:prob 0.2 :fact (heavy-snow plaza)}
          {:prob 0.2 :fact (drive-hazard ?x)}
          {:prob 0.2 :fact (accident ?x)}]
  :observations [])


(defkb bs-kb
  :rules  [{:prob 0.5
            :head (blocked-road ?loc)
            :tail [(heavy-snow ?loc) (drive-hazard ?loc)]}
           {:prob 0.5
            :head (blocked-road ?loc)
            :tail [(accident ?loc) (clearing-wreck ?crew ?loc)]}]
  :facts [{:prob 0.2 :fact (heavy-snow plaza)}
          {:prob 0.2 :fact (drive-hazard ?x)}
          {:prob 0.2 :fact (accident ?x)}
          {:prob 0.2 :fact (clearing-wreck ?x ?y)}]
  :observations [])


;;; (def jjj (explain '(groupby Table-1 COLA COLB) et/job-kb))
(defkb job-kb
  :rules [{:prob 0.70 :head (concatKey ?tab ?x ?y)      :tail [(jobID ?tab ?x ?y)]}
          {:prob 0.70 :head (jobID ?tab ?x ?y)          :tail [(date ?tab ?x) (productDesc ?tab ?y)]}
          {:prob 0.05 :head (productDesc ?tab ?x)       :tail [(date ?tab ?x)]}
          {:prob 0.40 :head (groupby ?tab ?col1  ?col2) :tail [(concatKey  ?tab ?col1 ?col2)]}
          {:prob 0.40 :head (groupby ?tab ?col1  ?col2) :tail [(concatKey  ?tab ?col2 ?col1)]}]
  :facts [{:prob 0.01 :fact (jobID ?tab ?x ?x)}]
  :observations [(date Table-1 COLA)
                 (productDesc Table-1 COLB)])

(defkb job-kb-facts
  :rules [{:prob 0.70 :head (concatKey ?tab ?x ?y)      :tail [(jobID ?tab ?x ?y)]}
          {:prob 0.70 :head (jobID ?tab ?x ?y)          :tail [(date ?tab ?x) (productDesc ?tab ?y)]}
          {:prob 0.05 :head (productDesc ?tab ?x)       :tail [(date ?tab ?x)]}
          {:prob 0.40 :head (groupby ?tab ?col1  ?col2) :tail [(concatKey  ?tab ?col1 ?col2)]}
          {:prob 0.40 :head (groupby ?tab ?col1  ?col2) :tail [(concatKey  ?tab ?col2 ?col1)]}]
  :facts [{:prob 0.01 :fact (jobID ?tab ?x ?x)}
          {:prob 0.90 :fact (date Table-1 COLA)}
          {:prob 0.90 :fact (productDesc Table-1 COLB)}])

;;; Follow the lead from alarm-kb. The result is a set of CPTs.
;;; Following ProbLog semantics, the lack of a rule means the corresponding entry
;;; in the CPT is 0. I should perhaps be using this in a little better in the job-kb?
(defkb shortness ; 'dyspnea'
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
(defkb r1
  :rules [{:prob 0.60 :head (objectiveFnVal ?x) :tail [(designVar ?x)                               (contributesToObj ?x)]}
          {:prob 0.60 :head (objectiveFnVal ?y) :tail [(optLocalVar ?y) (designVar ?x) (func ?x ?y) (contributesToObj ?y)]}]
  :facts [{:prob 0.10 :fact (func ?x ?x)}]
  :observations [(optLocalVar ActualEffort)
                 (designVar TeamsOnLine)
                 (func TeamsOnLine ActualEffort)
                 (contributesToObj ActualEffort)])

;;; (def eee (explain '(allDifferent doesJob) et/r2))
;;; It concludes that:
;;;  (1) doesJobs is injective from Workers to Jobs.
;;;  (2) The Workers set MUST NOT BE bigger than the Jobs set.
;;;  (3) The Jobs set CAN BE bigger than the Workers set.
(defkb r2 ; More stuff for assignment problem: is it legitimately using allDifferent?
  :rules [{:prob 0.90 :head (allDifferent ?f)       :tail [(func1 ?f ?x ?y) (injective ?f)]}
          {:prob 0.90 :head (func1 ?f ?x ?y)        :tail [(decisionVar ?f) (varDomain ?f ?x) (varCodomain ?f ?y)]}
          {:prob 0.01 :head (injective ?f)          :tail [(func1 ?f ?x ?y) (indexSet ?x) (indexSet ?y) (biggerSet ?x ?y)]}
          {:prob 0.60 :head (objectiveFnVal ?x)     :tail [(decisionVar ?x)                               (contributesToObj ?x)]}
          {:prob 0.60 :head (objectiveFnVal ?y)     :tail [(optLocalVar ?y) (decisionVar ?x) (func ?x ?y) (contributesToObj ?y)]}
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

;;;==================================== Tests ======================================================
;;; In ~is~ the correct one goes first in the =. (is (= correct-value generated-value))
#_(deftest test-binding-sets
  (testing "that binding sets are created correctly"
    (is (= '[{?f doesJob, ?y Jobs, ?x Workers} {?f TeamsOnLine, ?x $x-skolem, ?y $y-skolem}]
           (explain/binding-sets-aux '[{?f TeamsOnLine} {?f doesJob, ?x Workers} {?f doesJob, ?y Jobs}])))
    (is (= '[{?f doesJob, ?y Jobs, ?x Workers}]
           (explain/binding-sets-aux '[{?f doesJob} {?f doesJob, ?x Workers} {?f doesJob, ?y Jobs}])))))

;;; POD pprocess-prv not defined
#_(deftest test-postprocessed-proof-1
  (testing "that adductive logic proofs on a simple example look okay before post-processing."
    (is (= '{:prv (designVar CostTable),
             :proofs
             [{:fact
               {:cnf [{:pred (designVar CostTable), :neg? false}],
                :prob 0.9,
                :using "obs-1"},
               :subs {?x CostTable}}]}
           (explain/pprocess-prv '{:prv (designVar ?x),
                                   :proofs
                                   [{:fact
                                     {:cnf [{:pred (designVar CostTable), :neg? false}],
                                      :prob 0.9,
                                      :using "obs-1"},
                                     :subs {?x CostTable}}]})))))

(deftest test-postprocessed-proof-2 (is true))
#_(deftest test-postprocessed-proof-2
  (testing "that abductive logic proofs on a simple example look okay."
    (let [result (explain '(blocked-road plaza) blocked-road-kb)]
      (is (= '({:using-rule :rule-1,
                :rule-subs {?loc-r1 plaza},
                :prob 0.8,
                :lhs {:pred (blocked-road ?loc-r1), :neg? false},
                :rhs
                ({:pred (heavy-snow ?loc-r1), :neg? false}
                 {:pred (drive-hazard ?loc-r1), :neg? false}),
                :cnf
                [{:pred (blocked-road plaza), :neg? false}
                 {:pred (heavy-snow plaza), :neg? true}
                 {:pred (drive-hazard plaza), :neg? true}],
                :steps
                [{:prv (heavy-snow plaza),
                  :proofs
                  [{:fact
                    {:cnf [{:pred (heavy-snow plaza), :neg? false}],
                     :prob 0.2,
                     :using :fact-1}}]}
                 {:prv (drive-hazard plaza),
                  :proofs
                  [{:fact
                    {:cnf [{:pred (drive-hazard plaza), :neg? false}],
                     :prob 0.2,
                     :using :fact-2}}]}]}
               {:using-rule :rule-2,
                :rule-subs {?loc-r2 plaza, ?crew-r2 $crew-r2-skolem-1},
                :prob 0.5,
                :lhs {:pred (blocked-road ?loc-r2), :neg? false},
                :rhs
                ({:pred (accident ?loc-r2), :neg? false}
                 {:pred (clearing-wreck ?crew-r2 ?loc-r2), :neg? false}),
                :cnf
                [{:pred (blocked-road plaza), :neg? false}
                 {:pred (accident plaza), :neg? true}
                 {:pred (clearing-wreck $crew-r2-skolem-1 plaza), :neg? true}],
                :steps
                [{:prv (accident plaza),
                  :proofs
                  [{:fact
                    {:cnf [{:pred (accident plaza), :neg? false}],
                     :prob 0.2,
                     :using :fact-3}}]}
                 {:prv (clearing-wreck ?crew-r2 plaza),
                  :proofs
                  [{:fact
                    {:cnf
                     [{:pred (clearing-wreck $crew-r2-skolem-1 plaza),
                       :neg? false}],
                     :prob 0.2,
                     :using :fact-4}}]}]})
             (:all-proofs result))))))

;;; A <- B C
;;; A <- D E
;;;
;;; If downstream proof of D uses B, then NOT (B AND D) should be avoided.
;;; {:psets
;;;  [{:using :rule-5, :top-pids #{2 4}, :down-proof-pids #{7 3 9}}
;;;   {:using :rule-4, :top-pids #{1 5}, :down-proof-pids #{6 3 2}}],
;;; :or-pairs [#{2 1} #{2 5} #{4 1} #{4 5}]}.
;;;
;;; Means remove  #{2 1} and #{2 5} from :nand-pairs (that starts as a copy of :or-pairs).
#_(deftest test-max-sat
  (testing "that max-sat problems work (jupyter/app-gateway must be running)."
    (is (= (explain/python-maxsat
     "p wcnf 2 7 321
70        1           0
30       -1           0
20              2     0
80             -2     0
90        1    -2     0
20       -1     2     0
10       -1    -2     0")
           [{:model [1  -2], :cost 70,  :prob 0.4965853037914095}
            {:model [-1 -2], :cost 90,  :prob 0.4065696597405991}
            {:model [1   2], :cost 120, :prob 0.30119421191220214}
            {:model [-1  2], :cost 240, :prob 0.09071795328941251}]))))

;;; p wcnf 2 8 603
;;; 603      1    2    0
;;; 120      1         0 c FA (burglary plaza)
;;; 36      -1         0 c FA (not (burglary plaza))
;;; 22            2    0 c FA (earthquake plaza)
;;; 161          -2    0 c FA (not (earthquake plaza))
;;; 230      1   -2    0 c RU :rule-3 {?loc-r3 plaza} | INV | REDU (alarm plaza)
;;; 22      -1    2    0 c RU :rule-2 {?loc-r2 plaza} | INV | REDU (alarm plaza)
;;; 11      -1   -2    0 c RU :rule-1 {?loc-r1 plaza} | INV | REDU (alarm plaza)

(deftest good-explanations (is true))
#_(deftest good-explanations
  (testing "That MPE is getting good results. jupyter/app-gateway must be running"
    (is (= #{{:model [  1  -2] :cost    80}
             {:model [  1   2] :cost   208}
             {:model [ -1   2] :cost   511}}
           (->> (explain '(alarm plaza) alarm-kb) :mpe (map #(dissoc % :prob)) set)))
    (is (= #{{:model [-1 -2  3  4], :cost 388}
             {:model [ 1  2 -3 -4], :cost 435}}
           (->> (explain '(blocked-road plaza) blocked-road-kb) :mpe (map #(dissoc % :prob)) set)))
    (is (= #{{:model [  1   2  -3  -4] :cost   366}
             {:model [ -1  -2   3   4] :cost   464}}
           (->> (explain '(blocked-road plaza) bra-kb) :mpe (map #(dissoc % :prob)) set)))
    (is (= #{{:model [  1   2  -3  -4] :cost   435}
             {:model [ -1  -2   3   4] :cost   435}}
           (->> (explain '(blocked-road plaza) bs-kb) :mpe (map #(dissoc % :prob)) set)))
    (is (=  [{:model [ 1 -2 -3  4 -5 -6], :cost 220}
             {:model [-1  2  3 -4  5  6], :cost 676}]
           (as-> (explain '(groupby Table-1 COLA COLB) job-kb) ?r
             (:mpe ?r)
             (mapv #(dissoc % :prob) ?r))))
    ;; Without inverse facts and assumptions, this one just disappears!
    (is (= #{{:model [-1], :cost 51} {:model [1], :cost 92}}
           (->> (explain '(objectiveFnVal ActualEffort) r1) :mpe (map #(dissoc % :prob)) set)))
    ;; There is only one RHS on this one [1,2,3,4] are all PIDs
    (is (= #{{:model [ 1 -2 3 4], :cost 73}
             {:model [-1 -2 3 4], :cost 73}
             {:model [-1  2 3 4], :cost 575}
             {:model [ 1  2 3 4], :cost 1036}}
           (->> (explain '(allDifferent doesJob) r2) :mpe (map #(dissoc % :prob)) set)))))

(deftest instance-probs (is true))
#_(deftest instance-probs
  (testing "that conditional probabilities are calculcated correctly"
    (is true)))

;;;    (is (< 0.059
;;;           (* (explain/cprob p-kb '(dee $x1-skolem-1) '[(cee $x1-skolem-1)])
;;;              (explain/cprob p-kb '(cee $x1-skolem-1)))
;;;           0.061))
;;;    (is (< 0.239
;;;           (* (explain/cprob p-kb '(not (dee $x1-skolem-1)) '[(cee $x1-skolem-1)])
;;;              (explain/cprob p-kb '(cee $x1-skolem-1)))
;;;           0.251))
;;;    (is (< 0.069
;;;           (* (explain/cprob p-kb '(dee $x1-skolem-1) '[(not (cee $x1-skolem-1))])
;;;              (explain/cprob p-kb '(not (cee $x1-skolem-1))))
;;;           0.071))
;;;    (is (< 0.629
;;;           (* (explain/cprob p-kb '(not (dee $x1-skolem-1)) '[(not (cee $x1-skolem-1))])
;;;              (explain/cprob p-kb '(not (cee $x1-skolem-1))))
;;;           0.631))

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

(deftest proof-folding (is true))
#_(deftest proof-folding
  (testing "that gather-proven, etc. works"
    (is (= (explain/gather-proven pre-example) post-example))))


;;; Here is a problem: I don't think I should be creating assumptions until after all other RHS have created bindings.
;;; I currently have some code in prove-fact to collect bindings into an atom, rule-accum-subs, but that doesn't look
;;; like it is placed in the correct place. What it would make is a fact (py/traceVar demand demand) but I added
;;; a 0.001 probability fact (py/traceVar ?x ?x) which stopped it. (Comment this out to continue debugging rule-assume-subs).
;;; Since this is for :proof-vec, I think I'll be okay for the time being.
;;;
;;; (def eee (explain '(ta/conceptQuery demand) (pl/compose-kb (-> "data/testing/hints/facts-2.edn" slurp read-string))))
;;; (->> (:all-proofs eee) bind-proven strip-proof-useless)
;;; {:prob 0.60 :head (ta/conceptType  ?type ?x)        :tail [(py/traceVar ?x ?y)
;;;                                                            (ta/simMatchVar ?y ?type)]}
;;;

;;; IN FACT, rule-accum-subs definitely doesn't have the right stuff in it. It should only have bindings from one rule: (all its rlits)
;;; 20-07-26 21:26:28 PN120134 INFO [app.model.explain:286] - New assumption on (py/traceVar demand ?y-r4)
;;; subs= {?x-r2 demand, ?type-r4 ta/DemandType, ?x-r4 demand, ?type-r5 ta/DemandType, ?x-r5 demand, ?type-r3 ta/DemandType, ?x-r3 demand}
;;;       The rule would be rule-4, and it would have {?y-r4 demand} in it!
;;;  push-subs! works on each match (there are two). I think that is okay.
;;;  Maybe a second stack for inside the rule???

(def current-bogus
     '{:rule? true,
       :rhss [{:rhs? true
               :proven (py/traceVar demand demand),                                        ; This uses a binding between parts of the RHS.
               :proofs ({:proven (py/traceVar demand $y-r4-skolem-1), :assumption? true})} ; This is an assumption unaware of thing binding
              {:rhs? true                                                                  ; Q: Why did it put the skolem on ?y rather than ?x
               :proven (ta/simMatchVar demand ta/DemandType),                              ; A: The ?x binding came in from the head of the rule.
               :proofs ({:proven (ta/simMatchVar demand ta/DemandType), :fact? true})}]})

;;; Here is the kb I'm using in the above.
(defkb type-kb
  :rules [{:prob 0.95 :head (ta/conceptQuery ?x) :tail [(ta/conceptType ta/DemandType          ?x)]}
          {:prob 0.95 :head (ta/conceptQuery ?x) :tail [(ta/conceptType ta/WorkerType          ?x)]}
          {:prob 0.60 :head (ta/conceptType  ?type ?x)        :tail [(ta/conceptVar   ?type ?x)]}
          {:prob 0.60 :head (ta/conceptType  ?type ?x)        :tail [(ta/simMatchVar ?y ?type) ; POD I swapped order. See tests and notes 2020-07-26
                                                                     (py/traceVar ?x ?y)]}     ; This might just end up with e.g. (py/traceVar demand demand)
          {:prob 0.80 :head (ta/conceptVar   ?type  ?x)      :tail [(ta/isType ?type) (ta/simMatchVar ?x ?type)]}
          ;; not-inv? not useful? It is hard to describe. No penalty for not meeting it???
          ]
  :facts [{:prob 0.001 :fact (py/traceVar ?x ?x)}] ;
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
(defkb ptest
  :rules [{:prob 0.90 :head (p-lhs ?x ?y)  :tail [(p-1 ?x) (p-2 ?y) (p-3 ?x ?z) (p-4 ?y ?z)]}
          {:prob 0.90 :head (p-lhs ?x ?y)  :tail [(p-other ?x ?y)]} ; This generates an assumption.
          {:prob 0.01 :head (p-foo ?x)     :tail [(p-1 ?x)]}]
  :facts  [{:prob 0.01 :fact (p-1 x-3)}
           {:prob 0.01 :fact (p-3 x-1 ?x)}
           {:prob 0.01 :fact (p-5 ?x ?x)}]
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
  (explain/varize (set '[(p-3 x-1 z-1)
                         (p-3 x-1 z-2)
                         (p-3 x-bogo z-1)
                         (p-3 x-1 z-bogo)
                         (p-3 x-1 ?x-f2)]))) ; From a fact; not what is wanted.

(def corrected-data-from-datatab-p-3
  (explain/varize (set '[(p-3 x-1 z-1)
                         (p-3 x-1 z-2)
                         (p-3 x-bogo z-1)
                         (p-3 x-1 z-bogo)
                         (p-3 x-1 ?z-r1)]))) ; Better

(deftest test-consistent-naming
  (testing "That data from datatab (which can get weird naming from facts containing cvars),
            is renamed to the way it appears in rules. You have to know WHERE in the rule (ix)
            you are working because the rule can have the same predicate in the RHS several times."
    (let [query '(p-lhs x-1 y-1)
          kb (as-> (explain/finalize-kb ptest query) ?kb
               (assoc ?kb :datatab (explain/datatab ?kb)))]
      (is (= data-from-datatab-p-3
             (set (-> kb :datatab (get 'p-3)))))
      (is (= corrected-data-from-datatab-p-3
             (set (explain/consistent-cvar-naming kb :rule-1 3 (get (:datatab kb) 'p-3))))))))

(def proof-test-kb-1
  (let [query '(p-lhs x-1 y-1)]
    (as-> (explain/finalize-kb ptest query) ?kb
      (assoc ?kb :datatab (explain/datatab ?kb)))))

;;;(deftest tailtab-test (is true))
(deftest tailtab-test
  (testing "that explain/tailtest works"
    (is (= '{:rule-1
             {[1 p-1] ((p-1 x-1)),
              [2 p-2] ((p-2 y-1)),
              [3 p-3] ((p-3 x-1 ?z-r1)),
              [4 p-4] ((p-4 y-1 ?z-r1))},
             :rule-2
             {[1 p-other] ((p-other x-1 y-1))}}
           (explain/tailtab proof-test-kb-1 '(p-lhs x-1 y-1))))))

;;;(deftest rule-product-test (is true))
(deftest rule-product-test
  (testing "that explain/rule-product works"
    (let [prv '(p-lhs x-1 y-1)
          tailtab (explain/tailtab proof-test-kb-1 prv)]
      (is (= (set '(((p-1 x-1) (p-2 y-1) (p-3 x-1 z-bogo) (p-4 y-1 z-bogo))    ; ok
                    ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-bogo) (p-4 y-1 z-2))
                    ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-bogo) (p-4 y-1 z-1))
                    ;((p-1 x-1) (p-2 y-1) (p-3 x-1 z-bogo) (p-4 y-1 ?z-r1))     ; ok ... 2023. NOT!
                    ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-2) (p-4 y-1 z-bogo))
                    ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-2) (p-4 y-1 z-2))          ; ok
                    ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-2) (p-4 y-1 z-1))
                    ;((p-1 x-1) (p-2 y-1) (p-3 x-1 z-2) (p-4 y-1 ?z-r1))        ; ok ... 2023. NOT!
                    ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-1) (p-4 y-1 z-bogo))
                    ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-1) (p-4 y-1 z-2))
                    ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-1) (p-4 y-1 z-1))          ; ok
                    ;((p-1 x-1) (p-2 y-1) (p-3 x-1 z-1) (p-4 y-1 ?z-r1))        ; ok ... 2023. NOT!
                    ;((p-1 x-1) (p-2 y-1) (p-3 x-1 ?z-r1) (p-4 y-1 z-bogo))     ; ok ... 2023. NOT!
                    ;((p-1 x-1) (p-2 y-1) (p-3 x-1 ?z-r1) (p-4 y-1 z-2))        ; ok ... 2023. NOT!
                    ;((p-1 x-1) (p-2 y-1) (p-3 x-1 ?z-r1) (p-4 y-1 z-1))        ; ok ... 2023. NOT!
                    ((p-1 x-1) (p-2 y-1) (p-3 x-1 ?z-r1) (p-4 y-1 ?z-r1))))    ; ok
             (set (explain/rule-product proof-test-kb-1 :rule-1 (:rule-1 tailtab)))))
      (is (= '(((p-other x-1 y-1)))
             (explain/rule-product proof-test-kb-1 :rule-2 (:rule-2 tailtab)))))))

(defn proof-one-step
  "Return a collection of tuples that consistently unify the query (:prv)."
  [kb prv]
  (let [tailtab (explain/tailtab kb prv)]
    (reduce (fn [res rule-id]
              (let [tail (-> kb :rules rule-id :tail)]
                (into res (into [] (explain/filter-rule-product-transducer tail)
                                (explain/rule-product kb rule-id (rule-id tailtab))))))
            []
            (keys tailtab))))

;;; Most of the following are just the filtered collection from rule-product-test,
;;; but this include one, (p-other x1 y1), from rule-1.
(deftest one-step-of-proof
  (testing "the execution of the two rules that match on head for the query."
    (is (= (set '[;((p-1 x-1) (p-2 y-1) (p-3 x-1 ?z-r1)  (p-4 y-1 z-bogo)) ; 2023: I don't see how these could be considered correct!
                  ;((p-1 x-1) (p-2 y-1) (p-3 x-1 ?z-r1)  (p-4 y-1 z-2))    ; 2023: They are leaving a variable that is bound unbound.
                  ;((p-1 x-1) (p-2 y-1) (p-3 x-1 ?z-r1)  (p-4 y-1 z-1))
                  ((p-1 x-1) (p-2 y-1) (p-3 x-1 ?z-r1)  (p-4 y-1 ?z-r1))
                  ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-bogo) (p-4 y-1 z-bogo))
                  ;((p-1 x-1) (p-2 y-1) (p-3 x-1 z-bogo) (p-4 y-1 ?z-r1))
                  ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-2)    (p-4 y-1 z-2))
                  ;((p-1 x-1) (p-2 y-1) (p-3 x-1 z-2)    (p-4 y-1 ?z-r1))
                  ((p-1 x-1) (p-2 y-1) (p-3 x-1 z-1)    (p-4 y-1 z-1))
                  ;((p-1 x-1) (p-2 y-1) (p-3 x-1 z-1)    (p-4 y-1 ?z-r1))
                  ((p-other x-1 y-1))])
           (set (proof-one-step proof-test-kb-1 '(p-lhs x-1 y-1)))))))

;;; POD There might be more to think about with respect to how I do these.
;;;     For example, should I treat a skolem like a cvar?
;;; 2021-04-27 Commented out because explain/get-assumption doesn't seem to exist anymore.
#_(deftest assumptions-are-memoized
  (testing "that you get the same assumption when you call for something similar twice."
    (is (= (explain/get-assumption proof-test-kb-1 (explain/varize '(foo ?x)))
           (explain/get-assumption proof-test-kb-1 (explain/varize '(foo ?x)))))))


;;;=============================================================================================================
(defkb ptest
  :rules [{:prob 0.90 :head (p-lhs ?x ?y)  :tail [(p-1 ?x) (p-2 ?y) (p-3 ?x ?z) (p-4 ?y ?z)]}
          {:prob 0.90 :head (p-lhs ?x ?y)  :tail [(p-other ?x ?y)]} ; This generates an assumption.
          {:prob 0.01 :head (p-foo ?x)     :tail [(p-1 ?x)]}]
  :facts  [{:prob 0.01 :fact (p-1 x-3)}
           {:prob 0.01 :fact (p-3 x-1 ?x)} ;<==================== Is this getting used? Should it be?
           {:prob 0.01 :fact (p-5 ?x ?x)}]
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
  (explain/varize
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
  (explain/varize
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
  (explain/varize
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
  (explain/varize
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
            (->> (explain/walk-rules (-> "data/testing/proofs/whole-proof.edn" slurp read-string explain/varize)) (mapv #(mapv :step %)))))
    (is (= '[[(top-level 1 2 3) (second-level foo) (b 0)] [(top-level 1 2 3) (second-level foo) (third-level bar) (fourth-level baz) (d 1) (e 2) (f 3)]]
           (->> (explain/walk-rules small) (mapv #(mapv :step %)))))
    (is (= '[[(top-level ?a b-1 c-1) (a a-1) (b b-1) (c c-1)] [(top-level ?a b-1 c-1) (a a-2) (b b-1) (c c-1)]]
             (->> (explain/walk-rules tiny) (mapv #(mapv :step %)))))
    (is (= '[[(top-level a-1 b-1 c-1) (a a-1) (b b-1) (c c-1)]]
           (->> (explain/walk-rules tiny-) (mapv #(mapv :step %)))))))

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
  "explain/explain the given ID in the notebook."
  [id-key kb+setup]
  (let [id-sym (-> id-key name symbol)
        expect (-> kb+setup :setup :tests id-key :expect)
        loser (interesting-loser-fn id-sym expect)
        {:keys [mpe loser]}
        (explain/explain (seq (list 'ta/conceptQuery id-sym))
                         (:kb kb+setup)
                         :loser-fn loser)]
    {:mpe mpe :loser loser}))

(defn run-experiment
  "Like run experiment, but doesn't need jupyter because it is reading saved data from the NB analysis"
  [epath]
  (let [result
        (as-> (-> epath slurp  read-string) ?exp
          (update-in ?exp [:kb :assumptions-used] atom)
          (assoc-in ?exp [:kb :vars]
                    {:cost-fn      explainlib.core/neg-log-cost
                     :inv-cost-fn  explainlib.core/neg-log-cost-1
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

(deftest bautista-obvious
  (testing "medium-sized MPE calculation."
    (let [results (->> "data/testing/experiments/work-overload/b-obvious-in.edn"
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

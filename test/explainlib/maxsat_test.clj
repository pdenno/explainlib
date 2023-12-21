(ns explainlib.maxsat-test
  "Tests, demonstration and explanation for aspects of the explainlib algorithms."
  (:require
   [clojure.test                :refer [deftest is testing]]
   [explainlib.maxsat           :as maxsat]
   [libpython-clj2.require      :refer [require-python]]))

(require-python '[pysat.examples.rc2 :as rc2])
(require-python '[pysat.formula :as wcnf])

;;;================================ Test running the RC2 MAXSAT Python algorithm =============================
;;; WDIMACS format http://www.maxhs.org/docs/wdimacs.html N.B. Comments can only be on a line by themselves: #"^c (.*)"
;;; I use them differently, but the solver never sees my comments. Note that WDIMACS is used by CPLEX; probably quite old.

;;; WCNF = Weighted Conjunctive Normal Form, https://hardlog.udl.cat/static/doc/optilog/html/optilog/formula/WCNF.html
;;; CNF = Each line is a disjunction, the collection of lines is the conjunction.
;;; Horn Clause =  A disjunctive clause in which at most one literal (the head) is positive (not negated).
;;;    Intutitively, the motivation behind reasoning with Horn clauses is that the only truth table entry that is false is one in which
;;;    all the body literals are true and the head literal is false.
;;;    This can be interpreted as requiring necessarily that if the body literals are true, the head literal is also.
;;; pclause = A clause with associated probability computed for translation to a line in the WCNF.
;;;    N.B pclauses and the lines of the WCNF need not be Horn clauses.
;;;
;;; The WCNF cost is incurred if the individual has all literals opposite of the WCNF line.

(def simple-maxsat-1
"p wcnf 2 6 581

120     -1         0
36       1         0
22      -1    2    0
161     -1   -2    0
11       1    2    0
230      1   -2    0")


;;; 1 : 70        1           0
;;; 2 : 30       -1           0
;;; 3 : 20              2     0
;;; 4 : 80             -2     0
;;; 5 : 90        1    -2     0
;;; 6 : 20       -1     2     0
;;; 7 : 10       -1    -2     0

;;; [{:model [1,  -2], :cost 70}    ; L2 + L3 + L6      = 30 + 20 + 20      = 70
;;;  {:model [-1, -2], :cost 90}    ; L1 + L3           = 70 + 20           = 90
;;;  {:model [1,   2], :cost 120}   ; L2 + L4 + L7      = 30 + 80 + 10      = 120
;;;  {:model [-1,  2], :cost 240}]  ; L1 + L4 + L5      = 70 + 80 + 90      = 240

(def another-maxsat
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

(deftest maxsat-tests
  (testing "Testing that max-sat problems work."   ; The individual incurs the cost if they disagree on ALL literals of the WCNF line. (See numbered lines above.)
    (testing "Testing a model like Park :all-individuals?=true"
      (is (= [{:model [-1, -2], :cost 47}
              {:model [ 1, -2], :cost 142}
              {:model [-1,  2], :cost 266}
              {:model [ 1,  2], :cost 281}]
             (maxsat/run-rc2-problem (wcnf/WCNF nil :from_string simple-maxsat-1) 10))))
    (testing "Testing another simple maxsat."
      (is (= [{:model [ 1, -2, -3, -4, -5,  6, -7, -8, -9], :cost 238}
              {:model [-1,  2, -3, -4, -5, -6, -7, -8, -9], :cost 286}
              {:model [ 1, -2, -3, -4, -5, -6, -7, -8, -9], :cost 286}
              {:model [-1,  2, -3, -4, -5,  6, -7, -8, -9], :cost 322}
              {:model [-1,  2, -3, -4, -5, -6,  7, -8, -9], :cost 322}
              {:model [ 1,  2, -3, -4, -5,  6, -7, -8, -9], :cost 330}
              {:model [ 1, -2, -3,  4, -5,  6, -7, -8, -9], :cost 330}
              {:model [ 1, -2, -3, -4, -5,  6,  7, -8, -9], :cost 358}
              {:model [-1,  2, -3, -4, -5,  6,  7, -8, -9], :cost 358}
              {:model [ 1,  2, -3, -4, -5,  6,  7, -8, -9], :cost 366}]
             (maxsat/run-rc2-problem (wcnf/WCNF nil :from_string another-maxsat) 10))))))

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
         (maxsat/run-rc2-problem (wcnf/WCNF nil :from_string tseitin-2) 10))))

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
         (maxsat/run-rc2-problem (wcnf/WCNF nil :from_string tseitin-4) 10))))

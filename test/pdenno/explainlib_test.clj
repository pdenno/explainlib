(ns pdenno.explainlib-test
  (:require
   [clojure.test           :refer [deftest is testing]]
   [libpython-clj2.require :refer [require-python]]
   [libpython-clj2.python :as py :refer [py. py.. py.-]]
   [pdenno.explainlib :as explain]))

(require-python '[pysat.examples.rc2 :as rc2])
(require-python '[pysat.formula :as wcnf])

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








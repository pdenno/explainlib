# explainlib - A Clojure library for Bayesian Abductive Logic Programming (BALP) and identification of most probable explanation (MPE)

This library answers queries against Bayesian networks by
  (1) producing proof trees for all navigations of the network that support the query, and
  (2) assessing the probability of each navigation in a most probable explanation (MPE) calculation using probabilities in the Bayesian
	  network and observations.

For the most part, the calculations to make this happen are straightforward.
Things only get interesting when it is applied to problems where both probabilistic and satisfaction constraints are being expressed.
In that case some facts can be 'protected'. Unfortunately, this isn't completely implemented yet.

The library uses well-known techniques.
The algorithm for producing the proofs is similar to that described by Raghavan et al.[^1].
The algorithm for solving MPE problems is similar to that described by Park[^2] and uses the RC2 MaxSAT solver, Ignatiev et al.[^3].
Owing to the computational challenge of some of MPE problems, typically not all proofs are assessed together.
Specifically, the algorithm uses a tournament where a random selection of proofs compete and the ones with the best MPE score
from each such game advance to the next round of the tournament.


[![Clojars Project](https://img.shields.io/clojars/v/com.github.pdenno/explainlib.svg)](https://clojars.org/com.github.pdenno/explainlib)

# Installation

The library is written in Clojure and uses a Python-based interface to the RC2 MaxSAT solver.
Owing to that, in order to use the library it is necessary to install Python and the RC2 solver as well as Clojure.
(A Dockerized implementation is a "to do".)

# Usage

The file [tests](https://github.com/pdenno/explainlib/blob/main/test/pdenno/explainlib_test.clj) describes some
ordinary usage scenarios as well as some tests that illustrate intermediate forms generated in the process.


## Disclaimer

This software was developed by [NIST](http://nist/gov). [This disclaimer](https://www.nist.gov/el/software-disclaimer) applies.

## References

[^1]: S. Raghavan, P. Singla, R. J. Mooney, "Plan Recognition Using Statistical Relational Models",
  in Plan, Activity, and Intent Recognition, Morgan Kaufmann, 2014.

[^2]: J. Park, "Using Wighted MAX-SAT Engines to Solve MPE",
Proceedings of the National Conference on Artificial Intelligence, 2002.

[^3]: A. Ignatiev, A. Morgado, J. Marques-Siilva, "RC2: an Efficient MaxSAT Solver",
Journal of Satisfiability, Boolean Modeling and Computation, 2019.

# Contact Us

<a target="_blank" href="mailto:peter.denno@nist.gov">Peter Denno (peter.denno ( at ) nist.gov</a>

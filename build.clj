(ns build
  "This file by POD for a local build."
  (:require [clojure.tools.build.api :as b]
            [org.corfield.build :as bb]))

;;; https://github.com/seancorfield/build-clj
(def lib 'pdenno/explainlib)
;; if you want a version of MAJOR.MINOR.COMMITS:
;;; POD git rev-list --count HEAD
(def version (format "0.1.%s" (b/git-count-revs nil)))

;;; (build-jar {:lib lib :version version})
(defn build-jar "Run the CI pipeline of tests (and build the JAR)." [opts]
  (-> opts
      (assoc :lib lib :version version)
      ;(bb/run-tests)
      (bb/clean)
      (bb/jar)))

;;; (install-jar {})
(defn install "Install the JAR locally." [opts]
  (-> opts
      (assoc :lib lib :version version)
      (bb/install)))

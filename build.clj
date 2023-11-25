(ns build
  (:require
   [clojure.tools.build.api :as b]))

;;; I'm not sure this will even work, given the python dependencies.
;;; See also https://clojure.org/guides/tools_build
;;; To install jar: clj -T:build all

(def lib 'com.github.pdenno/explainlib)
(def version (format "1.0.%s" (b/git-count-revs nil)))
(def class-dir "target/classes")
(def basis (b/create-basis {:project "deps.edn"}))
(def jar-file (format "target/%s-%s.jar" (name lib) version))
(def target-dir "target")

(defn clean [_]
  (println "Doing the clean")
  (b/delete {:path "target"}))

(defn prep [_]
  (println "Writing the pom.")
  (b/write-pom {:class-dir class-dir
                :lib lib
                :version version
                :basis basis
                :src-dirs ["src"]})
  (b/copy-dir {:src-dirs ["src"] :target-dir class-dir}))

(defn jar [_]
  (println "Building the jar.")
  (b/jar {:class-dir class-dir :jar-file jar-file}))


;;; :basis - required, used for :mvn/local-repo
(defn install [_]
  (println "Installing: class-dir =" class-dir "version = " version)
  (let [opts {:lib lib :basis basis :jar-file jar-file :class-dir class-dir :version version}]
    (b/install opts)))

(defn all [_]
  (-> nil clean prep jar install))

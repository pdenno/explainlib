(ns pdenno.-configure
  (:require
   ;[cprop.core :refer [load-config]]
   [cprop.source :as source]
   [libpython-clj2.python :as py]))

;;; ToDo:
;;;    - See comments

(defonce env  (source/from-env))
(def python-home (:pythonhome env))

;;; local install - POD Needs work. 
#_(py/initialize! :python-executable (str python-home "/bin/python3.9")
		  :library-path      (str python-home "/Library/Frameworks/Python.framework/Versions/3.9/lib/libpython3.9.dylib"))

